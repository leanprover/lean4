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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Doc_joinInlines(lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(lean_object*);
lean_object* l_Lean_Doc_joinBlocks(lean_object*);
lean_object* l_Lean_Doc_prefixListLines(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Doc_prefixLines(lean_object*, lean_object*);
lean_object* l_Lean_Doc_MarkdownM_run_x27(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
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
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_partMarkdown___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_instMarkdownInlineElabInline___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instMarkdownInlineElabInline___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__19_value)} };
static const lean_object* l_Lean_instMarkdownInlineElabInline___closed__20 = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__20_value;
LEAN_EXPORT const lean_object* l_Lean_instMarkdownInlineElabInline = (const lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__20_value;
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprElabBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprElabBlock___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprElabBlock___closed__0 = (const lean_object*)&l_Lean_instReprElabBlock___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprElabBlock = (const lean_object*)&l_Lean_instReprElabBlock___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__19_value)} };
static const lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0 = (const lean_object*)&l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock = (const lean_object*)&l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__0_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__1_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__2 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__2_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "**"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__3 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__3_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__3_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__4 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__4_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__5 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "$$"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__6 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__6_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lean_findInternalDocString_x3f___closed__0_value),((lean_object*)&l_Lean_findInternalDocString_x3f___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]("};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__10 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__10_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__11 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__11_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__8 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__8_value;
static const lean_array_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__8_value)}};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__9 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__9_value;
static lean_once_cell_t l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__12;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__13 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__13_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[^"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__14 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__14_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__15 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__15_value;
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__16 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "* "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(size_t, size_t, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ". "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9___closed__1_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9___closed__1_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9(size_t, size_t, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "> "};
static const lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1 = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__15_value)}};
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
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__11_value)}};
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
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instToMarkdownSnippet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToMarkdownSnippet___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__20_value),((lean_object*)&l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0_value)} };
static const lean_object* l_Lean_instToMarkdownSnippet___closed__0 = (const lean_object*)&l_Lean_instToMarkdownSnippet___closed__0_value;
static const lean_closure_object l_Lean_instToMarkdownSnippet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToMarkdownSnippet___lam__1, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__20_value),((lean_object*)&l_Lean_instMarkdownBlockElabInlineElabBlock___closed__0_value),((lean_object*)&l_Lean_instMarkdownInlineElabInline___closed__19_value),((lean_object*)&l_Lean_instToMarkdownSnippet___closed__0_value)} };
static const lean_object* l_Lean_instToMarkdownSnippet___closed__1 = (const lean_object*)&l_Lean_instToMarkdownSnippet___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instToMarkdownSnippet = (const lean_object*)&l_Lean_instToMarkdownSnippet___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__0(lean_object* v___x_57_, lean_object* v_go_58_, lean_object* v___i_59_, lean_object* v_content_60_, lean_object* v___y_61_){
_start:
{
size_t v_sz_62_; size_t v___x_63_; lean_object* v___x_334__overap_64_; lean_object* v___x_65_; lean_object* v_fst_66_; lean_object* v_snd_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_75_; 
v_sz_62_ = lean_array_size(v_content_60_);
v___x_63_ = ((size_t)0ULL);
v___x_334__overap_64_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_57_, v_go_58_, v_sz_62_, v___x_63_, v_content_60_);
v___x_65_ = lean_apply_1(v___x_334__overap_64_, v___y_61_);
v_fst_66_ = lean_ctor_get(v___x_65_, 0);
v_snd_67_ = lean_ctor_get(v___x_65_, 1);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_75_ == 0)
{
v___x_69_ = v___x_65_;
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_snd_67_);
lean_inc(v_fst_66_);
lean_dec(v___x_65_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_71_ = l_Lean_Doc_joinInlines(v_fst_66_);
lean_dec(v_fst_66_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_71_);
v___x_73_ = v___x_69_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_snd_67_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownInlineElabInline___lam__0___boxed(lean_object* v___x_76_, lean_object* v_go_77_, lean_object* v___i_78_, lean_object* v_content_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_instMarkdownInlineElabInline___lam__0(v___x_76_, v_go_77_, v___i_78_, v_content_79_, v___y_80_);
lean_dec_ref(v___i_78_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0(lean_object* v_v_130_, lean_object* v_x_131_){
_start:
{
lean_object* v_name_132_; lean_object* v_val_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_159_; 
v_name_132_ = lean_ctor_get(v_v_130_, 0);
v_val_133_ = lean_ctor_get(v_v_130_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_v_130_);
if (v_isSharedCheck_159_ == 0)
{
v___x_135_ = v_v_130_;
v_isShared_136_ = v_isSharedCheck_159_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_val_133_);
lean_inc(v_name_132_);
lean_dec(v_v_130_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_159_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_137_ = lean_box(1);
v___x_138_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = l_Lean_Name_reprPrec(v_name_132_, v___x_139_);
if (v_isShared_136_ == 0)
{
lean_ctor_set_tag(v___x_135_, 5);
lean_ctor_set(v___x_135_, 1, v___x_140_);
lean_ctor_set(v___x_135_, 0, v___x_138_);
v___x_142_ = v___x_135_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_140_);
v___x_142_ = v_reuseFailAlloc_158_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_143_; uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_143_ = l_Std_Format_nestD(v___x_142_);
v___x_144_ = 0;
v___x_145_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_145_, 0, v___x_143_);
lean_ctor_set_uint8(v___x_145_, sizeof(void*)*1, v___x_144_);
v___x_146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v___x_137_);
v___x_147_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_148_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_133_);
lean_dec(v_val_133_);
v___x_149_ = l_Lean_Name_reprPrec(v___x_148_, v___x_139_);
v___x_150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_147_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = l_Std_Format_nestD(v___x_152_);
v___x_154_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*1, v___x_144_);
v___x_155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_146_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = l_Std_Format_nestD(v___x_155_);
v___x_157_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set_uint8(v___x_157_, sizeof(void*)*1, v___x_144_);
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0___boxed(lean_object* v_v_160_, lean_object* v_x_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_instReprElabBlock___lam__0(v_v_160_, v_x_161_);
lean_dec(v_x_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0(lean_object* v___x_165_, lean_object* v___goI_166_, lean_object* v_goB_167_, lean_object* v___b_168_, lean_object* v_content_169_, lean_object* v___y_170_){
_start:
{
size_t v_sz_171_; size_t v___x_172_; lean_object* v___x_334__overap_173_; lean_object* v___x_174_; lean_object* v_fst_175_; lean_object* v_snd_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_184_; 
v_sz_171_ = lean_array_size(v_content_169_);
v___x_172_ = ((size_t)0ULL);
v___x_334__overap_173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_165_, v_goB_167_, v_sz_171_, v___x_172_, v_content_169_);
v___x_174_ = lean_apply_1(v___x_334__overap_173_, v___y_170_);
v_fst_175_ = lean_ctor_get(v___x_174_, 0);
v_snd_176_ = lean_ctor_get(v___x_174_, 1);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_184_ == 0)
{
v___x_178_ = v___x_174_;
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_snd_176_);
lean_inc(v_fst_175_);
lean_dec(v___x_174_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_180_ = l_Lean_Doc_joinBlocks(v_fst_175_);
lean_dec(v_fst_175_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_180_);
v___x_182_ = v___x_178_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_snd_176_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0___boxed(lean_object* v___x_185_, lean_object* v___goI_186_, lean_object* v_goB_187_, lean_object* v___b_188_, lean_object* v_content_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_instMarkdownBlockElabInlineElabBlock___lam__0(v___x_185_, v___goI_186_, v_goB_187_, v___b_188_, v_content_189_, v___y_190_);
lean_dec_ref(v___b_188_);
lean_dec_ref(v___goI_186_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(lean_object* v_name_201_, lean_object* v_decl_202_, lean_object* v_ref_203_){
_start:
{
lean_object* v_defValue_205_; lean_object* v_descr_206_; lean_object* v_deprecation_x3f_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_defValue_205_ = lean_ctor_get(v_decl_202_, 0);
v_descr_206_ = lean_ctor_get(v_decl_202_, 1);
v_deprecation_x3f_207_ = lean_ctor_get(v_decl_202_, 2);
v___x_208_ = lean_alloc_ctor(1, 0, 1);
v___x_209_ = lean_unbox(v_defValue_205_);
lean_ctor_set_uint8(v___x_208_, 0, v___x_209_);
lean_inc(v_deprecation_x3f_207_);
lean_inc_ref(v_descr_206_);
lean_inc_n(v_name_201_, 2);
v___x_210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_210_, 0, v_name_201_);
lean_ctor_set(v___x_210_, 1, v_ref_203_);
lean_ctor_set(v___x_210_, 2, v___x_208_);
lean_ctor_set(v___x_210_, 3, v_descr_206_);
lean_ctor_set(v___x_210_, 4, v_deprecation_x3f_207_);
v___x_211_ = lean_register_option(v_name_201_, v___x_210_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_219_; 
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; 
v_unused_220_ = lean_ctor_get(v___x_211_, 0);
lean_dec(v_unused_220_);
v___x_213_ = v___x_211_;
v_isShared_214_ = v_isSharedCheck_219_;
goto v_resetjp_212_;
}
else
{
lean_dec(v___x_211_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_219_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___x_217_; 
lean_inc(v_defValue_205_);
v___x_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_215_, 0, v_name_201_);
lean_ctor_set(v___x_215_, 1, v_defValue_205_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_215_);
v___x_217_ = v___x_213_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
lean_dec(v_name_201_);
v_a_221_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_211_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_211_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_229_, lean_object* v_decl_230_, lean_object* v_ref_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v_name_229_, v_decl_230_, v_ref_231_);
lean_dec_ref(v_decl_230_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_251_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_252_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_253_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_254_ = l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v___x_251_, v___x_252_, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4____boxed(lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_();
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_274_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_275_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_276_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_277_ = l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v___x_274_, v___x_275_, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4____boxed(lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_();
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_box(1);
v___x_282_ = lean_st_mk_ref(v___x_281_);
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2____boxed(lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_();
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_286_, lean_object* v_x_287_){
_start:
{
if (lean_obj_tag(v_x_287_) == 0)
{
lean_object* v_k_288_; lean_object* v_v_289_; lean_object* v_l_290_; lean_object* v_r_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_k_288_ = lean_ctor_get(v_x_287_, 1);
v_v_289_ = lean_ctor_get(v_x_287_, 2);
v_l_290_ = lean_ctor_get(v_x_287_, 3);
v_r_291_ = lean_ctor_get(v_x_287_, 4);
v___x_292_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_286_, v_l_290_);
lean_inc(v_v_289_);
lean_inc(v_k_288_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_k_288_);
lean_ctor_set(v___x_293_, 1, v_v_289_);
v___x_294_ = lean_array_push(v___x_292_, v___x_293_);
v_init_286_ = v___x_294_;
v_x_287_ = v_r_291_;
goto _start;
}
else
{
return v_init_286_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_296_, lean_object* v_x_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_296_, v_x_297_);
lean_dec(v_x_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(lean_object* v_x_303_, lean_object* v_s_304_){
_start:
{
lean_object* v___x_305_; lean_object* v_ents_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_305_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v_ents_306_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v___x_305_, v_s_304_);
v___x_307_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
lean_inc_ref(v_ents_306_);
v___x_308_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v_ents_306_);
lean_ctor_set(v___x_308_, 2, v_ents_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object* v_x_309_, lean_object* v_s_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(v_x_309_, v_s_310_);
lean_dec(v_s_310_);
lean_dec_ref(v_x_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___f_320_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_321_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_322_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_323_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_321_, v___x_322_, v___f_320_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_();
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0(lean_object* v_init_326_, lean_object* v_t_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_326_, v_t_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_329_, lean_object* v_t_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0(v_init_329_, v_t_330_);
lean_dec(v_t_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_332_, lean_object* v_x_333_){
_start:
{
if (lean_obj_tag(v_x_333_) == 0)
{
lean_object* v_k_334_; lean_object* v_v_335_; lean_object* v_l_336_; lean_object* v_r_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_k_334_ = lean_ctor_get(v_x_333_, 1);
v_v_335_ = lean_ctor_get(v_x_333_, 2);
v_l_336_ = lean_ctor_get(v_x_333_, 3);
v_r_337_ = lean_ctor_get(v_x_333_, 4);
v___x_338_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_332_, v_l_336_);
lean_inc(v_v_335_);
lean_inc(v_k_334_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v_k_334_);
lean_ctor_set(v___x_339_, 1, v_v_335_);
v___x_340_ = lean_array_push(v___x_338_, v___x_339_);
v_init_332_ = v___x_340_;
v_x_333_ = v_r_337_;
goto _start;
}
else
{
return v_init_332_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_342_, lean_object* v_x_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_342_, v_x_343_);
lean_dec(v_x_343_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(lean_object* v_x_349_, lean_object* v_s_350_){
_start:
{
lean_object* v___x_351_; lean_object* v_ents_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_351_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v_ents_352_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v___x_351_, v_s_350_);
v___x_353_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
lean_inc_ref(v_ents_352_);
v___x_354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v_ents_352_);
lean_ctor_set(v___x_354_, 2, v_ents_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed(lean_object* v_x_355_, lean_object* v_s_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(v_x_355_, v_s_356_);
lean_dec(v_s_356_);
lean_dec_ref(v_x_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___f_387_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_388_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_389_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_390_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_388_, v___x_389_, v___f_387_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed(lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_();
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0(lean_object* v_init_393_, lean_object* v_t_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_393_, v_t_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_396_, lean_object* v_t_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0(v_init_396_, v_t_397_);
lean_dec(v_t_397_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_400_ = lean_box(1);
v___x_401_ = lean_st_mk_ref(v___x_400_);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2____boxed(lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_405_, lean_object* v_x_406_){
_start:
{
if (lean_obj_tag(v_x_406_) == 0)
{
lean_object* v_k_407_; lean_object* v_v_408_; lean_object* v_l_409_; lean_object* v_r_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_k_407_ = lean_ctor_get(v_x_406_, 1);
v_v_408_ = lean_ctor_get(v_x_406_, 2);
v_l_409_ = lean_ctor_get(v_x_406_, 3);
v_r_410_ = lean_ctor_get(v_x_406_, 4);
v___x_411_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_405_, v_l_409_);
lean_inc(v_v_408_);
lean_inc(v_k_407_);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v_k_407_);
lean_ctor_set(v___x_412_, 1, v_v_408_);
v___x_413_ = lean_array_push(v___x_411_, v___x_412_);
v_init_405_ = v___x_413_;
v_x_406_ = v_r_410_;
goto _start;
}
else
{
return v_init_405_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_415_, lean_object* v_x_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_415_, v_x_416_);
lean_dec(v_x_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(lean_object* v_x_422_, lean_object* v_s_423_){
_start:
{
lean_object* v___x_424_; lean_object* v_ents_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_424_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v_ents_425_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v___x_424_, v_s_423_);
v___x_426_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
lean_inc_ref(v_ents_425_);
v___x_427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v_ents_425_);
lean_ctor_set(v___x_427_, 2, v_ents_425_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object* v_x_428_, lean_object* v_s_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(v_x_428_, v_s_429_);
lean_dec(v_s_429_);
lean_dec_ref(v_x_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___f_437_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v___x_438_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v___x_439_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_440_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_438_, v___x_439_, v___f_437_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_();
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0(lean_object* v_init_443_, lean_object* v_t_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_443_, v_t_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_446_, lean_object* v_t_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0(v_init_446_, v_t_447_);
lean_dec(v_t_447_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString(lean_object* v_declName_449_, lean_object* v_docString_450_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_452_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_453_ = lean_st_ref_take(v___x_452_);
v___x_454_ = l_String_removeLeadingSpaces(v_docString_450_);
v___x_455_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_449_, v___x_454_, v___x_453_);
v___x_456_ = lean_st_ref_set(v___x_452_, v___x_455_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString___boxed(lean_object* v_declName_458_, lean_object* v_docString_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_addBuiltinDocString(v_declName_458_, v_docString_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(lean_object* v_k_462_, lean_object* v_t_463_){
_start:
{
if (lean_obj_tag(v_t_463_) == 0)
{
lean_object* v_k_464_; lean_object* v_v_465_; lean_object* v_l_466_; lean_object* v_r_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_1121_; 
v_k_464_ = lean_ctor_get(v_t_463_, 1);
v_v_465_ = lean_ctor_get(v_t_463_, 2);
v_l_466_ = lean_ctor_get(v_t_463_, 3);
v_r_467_ = lean_ctor_get(v_t_463_, 4);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_t_463_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; 
v_unused_1122_ = lean_ctor_get(v_t_463_, 0);
lean_dec(v_unused_1122_);
v___x_469_ = v_t_463_;
v_isShared_470_ = v_isSharedCheck_1121_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_r_467_);
lean_inc(v_l_466_);
lean_inc(v_v_465_);
lean_inc(v_k_464_);
lean_dec(v_t_463_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_1121_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
uint8_t v___x_471_; 
v___x_471_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_462_, v_k_464_);
switch(v___x_471_)
{
case 0:
{
lean_object* v_impl_472_; lean_object* v___x_473_; 
v_impl_472_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_462_, v_l_466_);
v___x_473_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_472_) == 0)
{
if (lean_obj_tag(v_r_467_) == 0)
{
lean_object* v_size_474_; lean_object* v_size_475_; lean_object* v_k_476_; lean_object* v_v_477_; lean_object* v_l_478_; lean_object* v_r_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_size_474_ = lean_ctor_get(v_impl_472_, 0);
lean_inc(v_size_474_);
v_size_475_ = lean_ctor_get(v_r_467_, 0);
v_k_476_ = lean_ctor_get(v_r_467_, 1);
v_v_477_ = lean_ctor_get(v_r_467_, 2);
v_l_478_ = lean_ctor_get(v_r_467_, 3);
lean_inc(v_l_478_);
v_r_479_ = lean_ctor_get(v_r_467_, 4);
v___x_480_ = lean_unsigned_to_nat(3u);
v___x_481_ = lean_nat_mul(v___x_480_, v_size_474_);
v___x_482_ = lean_nat_dec_lt(v___x_481_, v_size_475_);
lean_dec(v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
lean_dec(v_l_478_);
v___x_483_ = lean_nat_add(v___x_473_, v_size_474_);
lean_dec(v_size_474_);
v___x_484_ = lean_nat_add(v___x_483_, v_size_475_);
lean_dec(v___x_483_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 3, v_impl_472_);
lean_ctor_set(v___x_469_, 0, v___x_484_);
v___x_486_ = v___x_469_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_487_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_487_, 3, v_impl_472_);
lean_ctor_set(v_reuseFailAlloc_487_, 4, v_r_467_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
else
{
lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_551_; 
lean_inc(v_r_479_);
lean_inc(v_v_477_);
lean_inc(v_k_476_);
lean_inc(v_size_475_);
v_isSharedCheck_551_ = !lean_is_exclusive(v_r_467_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; lean_object* v_unused_553_; lean_object* v_unused_554_; lean_object* v_unused_555_; lean_object* v_unused_556_; 
v_unused_552_ = lean_ctor_get(v_r_467_, 4);
lean_dec(v_unused_552_);
v_unused_553_ = lean_ctor_get(v_r_467_, 3);
lean_dec(v_unused_553_);
v_unused_554_ = lean_ctor_get(v_r_467_, 2);
lean_dec(v_unused_554_);
v_unused_555_ = lean_ctor_get(v_r_467_, 1);
lean_dec(v_unused_555_);
v_unused_556_ = lean_ctor_get(v_r_467_, 0);
lean_dec(v_unused_556_);
v___x_489_ = v_r_467_;
v_isShared_490_ = v_isSharedCheck_551_;
goto v_resetjp_488_;
}
else
{
lean_dec(v_r_467_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_551_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v_size_491_; lean_object* v_k_492_; lean_object* v_v_493_; lean_object* v_l_494_; lean_object* v_r_495_; lean_object* v_size_496_; lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_size_491_ = lean_ctor_get(v_l_478_, 0);
v_k_492_ = lean_ctor_get(v_l_478_, 1);
v_v_493_ = lean_ctor_get(v_l_478_, 2);
v_l_494_ = lean_ctor_get(v_l_478_, 3);
v_r_495_ = lean_ctor_get(v_l_478_, 4);
v_size_496_ = lean_ctor_get(v_r_479_, 0);
v___x_497_ = lean_unsigned_to_nat(2u);
v___x_498_ = lean_nat_mul(v___x_497_, v_size_496_);
v___x_499_ = lean_nat_dec_lt(v_size_491_, v___x_498_);
lean_dec(v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_527_; 
lean_inc(v_r_495_);
lean_inc(v_l_494_);
lean_inc(v_v_493_);
lean_inc(v_k_492_);
v_isSharedCheck_527_ = !lean_is_exclusive(v_l_478_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; lean_object* v_unused_529_; lean_object* v_unused_530_; lean_object* v_unused_531_; lean_object* v_unused_532_; 
v_unused_528_ = lean_ctor_get(v_l_478_, 4);
lean_dec(v_unused_528_);
v_unused_529_ = lean_ctor_get(v_l_478_, 3);
lean_dec(v_unused_529_);
v_unused_530_ = lean_ctor_get(v_l_478_, 2);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_l_478_, 1);
lean_dec(v_unused_531_);
v_unused_532_ = lean_ctor_get(v_l_478_, 0);
lean_dec(v_unused_532_);
v___x_501_ = v_l_478_;
v_isShared_502_ = v_isSharedCheck_527_;
goto v_resetjp_500_;
}
else
{
lean_dec(v_l_478_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_527_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_517_; 
v___x_503_ = lean_nat_add(v___x_473_, v_size_474_);
lean_dec(v_size_474_);
v___x_504_ = lean_nat_add(v___x_503_, v_size_475_);
lean_dec(v_size_475_);
if (lean_obj_tag(v_l_494_) == 0)
{
lean_object* v_size_525_; 
v_size_525_ = lean_ctor_get(v_l_494_, 0);
lean_inc(v_size_525_);
v___y_517_ = v_size_525_;
goto v___jp_516_;
}
else
{
lean_object* v___x_526_; 
v___x_526_ = lean_unsigned_to_nat(0u);
v___y_517_ = v___x_526_;
goto v___jp_516_;
}
v___jp_505_:
{
lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_509_ = lean_nat_add(v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec(v___y_507_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 4, v_r_479_);
lean_ctor_set(v___x_501_, 3, v_r_495_);
lean_ctor_set(v___x_501_, 2, v_v_477_);
lean_ctor_set(v___x_501_, 1, v_k_476_);
lean_ctor_set(v___x_501_, 0, v___x_509_);
v___x_511_ = v___x_501_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_k_476_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v_v_477_);
lean_ctor_set(v_reuseFailAlloc_515_, 3, v_r_495_);
lean_ctor_set(v_reuseFailAlloc_515_, 4, v_r_479_);
v___x_511_ = v_reuseFailAlloc_515_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_513_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 4, v___x_511_);
lean_ctor_set(v___x_489_, 3, v___y_506_);
lean_ctor_set(v___x_489_, 2, v_v_493_);
lean_ctor_set(v___x_489_, 1, v_k_492_);
lean_ctor_set(v___x_489_, 0, v___x_504_);
v___x_513_ = v___x_489_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_k_492_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_v_493_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v___y_506_);
lean_ctor_set(v_reuseFailAlloc_514_, 4, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
v___jp_516_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = lean_nat_add(v___x_503_, v___y_517_);
lean_dec(v___y_517_);
lean_dec(v___x_503_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v_l_494_);
lean_ctor_set(v___x_469_, 3, v_impl_472_);
lean_ctor_set(v___x_469_, 0, v___x_518_);
v___x_520_ = v___x_469_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_524_, 3, v_impl_472_);
lean_ctor_set(v_reuseFailAlloc_524_, 4, v_l_494_);
v___x_520_ = v_reuseFailAlloc_524_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_521_; 
v___x_521_ = lean_nat_add(v___x_473_, v_size_496_);
if (lean_obj_tag(v_r_495_) == 0)
{
lean_object* v_size_522_; 
v_size_522_ = lean_ctor_get(v_r_495_, 0);
lean_inc(v_size_522_);
v___y_506_ = v___x_520_;
v___y_507_ = v___x_521_;
v___y_508_ = v_size_522_;
goto v___jp_505_;
}
else
{
lean_object* v___x_523_; 
v___x_523_ = lean_unsigned_to_nat(0u);
v___y_506_ = v___x_520_;
v___y_507_ = v___x_521_;
v___y_508_ = v___x_523_;
goto v___jp_505_;
}
}
}
}
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
lean_del_object(v___x_469_);
v___x_533_ = lean_nat_add(v___x_473_, v_size_474_);
lean_dec(v_size_474_);
v___x_534_ = lean_nat_add(v___x_533_, v_size_475_);
lean_dec(v_size_475_);
v___x_535_ = lean_nat_add(v___x_533_, v_size_491_);
lean_dec(v___x_533_);
lean_inc_ref(v_impl_472_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 4, v_l_478_);
lean_ctor_set(v___x_489_, 3, v_impl_472_);
lean_ctor_set(v___x_489_, 2, v_v_465_);
lean_ctor_set(v___x_489_, 1, v_k_464_);
lean_ctor_set(v___x_489_, 0, v___x_535_);
v___x_537_ = v___x_489_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v_impl_472_);
lean_ctor_set(v_reuseFailAlloc_550_, 4, v_l_478_);
v___x_537_ = v_reuseFailAlloc_550_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
v_isSharedCheck_544_ = !lean_is_exclusive(v_impl_472_);
if (v_isSharedCheck_544_ == 0)
{
lean_object* v_unused_545_; lean_object* v_unused_546_; lean_object* v_unused_547_; lean_object* v_unused_548_; lean_object* v_unused_549_; 
v_unused_545_ = lean_ctor_get(v_impl_472_, 4);
lean_dec(v_unused_545_);
v_unused_546_ = lean_ctor_get(v_impl_472_, 3);
lean_dec(v_unused_546_);
v_unused_547_ = lean_ctor_get(v_impl_472_, 2);
lean_dec(v_unused_547_);
v_unused_548_ = lean_ctor_get(v_impl_472_, 1);
lean_dec(v_unused_548_);
v_unused_549_ = lean_ctor_get(v_impl_472_, 0);
lean_dec(v_unused_549_);
v___x_539_ = v_impl_472_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_dec(v_impl_472_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 4, v_r_479_);
lean_ctor_set(v___x_539_, 3, v___x_537_);
lean_ctor_set(v___x_539_, 2, v_v_477_);
lean_ctor_set(v___x_539_, 1, v_k_476_);
lean_ctor_set(v___x_539_, 0, v___x_534_);
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_k_476_);
lean_ctor_set(v_reuseFailAlloc_543_, 2, v_v_477_);
lean_ctor_set(v_reuseFailAlloc_543_, 3, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_543_, 4, v_r_479_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v_size_557_ = lean_ctor_get(v_impl_472_, 0);
lean_inc(v_size_557_);
v___x_558_ = lean_nat_add(v___x_473_, v_size_557_);
lean_dec(v_size_557_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 3, v_impl_472_);
lean_ctor_set(v___x_469_, 0, v___x_558_);
v___x_560_ = v___x_469_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_impl_472_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v_r_467_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
else
{
if (lean_obj_tag(v_r_467_) == 0)
{
lean_object* v_l_562_; 
v_l_562_ = lean_ctor_get(v_r_467_, 3);
lean_inc(v_l_562_);
if (lean_obj_tag(v_l_562_) == 0)
{
lean_object* v_r_563_; 
v_r_563_ = lean_ctor_get(v_r_467_, 4);
lean_inc(v_r_563_);
if (lean_obj_tag(v_r_563_) == 0)
{
lean_object* v_size_564_; lean_object* v_k_565_; lean_object* v_v_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_579_; 
v_size_564_ = lean_ctor_get(v_r_467_, 0);
v_k_565_ = lean_ctor_get(v_r_467_, 1);
v_v_566_ = lean_ctor_get(v_r_467_, 2);
v_isSharedCheck_579_ = !lean_is_exclusive(v_r_467_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; lean_object* v_unused_581_; 
v_unused_580_ = lean_ctor_get(v_r_467_, 4);
lean_dec(v_unused_580_);
v_unused_581_ = lean_ctor_get(v_r_467_, 3);
lean_dec(v_unused_581_);
v___x_568_ = v_r_467_;
v_isShared_569_ = v_isSharedCheck_579_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_v_566_);
lean_inc(v_k_565_);
lean_inc(v_size_564_);
lean_dec(v_r_467_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_579_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v_size_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v_size_570_ = lean_ctor_get(v_l_562_, 0);
v___x_571_ = lean_nat_add(v___x_473_, v_size_564_);
lean_dec(v_size_564_);
v___x_572_ = lean_nat_add(v___x_473_, v_size_570_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 4, v_l_562_);
lean_ctor_set(v___x_568_, 3, v_impl_472_);
lean_ctor_set(v___x_568_, 2, v_v_465_);
lean_ctor_set(v___x_568_, 1, v_k_464_);
lean_ctor_set(v___x_568_, 0, v___x_572_);
v___x_574_ = v___x_568_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_578_, 3, v_impl_472_);
lean_ctor_set(v_reuseFailAlloc_578_, 4, v_l_562_);
v___x_574_ = v_reuseFailAlloc_578_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v_r_563_);
lean_ctor_set(v___x_469_, 3, v___x_574_);
lean_ctor_set(v___x_469_, 2, v_v_566_);
lean_ctor_set(v___x_469_, 1, v_k_565_);
lean_ctor_set(v___x_469_, 0, v___x_571_);
v___x_576_ = v___x_469_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_k_565_);
lean_ctor_set(v_reuseFailAlloc_577_, 2, v_v_566_);
lean_ctor_set(v_reuseFailAlloc_577_, 3, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_577_, 4, v_r_563_);
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
else
{
lean_object* v_k_582_; lean_object* v_v_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_606_; 
v_k_582_ = lean_ctor_get(v_r_467_, 1);
v_v_583_ = lean_ctor_get(v_r_467_, 2);
v_isSharedCheck_606_ = !lean_is_exclusive(v_r_467_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; lean_object* v_unused_608_; lean_object* v_unused_609_; 
v_unused_607_ = lean_ctor_get(v_r_467_, 4);
lean_dec(v_unused_607_);
v_unused_608_ = lean_ctor_get(v_r_467_, 3);
lean_dec(v_unused_608_);
v_unused_609_ = lean_ctor_get(v_r_467_, 0);
lean_dec(v_unused_609_);
v___x_585_ = v_r_467_;
v_isShared_586_ = v_isSharedCheck_606_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_v_583_);
lean_inc(v_k_582_);
lean_dec(v_r_467_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_606_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v_k_587_; lean_object* v_v_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_602_; 
v_k_587_ = lean_ctor_get(v_l_562_, 1);
v_v_588_ = lean_ctor_get(v_l_562_, 2);
v_isSharedCheck_602_ = !lean_is_exclusive(v_l_562_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; lean_object* v_unused_604_; lean_object* v_unused_605_; 
v_unused_603_ = lean_ctor_get(v_l_562_, 4);
lean_dec(v_unused_603_);
v_unused_604_ = lean_ctor_get(v_l_562_, 3);
lean_dec(v_unused_604_);
v_unused_605_ = lean_ctor_get(v_l_562_, 0);
lean_dec(v_unused_605_);
v___x_590_ = v_l_562_;
v_isShared_591_ = v_isSharedCheck_602_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_v_588_);
lean_inc(v_k_587_);
lean_dec(v_l_562_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_602_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_592_ = lean_unsigned_to_nat(3u);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 4, v_r_563_);
lean_ctor_set(v___x_590_, 3, v_r_563_);
lean_ctor_set(v___x_590_, 2, v_v_465_);
lean_ctor_set(v___x_590_, 1, v_k_464_);
lean_ctor_set(v___x_590_, 0, v___x_473_);
v___x_594_ = v___x_590_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v_r_563_);
lean_ctor_set(v_reuseFailAlloc_601_, 4, v_r_563_);
v___x_594_ = v_reuseFailAlloc_601_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_596_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 3, v_r_563_);
lean_ctor_set(v___x_585_, 0, v___x_473_);
v___x_596_ = v___x_585_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_k_582_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v_v_583_);
lean_ctor_set(v_reuseFailAlloc_600_, 3, v_r_563_);
lean_ctor_set(v_reuseFailAlloc_600_, 4, v_r_563_);
v___x_596_ = v_reuseFailAlloc_600_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_598_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v___x_596_);
lean_ctor_set(v___x_469_, 3, v___x_594_);
lean_ctor_set(v___x_469_, 2, v_v_588_);
lean_ctor_set(v___x_469_, 1, v_k_587_);
lean_ctor_set(v___x_469_, 0, v___x_592_);
v___x_598_ = v___x_469_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_k_587_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v_v_588_);
lean_ctor_set(v_reuseFailAlloc_599_, 3, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_599_, 4, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_610_; 
v_r_610_ = lean_ctor_get(v_r_467_, 4);
lean_inc(v_r_610_);
if (lean_obj_tag(v_r_610_) == 0)
{
lean_object* v_k_611_; lean_object* v_v_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_623_; 
v_k_611_ = lean_ctor_get(v_r_467_, 1);
v_v_612_ = lean_ctor_get(v_r_467_, 2);
v_isSharedCheck_623_ = !lean_is_exclusive(v_r_467_);
if (v_isSharedCheck_623_ == 0)
{
lean_object* v_unused_624_; lean_object* v_unused_625_; lean_object* v_unused_626_; 
v_unused_624_ = lean_ctor_get(v_r_467_, 4);
lean_dec(v_unused_624_);
v_unused_625_ = lean_ctor_get(v_r_467_, 3);
lean_dec(v_unused_625_);
v_unused_626_ = lean_ctor_get(v_r_467_, 0);
lean_dec(v_unused_626_);
v___x_614_ = v_r_467_;
v_isShared_615_ = v_isSharedCheck_623_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_v_612_);
lean_inc(v_k_611_);
lean_dec(v_r_467_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_623_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_616_ = lean_unsigned_to_nat(3u);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 4, v_l_562_);
lean_ctor_set(v___x_614_, 2, v_v_465_);
lean_ctor_set(v___x_614_, 1, v_k_464_);
lean_ctor_set(v___x_614_, 0, v___x_473_);
v___x_618_ = v___x_614_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_622_, 3, v_l_562_);
lean_ctor_set(v_reuseFailAlloc_622_, 4, v_l_562_);
v___x_618_ = v_reuseFailAlloc_622_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_620_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v_r_610_);
lean_ctor_set(v___x_469_, 3, v___x_618_);
lean_ctor_set(v___x_469_, 2, v_v_612_);
lean_ctor_set(v___x_469_, 1, v_k_611_);
lean_ctor_set(v___x_469_, 0, v___x_616_);
v___x_620_ = v___x_469_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_k_611_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v_v_612_);
lean_ctor_set(v_reuseFailAlloc_621_, 3, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_621_, 4, v_r_610_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v_size_627_; lean_object* v_k_628_; lean_object* v_v_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_640_; 
v_size_627_ = lean_ctor_get(v_r_467_, 0);
v_k_628_ = lean_ctor_get(v_r_467_, 1);
v_v_629_ = lean_ctor_get(v_r_467_, 2);
v_isSharedCheck_640_ = !lean_is_exclusive(v_r_467_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; lean_object* v_unused_642_; 
v_unused_641_ = lean_ctor_get(v_r_467_, 4);
lean_dec(v_unused_641_);
v_unused_642_ = lean_ctor_get(v_r_467_, 3);
lean_dec(v_unused_642_);
v___x_631_ = v_r_467_;
v_isShared_632_ = v_isSharedCheck_640_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_v_629_);
lean_inc(v_k_628_);
lean_inc(v_size_627_);
lean_dec(v_r_467_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_640_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 3, v_r_610_);
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_size_627_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_k_628_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_v_629_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v_r_610_);
lean_ctor_set(v_reuseFailAlloc_639_, 4, v_r_610_);
v___x_634_ = v_reuseFailAlloc_639_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_635_ = lean_unsigned_to_nat(2u);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v___x_634_);
lean_ctor_set(v___x_469_, 3, v_r_610_);
lean_ctor_set(v___x_469_, 0, v___x_635_);
v___x_637_ = v___x_469_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v_r_610_);
lean_ctor_set(v_reuseFailAlloc_638_, 4, v___x_634_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
}
else
{
lean_object* v___x_644_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 3, v_r_467_);
lean_ctor_set(v___x_469_, 0, v___x_473_);
v___x_644_ = v___x_469_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_645_, 3, v_r_467_);
lean_ctor_set(v_reuseFailAlloc_645_, 4, v_r_467_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
case 1:
{
lean_del_object(v___x_469_);
lean_dec(v_v_465_);
lean_dec(v_k_464_);
if (lean_obj_tag(v_l_466_) == 0)
{
if (lean_obj_tag(v_r_467_) == 0)
{
lean_object* v_size_646_; lean_object* v_k_647_; lean_object* v_v_648_; lean_object* v_l_649_; lean_object* v_r_650_; lean_object* v_size_651_; lean_object* v_k_652_; lean_object* v_v_653_; lean_object* v_l_654_; lean_object* v_r_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_size_646_ = lean_ctor_get(v_l_466_, 0);
v_k_647_ = lean_ctor_get(v_l_466_, 1);
v_v_648_ = lean_ctor_get(v_l_466_, 2);
v_l_649_ = lean_ctor_get(v_l_466_, 3);
v_r_650_ = lean_ctor_get(v_l_466_, 4);
lean_inc(v_r_650_);
v_size_651_ = lean_ctor_get(v_r_467_, 0);
v_k_652_ = lean_ctor_get(v_r_467_, 1);
v_v_653_ = lean_ctor_get(v_r_467_, 2);
v_l_654_ = lean_ctor_get(v_r_467_, 3);
lean_inc(v_l_654_);
v_r_655_ = lean_ctor_get(v_r_467_, 4);
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_nat_dec_lt(v_size_646_, v_size_651_);
if (v___x_657_ == 0)
{
lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_793_; 
lean_inc(v_l_649_);
lean_inc(v_v_648_);
lean_inc(v_k_647_);
v_isSharedCheck_793_ = !lean_is_exclusive(v_l_466_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; lean_object* v_unused_795_; lean_object* v_unused_796_; lean_object* v_unused_797_; lean_object* v_unused_798_; 
v_unused_794_ = lean_ctor_get(v_l_466_, 4);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_l_466_, 3);
lean_dec(v_unused_795_);
v_unused_796_ = lean_ctor_get(v_l_466_, 2);
lean_dec(v_unused_796_);
v_unused_797_ = lean_ctor_get(v_l_466_, 1);
lean_dec(v_unused_797_);
v_unused_798_ = lean_ctor_get(v_l_466_, 0);
lean_dec(v_unused_798_);
v___x_659_ = v_l_466_;
v_isShared_660_ = v_isSharedCheck_793_;
goto v_resetjp_658_;
}
else
{
lean_dec(v_l_466_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_793_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v_tree_662_; 
v___x_661_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_647_, v_v_648_, v_l_649_, v_r_650_);
v_tree_662_ = lean_ctor_get(v___x_661_, 2);
lean_inc(v_tree_662_);
if (lean_obj_tag(v_tree_662_) == 0)
{
lean_object* v_k_663_; lean_object* v_v_664_; lean_object* v_size_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_k_663_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_k_663_);
v_v_664_ = lean_ctor_get(v___x_661_, 1);
lean_inc(v_v_664_);
lean_dec_ref(v___x_661_);
v_size_665_ = lean_ctor_get(v_tree_662_, 0);
v___x_666_ = lean_unsigned_to_nat(3u);
v___x_667_ = lean_nat_mul(v___x_666_, v_size_665_);
v___x_668_ = lean_nat_dec_lt(v___x_667_, v_size_651_);
lean_dec(v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
lean_dec(v_l_654_);
v___x_669_ = lean_nat_add(v___x_656_, v_size_665_);
v___x_670_ = lean_nat_add(v___x_669_, v_size_651_);
lean_dec(v___x_669_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 4, v_r_467_);
lean_ctor_set(v___x_659_, 3, v_tree_662_);
lean_ctor_set(v___x_659_, 2, v_v_664_);
lean_ctor_set(v___x_659_, 1, v_k_663_);
lean_ctor_set(v___x_659_, 0, v___x_670_);
v___x_672_ = v___x_659_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_k_663_);
lean_ctor_set(v_reuseFailAlloc_673_, 2, v_v_664_);
lean_ctor_set(v_reuseFailAlloc_673_, 3, v_tree_662_);
lean_ctor_set(v_reuseFailAlloc_673_, 4, v_r_467_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
else
{
lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_728_; 
lean_inc(v_r_655_);
lean_inc(v_v_653_);
lean_inc(v_k_652_);
lean_inc(v_size_651_);
v_isSharedCheck_728_ = !lean_is_exclusive(v_r_467_);
if (v_isSharedCheck_728_ == 0)
{
lean_object* v_unused_729_; lean_object* v_unused_730_; lean_object* v_unused_731_; lean_object* v_unused_732_; lean_object* v_unused_733_; 
v_unused_729_ = lean_ctor_get(v_r_467_, 4);
lean_dec(v_unused_729_);
v_unused_730_ = lean_ctor_get(v_r_467_, 3);
lean_dec(v_unused_730_);
v_unused_731_ = lean_ctor_get(v_r_467_, 2);
lean_dec(v_unused_731_);
v_unused_732_ = lean_ctor_get(v_r_467_, 1);
lean_dec(v_unused_732_);
v_unused_733_ = lean_ctor_get(v_r_467_, 0);
lean_dec(v_unused_733_);
v___x_675_ = v_r_467_;
v_isShared_676_ = v_isSharedCheck_728_;
goto v_resetjp_674_;
}
else
{
lean_dec(v_r_467_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_728_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v_size_677_; lean_object* v_k_678_; lean_object* v_v_679_; lean_object* v_l_680_; lean_object* v_r_681_; lean_object* v_size_682_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v_size_677_ = lean_ctor_get(v_l_654_, 0);
v_k_678_ = lean_ctor_get(v_l_654_, 1);
v_v_679_ = lean_ctor_get(v_l_654_, 2);
v_l_680_ = lean_ctor_get(v_l_654_, 3);
v_r_681_ = lean_ctor_get(v_l_654_, 4);
v_size_682_ = lean_ctor_get(v_r_655_, 0);
v___x_683_ = lean_unsigned_to_nat(2u);
v___x_684_ = lean_nat_mul(v___x_683_, v_size_682_);
v___x_685_ = lean_nat_dec_lt(v_size_677_, v___x_684_);
lean_dec(v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_713_; 
lean_inc(v_r_681_);
lean_inc(v_l_680_);
lean_inc(v_v_679_);
lean_inc(v_k_678_);
v_isSharedCheck_713_ = !lean_is_exclusive(v_l_654_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; lean_object* v_unused_715_; lean_object* v_unused_716_; lean_object* v_unused_717_; lean_object* v_unused_718_; 
v_unused_714_ = lean_ctor_get(v_l_654_, 4);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v_l_654_, 3);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_l_654_, 2);
lean_dec(v_unused_716_);
v_unused_717_ = lean_ctor_get(v_l_654_, 1);
lean_dec(v_unused_717_);
v_unused_718_ = lean_ctor_get(v_l_654_, 0);
lean_dec(v_unused_718_);
v___x_687_ = v_l_654_;
v_isShared_688_ = v_isSharedCheck_713_;
goto v_resetjp_686_;
}
else
{
lean_dec(v_l_654_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_713_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_703_; 
v___x_689_ = lean_nat_add(v___x_656_, v_size_665_);
v___x_690_ = lean_nat_add(v___x_689_, v_size_651_);
lean_dec(v_size_651_);
if (lean_obj_tag(v_l_680_) == 0)
{
lean_object* v_size_711_; 
v_size_711_ = lean_ctor_get(v_l_680_, 0);
lean_inc(v_size_711_);
v___y_703_ = v_size_711_;
goto v___jp_702_;
}
else
{
lean_object* v___x_712_; 
v___x_712_ = lean_unsigned_to_nat(0u);
v___y_703_ = v___x_712_;
goto v___jp_702_;
}
v___jp_691_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = lean_nat_add(v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec(v___y_693_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 4, v_r_655_);
lean_ctor_set(v___x_687_, 3, v_r_681_);
lean_ctor_set(v___x_687_, 2, v_v_653_);
lean_ctor_set(v___x_687_, 1, v_k_652_);
lean_ctor_set(v___x_687_, 0, v___x_695_);
v___x_697_ = v___x_687_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_k_652_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_v_653_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_r_681_);
lean_ctor_set(v_reuseFailAlloc_701_, 4, v_r_655_);
v___x_697_ = v_reuseFailAlloc_701_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 4, v___x_697_);
lean_ctor_set(v___x_675_, 3, v___y_692_);
lean_ctor_set(v___x_675_, 2, v_v_679_);
lean_ctor_set(v___x_675_, 1, v_k_678_);
lean_ctor_set(v___x_675_, 0, v___x_690_);
v___x_699_ = v___x_675_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_k_678_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_v_679_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v___y_692_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
v___jp_702_:
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = lean_nat_add(v___x_689_, v___y_703_);
lean_dec(v___y_703_);
lean_dec(v___x_689_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 4, v_l_680_);
lean_ctor_set(v___x_659_, 3, v_tree_662_);
lean_ctor_set(v___x_659_, 2, v_v_664_);
lean_ctor_set(v___x_659_, 1, v_k_663_);
lean_ctor_set(v___x_659_, 0, v___x_704_);
v___x_706_ = v___x_659_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_k_663_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_v_664_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v_tree_662_);
lean_ctor_set(v_reuseFailAlloc_710_, 4, v_l_680_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_707_; 
v___x_707_ = lean_nat_add(v___x_656_, v_size_682_);
if (lean_obj_tag(v_r_681_) == 0)
{
lean_object* v_size_708_; 
v_size_708_ = lean_ctor_get(v_r_681_, 0);
lean_inc(v_size_708_);
v___y_692_ = v___x_706_;
v___y_693_ = v___x_707_;
v___y_694_ = v_size_708_;
goto v___jp_691_;
}
else
{
lean_object* v___x_709_; 
v___x_709_ = lean_unsigned_to_nat(0u);
v___y_692_ = v___x_706_;
v___y_693_ = v___x_707_;
v___y_694_ = v___x_709_;
goto v___jp_691_;
}
}
}
}
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_719_ = lean_nat_add(v___x_656_, v_size_665_);
v___x_720_ = lean_nat_add(v___x_719_, v_size_651_);
lean_dec(v_size_651_);
v___x_721_ = lean_nat_add(v___x_719_, v_size_677_);
lean_dec(v___x_719_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 4, v_l_654_);
lean_ctor_set(v___x_675_, 3, v_tree_662_);
lean_ctor_set(v___x_675_, 2, v_v_664_);
lean_ctor_set(v___x_675_, 1, v_k_663_);
lean_ctor_set(v___x_675_, 0, v___x_721_);
v___x_723_ = v___x_675_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_k_663_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v_v_664_);
lean_ctor_set(v_reuseFailAlloc_727_, 3, v_tree_662_);
lean_ctor_set(v_reuseFailAlloc_727_, 4, v_l_654_);
v___x_723_ = v_reuseFailAlloc_727_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_725_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 4, v_r_655_);
lean_ctor_set(v___x_659_, 3, v___x_723_);
lean_ctor_set(v___x_659_, 2, v_v_653_);
lean_ctor_set(v___x_659_, 1, v_k_652_);
lean_ctor_set(v___x_659_, 0, v___x_720_);
v___x_725_ = v___x_659_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_k_652_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_v_653_);
lean_ctor_set(v_reuseFailAlloc_726_, 3, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_726_, 4, v_r_655_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
}
else
{
lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_787_; 
lean_inc(v_r_655_);
lean_inc(v_v_653_);
lean_inc(v_k_652_);
lean_inc(v_size_651_);
v_isSharedCheck_787_ = !lean_is_exclusive(v_r_467_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; lean_object* v_unused_789_; lean_object* v_unused_790_; lean_object* v_unused_791_; lean_object* v_unused_792_; 
v_unused_788_ = lean_ctor_get(v_r_467_, 4);
lean_dec(v_unused_788_);
v_unused_789_ = lean_ctor_get(v_r_467_, 3);
lean_dec(v_unused_789_);
v_unused_790_ = lean_ctor_get(v_r_467_, 2);
lean_dec(v_unused_790_);
v_unused_791_ = lean_ctor_get(v_r_467_, 1);
lean_dec(v_unused_791_);
v_unused_792_ = lean_ctor_get(v_r_467_, 0);
lean_dec(v_unused_792_);
v___x_735_ = v_r_467_;
v_isShared_736_ = v_isSharedCheck_787_;
goto v_resetjp_734_;
}
else
{
lean_dec(v_r_467_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_787_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
if (lean_obj_tag(v_l_654_) == 0)
{
if (lean_obj_tag(v_r_655_) == 0)
{
lean_object* v_k_737_; lean_object* v_v_738_; lean_object* v_size_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_743_; 
v_k_737_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_k_737_);
v_v_738_ = lean_ctor_get(v___x_661_, 1);
lean_inc(v_v_738_);
lean_dec_ref(v___x_661_);
v_size_739_ = lean_ctor_get(v_l_654_, 0);
v___x_740_ = lean_nat_add(v___x_656_, v_size_651_);
lean_dec(v_size_651_);
v___x_741_ = lean_nat_add(v___x_656_, v_size_739_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 4, v_l_654_);
lean_ctor_set(v___x_735_, 3, v_tree_662_);
lean_ctor_set(v___x_735_, 2, v_v_738_);
lean_ctor_set(v___x_735_, 1, v_k_737_);
lean_ctor_set(v___x_735_, 0, v___x_741_);
v___x_743_ = v___x_735_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_k_737_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_v_738_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_tree_662_);
lean_ctor_set(v_reuseFailAlloc_747_, 4, v_l_654_);
v___x_743_ = v_reuseFailAlloc_747_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_745_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 4, v_r_655_);
lean_ctor_set(v___x_659_, 3, v___x_743_);
lean_ctor_set(v___x_659_, 2, v_v_653_);
lean_ctor_set(v___x_659_, 1, v_k_652_);
lean_ctor_set(v___x_659_, 0, v___x_740_);
v___x_745_ = v___x_659_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_k_652_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_v_653_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_746_, 4, v_r_655_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
lean_object* v_k_748_; lean_object* v_v_749_; lean_object* v_k_750_; lean_object* v_v_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_765_; 
lean_dec(v_size_651_);
v_k_748_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_k_748_);
v_v_749_ = lean_ctor_get(v___x_661_, 1);
lean_inc(v_v_749_);
lean_dec_ref(v___x_661_);
v_k_750_ = lean_ctor_get(v_l_654_, 1);
v_v_751_ = lean_ctor_get(v_l_654_, 2);
v_isSharedCheck_765_ = !lean_is_exclusive(v_l_654_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; lean_object* v_unused_767_; lean_object* v_unused_768_; 
v_unused_766_ = lean_ctor_get(v_l_654_, 4);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_l_654_, 3);
lean_dec(v_unused_767_);
v_unused_768_ = lean_ctor_get(v_l_654_, 0);
lean_dec(v_unused_768_);
v___x_753_ = v_l_654_;
v_isShared_754_ = v_isSharedCheck_765_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_v_751_);
lean_inc(v_k_750_);
lean_dec(v_l_654_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_765_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_755_ = lean_unsigned_to_nat(3u);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 4, v_r_655_);
lean_ctor_set(v___x_753_, 3, v_r_655_);
lean_ctor_set(v___x_753_, 2, v_v_749_);
lean_ctor_set(v___x_753_, 1, v_k_748_);
lean_ctor_set(v___x_753_, 0, v___x_656_);
v___x_757_ = v___x_753_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_k_748_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_v_749_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_r_655_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v_r_655_);
v___x_757_ = v_reuseFailAlloc_764_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_759_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 3, v_r_655_);
lean_ctor_set(v___x_735_, 0, v___x_656_);
v___x_759_ = v___x_735_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_k_652_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v_v_653_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v_r_655_);
lean_ctor_set(v_reuseFailAlloc_763_, 4, v_r_655_);
v___x_759_ = v_reuseFailAlloc_763_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_761_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 4, v___x_759_);
lean_ctor_set(v___x_659_, 3, v___x_757_);
lean_ctor_set(v___x_659_, 2, v_v_751_);
lean_ctor_set(v___x_659_, 1, v_k_750_);
lean_ctor_set(v___x_659_, 0, v___x_755_);
v___x_761_ = v___x_659_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_k_750_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v_v_751_);
lean_ctor_set(v_reuseFailAlloc_762_, 3, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_762_, 4, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_655_) == 0)
{
lean_object* v_k_769_; lean_object* v_v_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
lean_dec(v_size_651_);
v_k_769_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_k_769_);
v_v_770_ = lean_ctor_get(v___x_661_, 1);
lean_inc(v_v_770_);
lean_dec_ref(v___x_661_);
v___x_771_ = lean_unsigned_to_nat(3u);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 4, v_l_654_);
lean_ctor_set(v___x_735_, 2, v_v_770_);
lean_ctor_set(v___x_735_, 1, v_k_769_);
lean_ctor_set(v___x_735_, 0, v___x_656_);
v___x_773_ = v___x_735_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_k_769_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_v_770_);
lean_ctor_set(v_reuseFailAlloc_777_, 3, v_l_654_);
lean_ctor_set(v_reuseFailAlloc_777_, 4, v_l_654_);
v___x_773_ = v_reuseFailAlloc_777_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_775_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 4, v_r_655_);
lean_ctor_set(v___x_659_, 3, v___x_773_);
lean_ctor_set(v___x_659_, 2, v_v_653_);
lean_ctor_set(v___x_659_, 1, v_k_652_);
lean_ctor_set(v___x_659_, 0, v___x_771_);
v___x_775_ = v___x_659_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_k_652_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v_v_653_);
lean_ctor_set(v_reuseFailAlloc_776_, 3, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_776_, 4, v_r_655_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
else
{
lean_object* v_k_778_; lean_object* v_v_779_; lean_object* v___x_781_; 
v_k_778_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_k_778_);
v_v_779_ = lean_ctor_get(v___x_661_, 1);
lean_inc(v_v_779_);
lean_dec_ref(v___x_661_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 3, v_r_655_);
v___x_781_ = v___x_735_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_size_651_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_k_652_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_v_653_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v_r_655_);
lean_ctor_set(v_reuseFailAlloc_786_, 4, v_r_655_);
v___x_781_ = v_reuseFailAlloc_786_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_unsigned_to_nat(2u);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 4, v___x_781_);
lean_ctor_set(v___x_659_, 3, v_r_655_);
lean_ctor_set(v___x_659_, 2, v_v_779_);
lean_ctor_set(v___x_659_, 1, v_k_778_);
lean_ctor_set(v___x_659_, 0, v___x_782_);
v___x_784_ = v___x_659_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_k_778_);
lean_ctor_set(v_reuseFailAlloc_785_, 2, v_v_779_);
lean_ctor_set(v_reuseFailAlloc_785_, 3, v_r_655_);
lean_ctor_set(v_reuseFailAlloc_785_, 4, v___x_781_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
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
lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_951_; 
lean_inc(v_r_655_);
lean_inc(v_v_653_);
lean_inc(v_k_652_);
v_isSharedCheck_951_ = !lean_is_exclusive(v_r_467_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; lean_object* v_unused_953_; lean_object* v_unused_954_; lean_object* v_unused_955_; lean_object* v_unused_956_; 
v_unused_952_ = lean_ctor_get(v_r_467_, 4);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v_r_467_, 3);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_r_467_, 2);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_r_467_, 1);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_r_467_, 0);
lean_dec(v_unused_956_);
v___x_800_ = v_r_467_;
v_isShared_801_ = v_isSharedCheck_951_;
goto v_resetjp_799_;
}
else
{
lean_dec(v_r_467_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_951_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v_tree_803_; 
v___x_802_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_652_, v_v_653_, v_l_654_, v_r_655_);
v_tree_803_ = lean_ctor_get(v___x_802_, 2);
lean_inc(v_tree_803_);
if (lean_obj_tag(v_tree_803_) == 0)
{
lean_object* v_k_804_; lean_object* v_v_805_; lean_object* v_size_806_; lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_k_804_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_k_804_);
v_v_805_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_v_805_);
lean_dec_ref(v___x_802_);
v_size_806_ = lean_ctor_get(v_tree_803_, 0);
v___x_807_ = lean_unsigned_to_nat(3u);
v___x_808_ = lean_nat_mul(v___x_807_, v_size_806_);
v___x_809_ = lean_nat_dec_lt(v___x_808_, v_size_646_);
lean_dec(v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
lean_dec(v_r_650_);
v___x_810_ = lean_nat_add(v___x_656_, v_size_646_);
v___x_811_ = lean_nat_add(v___x_810_, v_size_806_);
lean_dec(v___x_810_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v_tree_803_);
lean_ctor_set(v___x_800_, 3, v_l_466_);
lean_ctor_set(v___x_800_, 2, v_v_805_);
lean_ctor_set(v___x_800_, 1, v_k_804_);
lean_ctor_set(v___x_800_, 0, v___x_811_);
v___x_813_ = v___x_800_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_k_804_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_v_805_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v_l_466_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v_tree_803_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
else
{
lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_880_; 
lean_inc(v_l_649_);
lean_inc(v_v_648_);
lean_inc(v_k_647_);
lean_inc(v_size_646_);
v_isSharedCheck_880_ = !lean_is_exclusive(v_l_466_);
if (v_isSharedCheck_880_ == 0)
{
lean_object* v_unused_881_; lean_object* v_unused_882_; lean_object* v_unused_883_; lean_object* v_unused_884_; lean_object* v_unused_885_; 
v_unused_881_ = lean_ctor_get(v_l_466_, 4);
lean_dec(v_unused_881_);
v_unused_882_ = lean_ctor_get(v_l_466_, 3);
lean_dec(v_unused_882_);
v_unused_883_ = lean_ctor_get(v_l_466_, 2);
lean_dec(v_unused_883_);
v_unused_884_ = lean_ctor_get(v_l_466_, 1);
lean_dec(v_unused_884_);
v_unused_885_ = lean_ctor_get(v_l_466_, 0);
lean_dec(v_unused_885_);
v___x_816_ = v_l_466_;
v_isShared_817_ = v_isSharedCheck_880_;
goto v_resetjp_815_;
}
else
{
lean_dec(v_l_466_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_880_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v_size_818_; lean_object* v_size_819_; lean_object* v_k_820_; lean_object* v_v_821_; lean_object* v_l_822_; lean_object* v_r_823_; lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_size_818_ = lean_ctor_get(v_l_649_, 0);
v_size_819_ = lean_ctor_get(v_r_650_, 0);
v_k_820_ = lean_ctor_get(v_r_650_, 1);
v_v_821_ = lean_ctor_get(v_r_650_, 2);
v_l_822_ = lean_ctor_get(v_r_650_, 3);
v_r_823_ = lean_ctor_get(v_r_650_, 4);
v___x_824_ = lean_unsigned_to_nat(2u);
v___x_825_ = lean_nat_mul(v___x_824_, v_size_818_);
v___x_826_ = lean_nat_dec_lt(v_size_819_, v___x_825_);
lean_dec(v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_864_; 
lean_inc(v_r_823_);
lean_inc(v_l_822_);
lean_inc(v_v_821_);
lean_inc(v_k_820_);
lean_del_object(v___x_816_);
v_isSharedCheck_864_ = !lean_is_exclusive(v_r_650_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; lean_object* v_unused_866_; lean_object* v_unused_867_; lean_object* v_unused_868_; lean_object* v_unused_869_; 
v_unused_865_ = lean_ctor_get(v_r_650_, 4);
lean_dec(v_unused_865_);
v_unused_866_ = lean_ctor_get(v_r_650_, 3);
lean_dec(v_unused_866_);
v_unused_867_ = lean_ctor_get(v_r_650_, 2);
lean_dec(v_unused_867_);
v_unused_868_ = lean_ctor_get(v_r_650_, 1);
lean_dec(v_unused_868_);
v_unused_869_ = lean_ctor_get(v_r_650_, 0);
lean_dec(v_unused_869_);
v___x_828_ = v_r_650_;
v_isShared_829_ = v_isSharedCheck_864_;
goto v_resetjp_827_;
}
else
{
lean_dec(v_r_650_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_864_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___x_852_; lean_object* v___y_854_; 
v___x_830_ = lean_nat_add(v___x_656_, v_size_646_);
lean_dec(v_size_646_);
v___x_831_ = lean_nat_add(v___x_830_, v_size_806_);
lean_dec(v___x_830_);
v___x_852_ = lean_nat_add(v___x_656_, v_size_818_);
if (lean_obj_tag(v_l_822_) == 0)
{
lean_object* v_size_862_; 
v_size_862_ = lean_ctor_get(v_l_822_, 0);
lean_inc(v_size_862_);
v___y_854_ = v_size_862_;
goto v___jp_853_;
}
else
{
lean_object* v___x_863_; 
v___x_863_ = lean_unsigned_to_nat(0u);
v___y_854_ = v___x_863_;
goto v___jp_853_;
}
v___jp_832_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = lean_nat_add(v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec(v___y_834_);
lean_inc_ref(v_tree_803_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 4, v_tree_803_);
lean_ctor_set(v___x_828_, 3, v_r_823_);
lean_ctor_set(v___x_828_, 2, v_v_805_);
lean_ctor_set(v___x_828_, 1, v_k_804_);
lean_ctor_set(v___x_828_, 0, v___x_836_);
v___x_838_ = v___x_828_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_k_804_);
lean_ctor_set(v_reuseFailAlloc_851_, 2, v_v_805_);
lean_ctor_set(v_reuseFailAlloc_851_, 3, v_r_823_);
lean_ctor_set(v_reuseFailAlloc_851_, 4, v_tree_803_);
v___x_838_ = v_reuseFailAlloc_851_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
v_isSharedCheck_845_ = !lean_is_exclusive(v_tree_803_);
if (v_isSharedCheck_845_ == 0)
{
lean_object* v_unused_846_; lean_object* v_unused_847_; lean_object* v_unused_848_; lean_object* v_unused_849_; lean_object* v_unused_850_; 
v_unused_846_ = lean_ctor_get(v_tree_803_, 4);
lean_dec(v_unused_846_);
v_unused_847_ = lean_ctor_get(v_tree_803_, 3);
lean_dec(v_unused_847_);
v_unused_848_ = lean_ctor_get(v_tree_803_, 2);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v_tree_803_, 1);
lean_dec(v_unused_849_);
v_unused_850_ = lean_ctor_get(v_tree_803_, 0);
lean_dec(v_unused_850_);
v___x_840_ = v_tree_803_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_dec(v_tree_803_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 4, v___x_838_);
lean_ctor_set(v___x_840_, 3, v___y_833_);
lean_ctor_set(v___x_840_, 2, v_v_821_);
lean_ctor_set(v___x_840_, 1, v_k_820_);
lean_ctor_set(v___x_840_, 0, v___x_831_);
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v_k_820_);
lean_ctor_set(v_reuseFailAlloc_844_, 2, v_v_821_);
lean_ctor_set(v_reuseFailAlloc_844_, 3, v___y_833_);
lean_ctor_set(v_reuseFailAlloc_844_, 4, v___x_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
v___jp_853_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = lean_nat_add(v___x_852_, v___y_854_);
lean_dec(v___y_854_);
lean_dec(v___x_852_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v_l_822_);
lean_ctor_set(v___x_800_, 3, v_l_649_);
lean_ctor_set(v___x_800_, 2, v_v_648_);
lean_ctor_set(v___x_800_, 1, v_k_647_);
lean_ctor_set(v___x_800_, 0, v___x_855_);
v___x_857_ = v___x_800_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_k_647_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_v_648_);
lean_ctor_set(v_reuseFailAlloc_861_, 3, v_l_649_);
lean_ctor_set(v_reuseFailAlloc_861_, 4, v_l_822_);
v___x_857_ = v_reuseFailAlloc_861_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; 
v___x_858_ = lean_nat_add(v___x_656_, v_size_806_);
if (lean_obj_tag(v_r_823_) == 0)
{
lean_object* v_size_859_; 
v_size_859_ = lean_ctor_get(v_r_823_, 0);
lean_inc(v_size_859_);
v___y_833_ = v___x_857_;
v___y_834_ = v___x_858_;
v___y_835_ = v_size_859_;
goto v___jp_832_;
}
else
{
lean_object* v___x_860_; 
v___x_860_ = lean_unsigned_to_nat(0u);
v___y_833_ = v___x_857_;
v___y_834_ = v___x_858_;
v___y_835_ = v___x_860_;
goto v___jp_832_;
}
}
}
}
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_870_ = lean_nat_add(v___x_656_, v_size_646_);
lean_dec(v_size_646_);
v___x_871_ = lean_nat_add(v___x_870_, v_size_806_);
lean_dec(v___x_870_);
v___x_872_ = lean_nat_add(v___x_656_, v_size_806_);
v___x_873_ = lean_nat_add(v___x_872_, v_size_819_);
lean_dec(v___x_872_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v_tree_803_);
lean_ctor_set(v___x_800_, 3, v_r_650_);
lean_ctor_set(v___x_800_, 2, v_v_805_);
lean_ctor_set(v___x_800_, 1, v_k_804_);
lean_ctor_set(v___x_800_, 0, v___x_873_);
v___x_875_ = v___x_800_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_k_804_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_v_805_);
lean_ctor_set(v_reuseFailAlloc_879_, 3, v_r_650_);
lean_ctor_set(v_reuseFailAlloc_879_, 4, v_tree_803_);
v___x_875_ = v_reuseFailAlloc_879_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_877_; 
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 4, v___x_875_);
lean_ctor_set(v___x_816_, 0, v___x_871_);
v___x_877_ = v___x_816_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_k_647_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v_v_648_);
lean_ctor_set(v_reuseFailAlloc_878_, 3, v_l_649_);
lean_ctor_set(v_reuseFailAlloc_878_, 4, v___x_875_);
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
}
}
else
{
if (lean_obj_tag(v_l_649_) == 0)
{
lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_909_; 
lean_inc_ref(v_l_649_);
lean_inc(v_v_648_);
lean_inc(v_k_647_);
lean_inc(v_size_646_);
v_isSharedCheck_909_ = !lean_is_exclusive(v_l_466_);
if (v_isSharedCheck_909_ == 0)
{
lean_object* v_unused_910_; lean_object* v_unused_911_; lean_object* v_unused_912_; lean_object* v_unused_913_; lean_object* v_unused_914_; 
v_unused_910_ = lean_ctor_get(v_l_466_, 4);
lean_dec(v_unused_910_);
v_unused_911_ = lean_ctor_get(v_l_466_, 3);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v_l_466_, 2);
lean_dec(v_unused_912_);
v_unused_913_ = lean_ctor_get(v_l_466_, 1);
lean_dec(v_unused_913_);
v_unused_914_ = lean_ctor_get(v_l_466_, 0);
lean_dec(v_unused_914_);
v___x_887_ = v_l_466_;
v_isShared_888_ = v_isSharedCheck_909_;
goto v_resetjp_886_;
}
else
{
lean_dec(v_l_466_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_909_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
if (lean_obj_tag(v_r_650_) == 0)
{
lean_object* v_k_889_; lean_object* v_v_890_; lean_object* v_size_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
v_k_889_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_k_889_);
v_v_890_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_v_890_);
lean_dec_ref(v___x_802_);
v_size_891_ = lean_ctor_get(v_r_650_, 0);
v___x_892_ = lean_nat_add(v___x_656_, v_size_646_);
lean_dec(v_size_646_);
v___x_893_ = lean_nat_add(v___x_656_, v_size_891_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v_tree_803_);
lean_ctor_set(v___x_800_, 3, v_r_650_);
lean_ctor_set(v___x_800_, 2, v_v_890_);
lean_ctor_set(v___x_800_, 1, v_k_889_);
lean_ctor_set(v___x_800_, 0, v___x_893_);
v___x_895_ = v___x_800_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_k_889_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_v_890_);
lean_ctor_set(v_reuseFailAlloc_899_, 3, v_r_650_);
lean_ctor_set(v_reuseFailAlloc_899_, 4, v_tree_803_);
v___x_895_ = v_reuseFailAlloc_899_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_897_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 4, v___x_895_);
lean_ctor_set(v___x_887_, 0, v___x_892_);
v___x_897_ = v___x_887_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_k_647_);
lean_ctor_set(v_reuseFailAlloc_898_, 2, v_v_648_);
lean_ctor_set(v_reuseFailAlloc_898_, 3, v_l_649_);
lean_ctor_set(v_reuseFailAlloc_898_, 4, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
else
{
lean_object* v_k_900_; lean_object* v_v_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
lean_dec(v_size_646_);
v_k_900_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_k_900_);
v_v_901_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_v_901_);
lean_dec_ref(v___x_802_);
v___x_902_ = lean_unsigned_to_nat(3u);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v_r_650_);
lean_ctor_set(v___x_800_, 3, v_r_650_);
lean_ctor_set(v___x_800_, 2, v_v_901_);
lean_ctor_set(v___x_800_, 1, v_k_900_);
lean_ctor_set(v___x_800_, 0, v___x_656_);
v___x_904_ = v___x_800_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_k_900_);
lean_ctor_set(v_reuseFailAlloc_908_, 2, v_v_901_);
lean_ctor_set(v_reuseFailAlloc_908_, 3, v_r_650_);
lean_ctor_set(v_reuseFailAlloc_908_, 4, v_r_650_);
v___x_904_ = v_reuseFailAlloc_908_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_906_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 4, v___x_904_);
lean_ctor_set(v___x_887_, 0, v___x_902_);
v___x_906_ = v___x_887_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_k_647_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_v_648_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v_l_649_);
lean_ctor_set(v_reuseFailAlloc_907_, 4, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_650_) == 0)
{
lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_939_; 
lean_inc(v_l_649_);
lean_inc(v_v_648_);
lean_inc(v_k_647_);
v_isSharedCheck_939_ = !lean_is_exclusive(v_l_466_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; lean_object* v_unused_941_; lean_object* v_unused_942_; lean_object* v_unused_943_; lean_object* v_unused_944_; 
v_unused_940_ = lean_ctor_get(v_l_466_, 4);
lean_dec(v_unused_940_);
v_unused_941_ = lean_ctor_get(v_l_466_, 3);
lean_dec(v_unused_941_);
v_unused_942_ = lean_ctor_get(v_l_466_, 2);
lean_dec(v_unused_942_);
v_unused_943_ = lean_ctor_get(v_l_466_, 1);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v_l_466_, 0);
lean_dec(v_unused_944_);
v___x_916_ = v_l_466_;
v_isShared_917_ = v_isSharedCheck_939_;
goto v_resetjp_915_;
}
else
{
lean_dec(v_l_466_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_939_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v_k_918_; lean_object* v_v_919_; lean_object* v_k_920_; lean_object* v_v_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_935_; 
v_k_918_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_k_918_);
v_v_919_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_v_919_);
lean_dec_ref(v___x_802_);
v_k_920_ = lean_ctor_get(v_r_650_, 1);
v_v_921_ = lean_ctor_get(v_r_650_, 2);
v_isSharedCheck_935_ = !lean_is_exclusive(v_r_650_);
if (v_isSharedCheck_935_ == 0)
{
lean_object* v_unused_936_; lean_object* v_unused_937_; lean_object* v_unused_938_; 
v_unused_936_ = lean_ctor_get(v_r_650_, 4);
lean_dec(v_unused_936_);
v_unused_937_ = lean_ctor_get(v_r_650_, 3);
lean_dec(v_unused_937_);
v_unused_938_ = lean_ctor_get(v_r_650_, 0);
lean_dec(v_unused_938_);
v___x_923_ = v_r_650_;
v_isShared_924_ = v_isSharedCheck_935_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_v_921_);
lean_inc(v_k_920_);
lean_dec(v_r_650_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_935_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_925_ = lean_unsigned_to_nat(3u);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 4, v_l_649_);
lean_ctor_set(v___x_923_, 3, v_l_649_);
lean_ctor_set(v___x_923_, 2, v_v_648_);
lean_ctor_set(v___x_923_, 1, v_k_647_);
lean_ctor_set(v___x_923_, 0, v___x_656_);
v___x_927_ = v___x_923_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_k_647_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v_v_648_);
lean_ctor_set(v_reuseFailAlloc_934_, 3, v_l_649_);
lean_ctor_set(v_reuseFailAlloc_934_, 4, v_l_649_);
v___x_927_ = v_reuseFailAlloc_934_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_929_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v_l_649_);
lean_ctor_set(v___x_800_, 3, v_l_649_);
lean_ctor_set(v___x_800_, 2, v_v_919_);
lean_ctor_set(v___x_800_, 1, v_k_918_);
lean_ctor_set(v___x_800_, 0, v___x_656_);
v___x_929_ = v___x_800_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_k_918_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_v_919_);
lean_ctor_set(v_reuseFailAlloc_933_, 3, v_l_649_);
lean_ctor_set(v_reuseFailAlloc_933_, 4, v_l_649_);
v___x_929_ = v_reuseFailAlloc_933_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_931_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 4, v___x_929_);
lean_ctor_set(v___x_916_, 3, v___x_927_);
lean_ctor_set(v___x_916_, 2, v_v_921_);
lean_ctor_set(v___x_916_, 1, v_k_920_);
lean_ctor_set(v___x_916_, 0, v___x_925_);
v___x_931_ = v___x_916_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_k_920_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_v_921_);
lean_ctor_set(v_reuseFailAlloc_932_, 3, v___x_927_);
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
}
}
}
else
{
lean_object* v_k_945_; lean_object* v_v_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v_k_945_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_k_945_);
v_v_946_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_v_946_);
lean_dec_ref(v___x_802_);
v___x_947_ = lean_unsigned_to_nat(2u);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 4, v_r_650_);
lean_ctor_set(v___x_800_, 3, v_l_466_);
lean_ctor_set(v___x_800_, 2, v_v_946_);
lean_ctor_set(v___x_800_, 1, v_k_945_);
lean_ctor_set(v___x_800_, 0, v___x_947_);
v___x_949_ = v___x_800_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_k_945_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_v_946_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_l_466_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_r_650_);
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
}
}
else
{
return v_l_466_;
}
}
else
{
return v_r_467_;
}
}
default: 
{
lean_object* v_impl_957_; lean_object* v___x_958_; 
v_impl_957_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_462_, v_r_467_);
v___x_958_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_957_) == 0)
{
if (lean_obj_tag(v_l_466_) == 0)
{
lean_object* v_size_959_; lean_object* v_size_960_; lean_object* v_k_961_; lean_object* v_v_962_; lean_object* v_l_963_; lean_object* v_r_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v_size_959_ = lean_ctor_get(v_impl_957_, 0);
lean_inc(v_size_959_);
v_size_960_ = lean_ctor_get(v_l_466_, 0);
v_k_961_ = lean_ctor_get(v_l_466_, 1);
v_v_962_ = lean_ctor_get(v_l_466_, 2);
v_l_963_ = lean_ctor_get(v_l_466_, 3);
v_r_964_ = lean_ctor_get(v_l_466_, 4);
lean_inc(v_r_964_);
v___x_965_ = lean_unsigned_to_nat(3u);
v___x_966_ = lean_nat_mul(v___x_965_, v_size_959_);
v___x_967_ = lean_nat_dec_lt(v___x_966_, v_size_960_);
lean_dec(v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
lean_dec(v_r_964_);
v___x_968_ = lean_nat_add(v___x_958_, v_size_960_);
v___x_969_ = lean_nat_add(v___x_968_, v_size_959_);
lean_dec(v_size_959_);
lean_dec(v___x_968_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v_impl_957_);
lean_ctor_set(v___x_469_, 0, v___x_969_);
v___x_971_ = v___x_469_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_972_, 3, v_l_466_);
lean_ctor_set(v_reuseFailAlloc_972_, 4, v_impl_957_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
else
{
lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_1038_; 
lean_inc(v_l_963_);
lean_inc(v_v_962_);
lean_inc(v_k_961_);
lean_inc(v_size_960_);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_l_466_);
if (v_isSharedCheck_1038_ == 0)
{
lean_object* v_unused_1039_; lean_object* v_unused_1040_; lean_object* v_unused_1041_; lean_object* v_unused_1042_; lean_object* v_unused_1043_; 
v_unused_1039_ = lean_ctor_get(v_l_466_, 4);
lean_dec(v_unused_1039_);
v_unused_1040_ = lean_ctor_get(v_l_466_, 3);
lean_dec(v_unused_1040_);
v_unused_1041_ = lean_ctor_get(v_l_466_, 2);
lean_dec(v_unused_1041_);
v_unused_1042_ = lean_ctor_get(v_l_466_, 1);
lean_dec(v_unused_1042_);
v_unused_1043_ = lean_ctor_get(v_l_466_, 0);
lean_dec(v_unused_1043_);
v___x_974_ = v_l_466_;
v_isShared_975_ = v_isSharedCheck_1038_;
goto v_resetjp_973_;
}
else
{
lean_dec(v_l_466_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_1038_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v_size_976_; lean_object* v_size_977_; lean_object* v_k_978_; lean_object* v_v_979_; lean_object* v_l_980_; lean_object* v_r_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v_size_976_ = lean_ctor_get(v_l_963_, 0);
v_size_977_ = lean_ctor_get(v_r_964_, 0);
v_k_978_ = lean_ctor_get(v_r_964_, 1);
v_v_979_ = lean_ctor_get(v_r_964_, 2);
v_l_980_ = lean_ctor_get(v_r_964_, 3);
v_r_981_ = lean_ctor_get(v_r_964_, 4);
v___x_982_ = lean_unsigned_to_nat(2u);
v___x_983_ = lean_nat_mul(v___x_982_, v_size_976_);
v___x_984_ = lean_nat_dec_lt(v_size_977_, v___x_983_);
lean_dec(v___x_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1013_; 
lean_inc(v_r_981_);
lean_inc(v_l_980_);
lean_inc(v_v_979_);
lean_inc(v_k_978_);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_r_964_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; lean_object* v_unused_1015_; lean_object* v_unused_1016_; lean_object* v_unused_1017_; lean_object* v_unused_1018_; 
v_unused_1014_ = lean_ctor_get(v_r_964_, 4);
lean_dec(v_unused_1014_);
v_unused_1015_ = lean_ctor_get(v_r_964_, 3);
lean_dec(v_unused_1015_);
v_unused_1016_ = lean_ctor_get(v_r_964_, 2);
lean_dec(v_unused_1016_);
v_unused_1017_ = lean_ctor_get(v_r_964_, 1);
lean_dec(v_unused_1017_);
v_unused_1018_ = lean_ctor_get(v_r_964_, 0);
lean_dec(v_unused_1018_);
v___x_986_ = v_r_964_;
v_isShared_987_ = v_isSharedCheck_1013_;
goto v_resetjp_985_;
}
else
{
lean_dec(v_r_964_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1013_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___x_1001_; lean_object* v___y_1003_; 
v___x_988_ = lean_nat_add(v___x_958_, v_size_960_);
lean_dec(v_size_960_);
v___x_989_ = lean_nat_add(v___x_988_, v_size_959_);
lean_dec(v___x_988_);
v___x_1001_ = lean_nat_add(v___x_958_, v_size_976_);
if (lean_obj_tag(v_l_980_) == 0)
{
lean_object* v_size_1011_; 
v_size_1011_ = lean_ctor_get(v_l_980_, 0);
lean_inc(v_size_1011_);
v___y_1003_ = v_size_1011_;
goto v___jp_1002_;
}
else
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_unsigned_to_nat(0u);
v___y_1003_ = v___x_1012_;
goto v___jp_1002_;
}
v___jp_990_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = lean_nat_add(v___y_991_, v___y_993_);
lean_dec(v___y_993_);
lean_dec(v___y_991_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 4, v_impl_957_);
lean_ctor_set(v___x_986_, 3, v_r_981_);
lean_ctor_set(v___x_986_, 2, v_v_465_);
lean_ctor_set(v___x_986_, 1, v_k_464_);
lean_ctor_set(v___x_986_, 0, v___x_994_);
v___x_996_ = v___x_986_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_1000_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_1000_, 3, v_r_981_);
lean_ctor_set(v_reuseFailAlloc_1000_, 4, v_impl_957_);
v___x_996_ = v_reuseFailAlloc_1000_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_998_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 4, v___x_996_);
lean_ctor_set(v___x_974_, 3, v___y_992_);
lean_ctor_set(v___x_974_, 2, v_v_979_);
lean_ctor_set(v___x_974_, 1, v_k_978_);
lean_ctor_set(v___x_974_, 0, v___x_989_);
v___x_998_ = v___x_974_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_k_978_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_v_979_);
lean_ctor_set(v_reuseFailAlloc_999_, 3, v___y_992_);
lean_ctor_set(v_reuseFailAlloc_999_, 4, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
v___jp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1004_ = lean_nat_add(v___x_1001_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec(v___x_1001_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v_l_980_);
lean_ctor_set(v___x_469_, 3, v_l_963_);
lean_ctor_set(v___x_469_, 2, v_v_962_);
lean_ctor_set(v___x_469_, 1, v_k_961_);
lean_ctor_set(v___x_469_, 0, v___x_1004_);
v___x_1006_ = v___x_469_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_k_961_);
lean_ctor_set(v_reuseFailAlloc_1010_, 2, v_v_962_);
lean_ctor_set(v_reuseFailAlloc_1010_, 3, v_l_963_);
lean_ctor_set(v_reuseFailAlloc_1010_, 4, v_l_980_);
v___x_1006_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_nat_add(v___x_958_, v_size_959_);
lean_dec(v_size_959_);
if (lean_obj_tag(v_r_981_) == 0)
{
lean_object* v_size_1008_; 
v_size_1008_ = lean_ctor_get(v_r_981_, 0);
lean_inc(v_size_1008_);
v___y_991_ = v___x_1007_;
v___y_992_ = v___x_1006_;
v___y_993_ = v_size_1008_;
goto v___jp_990_;
}
else
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_unsigned_to_nat(0u);
v___y_991_ = v___x_1007_;
v___y_992_ = v___x_1006_;
v___y_993_ = v___x_1009_;
goto v___jp_990_;
}
}
}
}
}
else
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
lean_del_object(v___x_469_);
v___x_1019_ = lean_nat_add(v___x_958_, v_size_960_);
lean_dec(v_size_960_);
v___x_1020_ = lean_nat_add(v___x_1019_, v_size_959_);
lean_dec(v___x_1019_);
v___x_1021_ = lean_nat_add(v___x_958_, v_size_959_);
lean_dec(v_size_959_);
v___x_1022_ = lean_nat_add(v___x_1021_, v_size_977_);
lean_dec(v___x_1021_);
lean_inc_ref(v_impl_957_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 4, v_impl_957_);
lean_ctor_set(v___x_974_, 3, v_r_964_);
lean_ctor_set(v___x_974_, 2, v_v_465_);
lean_ctor_set(v___x_974_, 1, v_k_464_);
lean_ctor_set(v___x_974_, 0, v___x_1022_);
v___x_1024_ = v___x_974_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_1037_, 3, v_r_964_);
lean_ctor_set(v_reuseFailAlloc_1037_, 4, v_impl_957_);
v___x_1024_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_isSharedCheck_1031_ = !lean_is_exclusive(v_impl_957_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; lean_object* v_unused_1033_; lean_object* v_unused_1034_; lean_object* v_unused_1035_; lean_object* v_unused_1036_; 
v_unused_1032_ = lean_ctor_get(v_impl_957_, 4);
lean_dec(v_unused_1032_);
v_unused_1033_ = lean_ctor_get(v_impl_957_, 3);
lean_dec(v_unused_1033_);
v_unused_1034_ = lean_ctor_get(v_impl_957_, 2);
lean_dec(v_unused_1034_);
v_unused_1035_ = lean_ctor_get(v_impl_957_, 1);
lean_dec(v_unused_1035_);
v_unused_1036_ = lean_ctor_get(v_impl_957_, 0);
lean_dec(v_unused_1036_);
v___x_1026_ = v_impl_957_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_dec(v_impl_957_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 4, v___x_1024_);
lean_ctor_set(v___x_1026_, 3, v_l_963_);
lean_ctor_set(v___x_1026_, 2, v_v_962_);
lean_ctor_set(v___x_1026_, 1, v_k_961_);
lean_ctor_set(v___x_1026_, 0, v___x_1020_);
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1020_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_k_961_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_v_962_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v_l_963_);
lean_ctor_set(v_reuseFailAlloc_1030_, 4, v___x_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v_size_1044_ = lean_ctor_get(v_impl_957_, 0);
lean_inc(v_size_1044_);
v___x_1045_ = lean_nat_add(v___x_958_, v_size_1044_);
lean_dec(v_size_1044_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v_impl_957_);
lean_ctor_set(v___x_469_, 0, v___x_1045_);
v___x_1047_ = v___x_469_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_1048_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_1048_, 3, v_l_466_);
lean_ctor_set(v_reuseFailAlloc_1048_, 4, v_impl_957_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
else
{
if (lean_obj_tag(v_l_466_) == 0)
{
lean_object* v_l_1049_; 
v_l_1049_ = lean_ctor_get(v_l_466_, 3);
if (lean_obj_tag(v_l_1049_) == 0)
{
lean_object* v_r_1050_; 
lean_inc_ref(v_l_1049_);
v_r_1050_ = lean_ctor_get(v_l_466_, 4);
lean_inc(v_r_1050_);
if (lean_obj_tag(v_r_1050_) == 0)
{
lean_object* v_size_1051_; lean_object* v_k_1052_; lean_object* v_v_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1066_; 
v_size_1051_ = lean_ctor_get(v_l_466_, 0);
v_k_1052_ = lean_ctor_get(v_l_466_, 1);
v_v_1053_ = lean_ctor_get(v_l_466_, 2);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_l_466_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; lean_object* v_unused_1068_; 
v_unused_1067_ = lean_ctor_get(v_l_466_, 4);
lean_dec(v_unused_1067_);
v_unused_1068_ = lean_ctor_get(v_l_466_, 3);
lean_dec(v_unused_1068_);
v___x_1055_ = v_l_466_;
v_isShared_1056_ = v_isSharedCheck_1066_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_v_1053_);
lean_inc(v_k_1052_);
lean_inc(v_size_1051_);
lean_dec(v_l_466_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1066_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_size_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v_size_1057_ = lean_ctor_get(v_r_1050_, 0);
v___x_1058_ = lean_nat_add(v___x_958_, v_size_1051_);
lean_dec(v_size_1051_);
v___x_1059_ = lean_nat_add(v___x_958_, v_size_1057_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 4, v_impl_957_);
lean_ctor_set(v___x_1055_, 3, v_r_1050_);
lean_ctor_set(v___x_1055_, 2, v_v_465_);
lean_ctor_set(v___x_1055_, 1, v_k_464_);
lean_ctor_set(v___x_1055_, 0, v___x_1059_);
v___x_1061_ = v___x_1055_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_1065_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_1065_, 3, v_r_1050_);
lean_ctor_set(v_reuseFailAlloc_1065_, 4, v_impl_957_);
v___x_1061_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1063_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v___x_1061_);
lean_ctor_set(v___x_469_, 3, v_l_1049_);
lean_ctor_set(v___x_469_, 2, v_v_1053_);
lean_ctor_set(v___x_469_, 1, v_k_1052_);
lean_ctor_set(v___x_469_, 0, v___x_1058_);
v___x_1063_ = v___x_469_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_k_1052_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_v_1053_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v_l_1049_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v___x_1061_);
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
else
{
lean_object* v_k_1069_; lean_object* v_v_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1081_; 
v_k_1069_ = lean_ctor_get(v_l_466_, 1);
v_v_1070_ = lean_ctor_get(v_l_466_, 2);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_l_466_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; lean_object* v_unused_1083_; lean_object* v_unused_1084_; 
v_unused_1082_ = lean_ctor_get(v_l_466_, 4);
lean_dec(v_unused_1082_);
v_unused_1083_ = lean_ctor_get(v_l_466_, 3);
lean_dec(v_unused_1083_);
v_unused_1084_ = lean_ctor_get(v_l_466_, 0);
lean_dec(v_unused_1084_);
v___x_1072_ = v_l_466_;
v_isShared_1073_ = v_isSharedCheck_1081_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_v_1070_);
lean_inc(v_k_1069_);
lean_dec(v_l_466_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1081_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_unsigned_to_nat(3u);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 3, v_r_1050_);
lean_ctor_set(v___x_1072_, 2, v_v_465_);
lean_ctor_set(v___x_1072_, 1, v_k_464_);
lean_ctor_set(v___x_1072_, 0, v___x_958_);
v___x_1076_ = v___x_1072_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v_r_1050_);
lean_ctor_set(v_reuseFailAlloc_1080_, 4, v_r_1050_);
v___x_1076_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v___x_1076_);
lean_ctor_set(v___x_469_, 3, v_l_1049_);
lean_ctor_set(v___x_469_, 2, v_v_1070_);
lean_ctor_set(v___x_469_, 1, v_k_1069_);
lean_ctor_set(v___x_469_, 0, v___x_1074_);
v___x_1078_ = v___x_469_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_k_1069_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_v_1070_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v_l_1049_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
else
{
lean_object* v_r_1085_; 
v_r_1085_ = lean_ctor_get(v_l_466_, 4);
lean_inc(v_r_1085_);
if (lean_obj_tag(v_r_1085_) == 0)
{
lean_object* v_k_1086_; lean_object* v_v_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1110_; 
lean_inc(v_l_1049_);
v_k_1086_ = lean_ctor_get(v_l_466_, 1);
v_v_1087_ = lean_ctor_get(v_l_466_, 2);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_l_466_);
if (v_isSharedCheck_1110_ == 0)
{
lean_object* v_unused_1111_; lean_object* v_unused_1112_; lean_object* v_unused_1113_; 
v_unused_1111_ = lean_ctor_get(v_l_466_, 4);
lean_dec(v_unused_1111_);
v_unused_1112_ = lean_ctor_get(v_l_466_, 3);
lean_dec(v_unused_1112_);
v_unused_1113_ = lean_ctor_get(v_l_466_, 0);
lean_dec(v_unused_1113_);
v___x_1089_ = v_l_466_;
v_isShared_1090_ = v_isSharedCheck_1110_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_v_1087_);
lean_inc(v_k_1086_);
lean_dec(v_l_466_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1110_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v_k_1091_; lean_object* v_v_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1106_; 
v_k_1091_ = lean_ctor_get(v_r_1085_, 1);
v_v_1092_ = lean_ctor_get(v_r_1085_, 2);
v_isSharedCheck_1106_ = !lean_is_exclusive(v_r_1085_);
if (v_isSharedCheck_1106_ == 0)
{
lean_object* v_unused_1107_; lean_object* v_unused_1108_; lean_object* v_unused_1109_; 
v_unused_1107_ = lean_ctor_get(v_r_1085_, 4);
lean_dec(v_unused_1107_);
v_unused_1108_ = lean_ctor_get(v_r_1085_, 3);
lean_dec(v_unused_1108_);
v_unused_1109_ = lean_ctor_get(v_r_1085_, 0);
lean_dec(v_unused_1109_);
v___x_1094_ = v_r_1085_;
v_isShared_1095_ = v_isSharedCheck_1106_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_v_1092_);
lean_inc(v_k_1091_);
lean_dec(v_r_1085_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1106_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1096_ = lean_unsigned_to_nat(3u);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 4, v_l_1049_);
lean_ctor_set(v___x_1094_, 3, v_l_1049_);
lean_ctor_set(v___x_1094_, 2, v_v_1087_);
lean_ctor_set(v___x_1094_, 1, v_k_1086_);
lean_ctor_set(v___x_1094_, 0, v___x_958_);
v___x_1098_ = v___x_1094_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_k_1086_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v_v_1087_);
lean_ctor_set(v_reuseFailAlloc_1105_, 3, v_l_1049_);
lean_ctor_set(v_reuseFailAlloc_1105_, 4, v_l_1049_);
v___x_1098_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1100_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 4, v_l_1049_);
lean_ctor_set(v___x_1089_, 2, v_v_465_);
lean_ctor_set(v___x_1089_, 1, v_k_464_);
lean_ctor_set(v___x_1089_, 0, v___x_958_);
v___x_1100_ = v___x_1089_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_1104_, 3, v_l_1049_);
lean_ctor_set(v_reuseFailAlloc_1104_, 4, v_l_1049_);
v___x_1100_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1102_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v___x_1100_);
lean_ctor_set(v___x_469_, 3, v___x_1098_);
lean_ctor_set(v___x_469_, 2, v_v_1092_);
lean_ctor_set(v___x_469_, 1, v_k_1091_);
lean_ctor_set(v___x_469_, 0, v___x_1096_);
v___x_1102_ = v___x_469_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_k_1091_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v_v_1092_);
lean_ctor_set(v_reuseFailAlloc_1103_, 3, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1103_, 4, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1114_ = lean_unsigned_to_nat(2u);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v_r_1085_);
lean_ctor_set(v___x_469_, 0, v___x_1114_);
v___x_1116_ = v___x_469_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_1117_, 3, v_l_466_);
lean_ctor_set(v_reuseFailAlloc_1117_, 4, v_r_1085_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
else
{
lean_object* v___x_1119_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 4, v_l_466_);
lean_ctor_set(v___x_469_, 0, v___x_958_);
v___x_1119_ = v___x_469_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_k_464_);
lean_ctor_set(v_reuseFailAlloc_1120_, 2, v_v_465_);
lean_ctor_set(v_reuseFailAlloc_1120_, 3, v_l_466_);
lean_ctor_set(v_reuseFailAlloc_1120_, 4, v_l_466_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
}
}
else
{
return v_t_463_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg___boxed(lean_object* v_k_1123_, lean_object* v_t_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_1123_, v_t_1124_);
lean_dec(v_k_1123_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString(lean_object* v_declName_1126_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1128_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1129_ = lean_st_ref_take(v___x_1128_);
v___x_1130_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_declName_1126_, v___x_1129_);
v___x_1131_ = lean_st_ref_set(v___x_1128_, v___x_1130_);
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString___boxed(lean_object* v_declName_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_removeBuiltinDocString(v_declName_1133_);
lean_dec(v_declName_1133_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(lean_object* v_00_u03b2_1136_, lean_object* v_k_1137_, lean_object* v_t_1138_, lean_object* v_h_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_1137_, v_t_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___boxed(lean_object* v_00_u03b2_1141_, lean_object* v_k_1142_, lean_object* v_t_1143_, lean_object* v_h_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(v_00_u03b2_1141_, v_k_1142_, v_t_1143_, v_h_1144_);
lean_dec(v_k_1142_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings(){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1147_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1148_ = lean_st_ref_get(v___x_1147_);
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings___boxed(lean_object* v_a_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_getBuiltinVersoDocStrings();
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__0(lean_object* v_docString_1152_, lean_object* v_declName_1153_, lean_object* v_env_1154_){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = l_Lean_docStringExt;
v___x_1156_ = l_String_removeLeadingSpaces(v_docString_1152_);
v___x_1157_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1155_, v_env_1154_, v_declName_1153_, v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__1(lean_object* v_modifyEnv_1158_, lean_object* v___f_1159_, lean_object* v_____r_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_apply_1(v_modifyEnv_1158_, v___f_1159_);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l_Lean_addDocStringCore___redArg___lam__2___closed__0));
v___x_1164_ = l_Lean_stringToMessageData(v___x_1163_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_Lean_addDocStringCore___redArg___lam__2___closed__2));
v___x_1167_ = l_Lean_stringToMessageData(v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2(lean_object* v_declName_1168_, lean_object* v_modifyEnv_1169_, lean_object* v___f_1170_, lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_toBind_1173_, lean_object* v___f_1174_, lean_object* v_____do__lift_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1175_, v_declName_1168_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v___x_1177_; 
lean_dec(v___f_1174_);
lean_dec(v_toBind_1173_);
lean_dec_ref(v_inst_1172_);
lean_dec_ref(v_inst_1171_);
lean_dec(v_declName_1168_);
v___x_1177_ = lean_apply_1(v_modifyEnv_1169_, v___f_1170_);
return v___x_1177_;
}
else
{
uint8_t v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec_ref_known(v___x_1176_, 1);
lean_dec_ref(v___f_1170_);
lean_dec(v_modifyEnv_1169_);
v___x_1178_ = 0;
v___x_1179_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__1, &l_Lean_addDocStringCore___redArg___lam__2___closed__1_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1);
v___x_1180_ = l_Lean_MessageData_ofConstName(v_declName_1168_, v___x_1178_);
v___x_1181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = l_Lean_throwError___redArg(v_inst_1171_, v_inst_1172_, v___x_1183_);
v___x_1185_ = lean_apply_4(v_toBind_1173_, lean_box(0), lean_box(0), v___x_1184_, v___f_1174_);
return v___x_1185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_1186_, lean_object* v_modifyEnv_1187_, lean_object* v___f_1188_, lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_toBind_1191_, lean_object* v___f_1192_, lean_object* v_____do__lift_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_addDocStringCore___redArg___lam__2(v_declName_1186_, v_modifyEnv_1187_, v___f_1188_, v_inst_1189_, v_inst_1190_, v_toBind_1191_, v___f_1192_, v_____do__lift_1193_);
lean_dec_ref(v_____do__lift_1193_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg(lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_declName_1198_, lean_object* v_docString_1199_){
_start:
{
lean_object* v_toBind_1200_; lean_object* v_getEnv_1201_; lean_object* v_modifyEnv_1202_; lean_object* v___f_1203_; lean_object* v___f_1204_; lean_object* v___f_1205_; lean_object* v___x_1206_; 
v_toBind_1200_ = lean_ctor_get(v_inst_1195_, 1);
lean_inc_n(v_toBind_1200_, 2);
v_getEnv_1201_ = lean_ctor_get(v_inst_1197_, 0);
lean_inc(v_getEnv_1201_);
v_modifyEnv_1202_ = lean_ctor_get(v_inst_1197_, 1);
lean_inc_n(v_modifyEnv_1202_, 2);
lean_dec_ref(v_inst_1197_);
lean_inc(v_declName_1198_);
v___f_1203_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1203_, 0, v_docString_1199_);
lean_closure_set(v___f_1203_, 1, v_declName_1198_);
lean_inc_ref(v___f_1203_);
v___f_1204_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1204_, 0, v_modifyEnv_1202_);
lean_closure_set(v___f_1204_, 1, v___f_1203_);
v___f_1205_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1205_, 0, v_declName_1198_);
lean_closure_set(v___f_1205_, 1, v_modifyEnv_1202_);
lean_closure_set(v___f_1205_, 2, v___f_1203_);
lean_closure_set(v___f_1205_, 3, v_inst_1195_);
lean_closure_set(v___f_1205_, 4, v_inst_1196_);
lean_closure_set(v___f_1205_, 5, v_toBind_1200_);
lean_closure_set(v___f_1205_, 6, v___f_1204_);
v___x_1206_ = lean_apply_4(v_toBind_1200_, lean_box(0), lean_box(0), v_getEnv_1201_, v___f_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore(lean_object* v_m_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_inst_1211_, lean_object* v_declName_1212_, lean_object* v_docString_1213_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_addDocStringCore___redArg(v_inst_1208_, v_inst_1209_, v_inst_1210_, v_declName_1212_, v_docString_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___boxed(lean_object* v_m_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_inst_1219_, lean_object* v_declName_1220_, lean_object* v_docString_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_addDocStringCore(v_m_1215_, v_inst_1216_, v_inst_1217_, v_inst_1218_, v_inst_1219_, v_declName_1220_, v_docString_1221_);
lean_dec(v_inst_1219_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__0(lean_object* v_declName_1224_, lean_object* v_x_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__0___closed__0));
v___x_1227_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_1226_, v_declName_1224_, v_x_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__1(lean_object* v___f_1228_, lean_object* v_env_1229_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1230_ = l_Lean_docStringExt;
v___x_1231_ = lean_box(2);
v___x_1232_ = lean_box(0);
v___x_1233_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_1230_, v_env_1229_, v___f_1228_, v___x_1231_, v___x_1232_);
return v___x_1233_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__3___closed__0));
v___x_1236_ = l_Lean_stringToMessageData(v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3(lean_object* v_declName_1237_, lean_object* v_modifyEnv_1238_, lean_object* v___f_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_toBind_1242_, lean_object* v___f_1243_, lean_object* v_____do__lift_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1244_, v_declName_1237_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___x_1246_; 
lean_dec(v___f_1243_);
lean_dec(v_toBind_1242_);
lean_dec_ref(v_inst_1241_);
lean_dec_ref(v_inst_1240_);
lean_dec(v_declName_1237_);
v___x_1246_ = lean_apply_1(v_modifyEnv_1238_, v___f_1239_);
return v___x_1246_;
}
else
{
uint8_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec_ref_known(v___x_1245_, 1);
lean_dec_ref(v___f_1239_);
lean_dec(v_modifyEnv_1238_);
v___x_1247_ = 0;
v___x_1248_ = lean_obj_once(&l_Lean_removeDocStringCore___redArg___lam__3___closed__1, &l_Lean_removeDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1);
v___x_1249_ = l_Lean_MessageData_ofConstName(v_declName_1237_, v___x_1247_);
v___x_1250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = l_Lean_throwError___redArg(v_inst_1240_, v_inst_1241_, v___x_1252_);
v___x_1254_ = lean_apply_4(v_toBind_1242_, lean_box(0), lean_box(0), v___x_1253_, v___f_1243_);
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_1255_, lean_object* v_modifyEnv_1256_, lean_object* v___f_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_toBind_1260_, lean_object* v___f_1261_, lean_object* v_____do__lift_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_removeDocStringCore___redArg___lam__3(v_declName_1255_, v_modifyEnv_1256_, v___f_1257_, v_inst_1258_, v_inst_1259_, v_toBind_1260_, v___f_1261_, v_____do__lift_1262_);
lean_dec_ref(v_____do__lift_1262_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg(lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_declName_1267_){
_start:
{
lean_object* v_toBind_1268_; lean_object* v_getEnv_1269_; lean_object* v_modifyEnv_1270_; lean_object* v___f_1271_; lean_object* v___f_1272_; lean_object* v___f_1273_; lean_object* v___f_1274_; lean_object* v___x_1275_; 
v_toBind_1268_ = lean_ctor_get(v_inst_1264_, 1);
lean_inc_n(v_toBind_1268_, 2);
v_getEnv_1269_ = lean_ctor_get(v_inst_1266_, 0);
lean_inc(v_getEnv_1269_);
v_modifyEnv_1270_ = lean_ctor_get(v_inst_1266_, 1);
lean_inc_n(v_modifyEnv_1270_, 2);
lean_dec_ref(v_inst_1266_);
lean_inc(v_declName_1267_);
v___f_1271_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1271_, 0, v_declName_1267_);
v___f_1272_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1272_, 0, v___f_1271_);
lean_inc_ref(v___f_1272_);
v___f_1273_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1273_, 0, v_modifyEnv_1270_);
lean_closure_set(v___f_1273_, 1, v___f_1272_);
v___f_1274_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1274_, 0, v_declName_1267_);
lean_closure_set(v___f_1274_, 1, v_modifyEnv_1270_);
lean_closure_set(v___f_1274_, 2, v___f_1272_);
lean_closure_set(v___f_1274_, 3, v_inst_1264_);
lean_closure_set(v___f_1274_, 4, v_inst_1265_);
lean_closure_set(v___f_1274_, 5, v_toBind_1268_);
lean_closure_set(v___f_1274_, 6, v___f_1273_);
v___x_1275_ = lean_apply_4(v_toBind_1268_, lean_box(0), lean_box(0), v_getEnv_1269_, v___f_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore(lean_object* v_m_1276_, lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_inst_1279_, lean_object* v_inst_1280_, lean_object* v_declName_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_removeDocStringCore___redArg(v_inst_1277_, v_inst_1278_, v_inst_1279_, v_declName_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___boxed(lean_object* v_m_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_declName_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_removeDocStringCore(v_m_1283_, v_inst_1284_, v_inst_1285_, v_inst_1286_, v_inst_1287_, v_declName_1288_);
lean_dec(v_inst_1287_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___redArg(lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_declName_1293_, lean_object* v_docString_x3f_1294_){
_start:
{
if (lean_obj_tag(v_docString_x3f_1294_) == 0)
{
lean_object* v_toApplicative_1295_; lean_object* v_toPure_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v_toApplicative_1295_ = lean_ctor_get(v_inst_1290_, 0);
lean_inc_ref(v_toApplicative_1295_);
lean_dec(v_declName_1293_);
lean_dec_ref(v_inst_1292_);
lean_dec_ref(v_inst_1291_);
lean_dec_ref(v_inst_1290_);
v_toPure_1296_ = lean_ctor_get(v_toApplicative_1295_, 1);
lean_inc(v_toPure_1296_);
lean_dec_ref(v_toApplicative_1295_);
v___x_1297_ = lean_box(0);
v___x_1298_ = lean_apply_2(v_toPure_1296_, lean_box(0), v___x_1297_);
return v___x_1298_;
}
else
{
lean_object* v_val_1299_; lean_object* v___x_1300_; 
v_val_1299_ = lean_ctor_get(v_docString_x3f_1294_, 0);
lean_inc(v_val_1299_);
lean_dec_ref_known(v_docString_x3f_1294_, 1);
v___x_1300_ = l_Lean_addDocStringCore___redArg(v_inst_1290_, v_inst_1291_, v_inst_1292_, v_declName_1293_, v_val_1299_);
return v___x_1300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27(lean_object* v_m_1301_, lean_object* v_inst_1302_, lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_inst_1305_, lean_object* v_declName_1306_, lean_object* v_docString_x3f_1307_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_addDocStringCore_x27___redArg(v_inst_1302_, v_inst_1303_, v_inst_1304_, v_declName_1306_, v_docString_x3f_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___boxed(lean_object* v_m_1309_, lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_inst_1312_, lean_object* v_inst_1313_, lean_object* v_declName_1314_, lean_object* v_docString_x3f_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_addDocStringCore_x27(v_m_1309_, v_inst_1310_, v_inst_1311_, v_inst_1312_, v_inst_1313_, v_declName_1314_, v_docString_x3f_1315_);
lean_dec(v_inst_1313_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__0(lean_object* v_declName_1317_, lean_object* v_target_1318_, lean_object* v_env_1319_){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v___x_1321_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1320_, v_env_1319_, v_declName_1317_, v_target_1318_);
return v___x_1321_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__2___closed__0));
v___x_1324_ = l_Lean_stringToMessageData(v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__2(lean_object* v___x_1325_, lean_object* v_target_1326_, lean_object* v_declName_1327_, lean_object* v___x_1328_, lean_object* v_modifyEnv_1329_, lean_object* v___f_1330_, lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_toBind_1333_, lean_object* v___f_1334_, lean_object* v_____do__lift_1335_){
_start:
{
lean_object* v___x_1336_; lean_object* v_toEnvExtension_1337_; lean_object* v_asyncMode_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1336_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1337_ = lean_ctor_get(v___x_1336_, 0);
v_asyncMode_1338_ = lean_ctor_get(v_toEnvExtension_1337_, 2);
v___x_1339_ = 1;
v___x_1340_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1325_, v___x_1336_, v_____do__lift_1335_, v_target_1326_, v_asyncMode_1338_, v___x_1339_);
v___x_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1341_, 0, v_declName_1327_);
v___x_1342_ = l_Option_instBEq_beq___redArg(v___x_1328_, v___x_1340_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; 
lean_dec(v___f_1334_);
lean_dec(v_toBind_1333_);
lean_dec_ref(v_inst_1332_);
lean_dec_ref(v_inst_1331_);
v___x_1343_ = lean_apply_1(v_modifyEnv_1329_, v___f_1330_);
return v___x_1343_;
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec_ref(v___f_1330_);
lean_dec(v_modifyEnv_1329_);
v___x_1344_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__2___closed__1, &l_Lean_addInheritedDocString___redArg___lam__2___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__2___closed__1);
v___x_1345_ = l_Lean_throwError___redArg(v_inst_1331_, v_inst_1332_, v___x_1344_);
v___x_1346_ = lean_apply_4(v_toBind_1333_, lean_box(0), lean_box(0), v___x_1345_, v___f_1334_);
return v___x_1346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__1(lean_object* v_toBind_1347_, lean_object* v_getEnv_1348_, lean_object* v___f_1349_, lean_object* v_____r_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_apply_4(v_toBind_1347_, lean_box(0), lean_box(0), v_getEnv_1348_, v___f_1349_);
return v___x_1351_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__3___closed__0));
v___x_1354_ = l_Lean_stringToMessageData(v___x_1353_);
return v___x_1354_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__3___closed__2));
v___x_1357_ = l_Lean_stringToMessageData(v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__3(lean_object* v___x_1358_, lean_object* v_declName_1359_, lean_object* v_toBind_1360_, lean_object* v_getEnv_1361_, lean_object* v___f_1362_, lean_object* v_inst_1363_, lean_object* v_inst_1364_, lean_object* v___f_1365_, lean_object* v_____do__lift_1366_){
_start:
{
lean_object* v___x_1367_; lean_object* v_toEnvExtension_1368_; lean_object* v_asyncMode_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; 
v___x_1367_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1368_ = lean_ctor_get(v___x_1367_, 0);
v_asyncMode_1369_ = lean_ctor_get(v_toEnvExtension_1368_, 2);
v___x_1370_ = 1;
lean_inc(v_declName_1359_);
v___x_1371_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1358_, v___x_1367_, v_____do__lift_1366_, v_declName_1359_, v_asyncMode_1369_, v___x_1370_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v___x_1372_; 
lean_dec(v___f_1365_);
lean_dec_ref(v_inst_1364_);
lean_dec_ref(v_inst_1363_);
lean_dec(v_declName_1359_);
v___x_1372_ = lean_apply_4(v_toBind_1360_, lean_box(0), lean_box(0), v_getEnv_1361_, v___f_1362_);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_dec_ref_known(v___x_1371_, 1);
lean_dec(v___f_1362_);
lean_dec(v_getEnv_1361_);
v___x_1373_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__1, &l_Lean_addInheritedDocString___redArg___lam__3___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1);
v___x_1374_ = 0;
v___x_1375_ = l_Lean_MessageData_ofConstName(v_declName_1359_, v___x_1374_);
v___x_1376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1373_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__3, &l_Lean_addInheritedDocString___redArg___lam__3___closed__3_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__3);
v___x_1378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1376_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = l_Lean_throwError___redArg(v_inst_1363_, v_inst_1364_, v___x_1378_);
v___x_1380_ = lean_apply_4(v_toBind_1360_, lean_box(0), lean_box(0), v___x_1379_, v___f_1365_);
return v___x_1380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5(lean_object* v_declName_1381_, lean_object* v_toBind_1382_, lean_object* v_getEnv_1383_, lean_object* v___f_1384_, lean_object* v_inst_1385_, lean_object* v_inst_1386_, lean_object* v___f_1387_, lean_object* v_____do__lift_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1388_, v_declName_1381_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v___x_1390_; 
lean_dec(v___f_1387_);
lean_dec_ref(v_inst_1386_);
lean_dec_ref(v_inst_1385_);
lean_dec(v_declName_1381_);
v___x_1390_ = lean_apply_4(v_toBind_1382_, lean_box(0), lean_box(0), v_getEnv_1383_, v___f_1384_);
return v___x_1390_;
}
else
{
uint8_t v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_dec_ref_known(v___x_1389_, 1);
lean_dec(v___f_1384_);
lean_dec(v_getEnv_1383_);
v___x_1391_ = 0;
v___x_1392_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__3___closed__1, &l_Lean_addInheritedDocString___redArg___lam__3___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__3___closed__1);
v___x_1393_ = l_Lean_MessageData_ofConstName(v_declName_1381_, v___x_1391_);
v___x_1394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__3, &l_Lean_addDocStringCore___redArg___lam__2___closed__3_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__3);
v___x_1396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1394_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = l_Lean_throwError___redArg(v_inst_1385_, v_inst_1386_, v___x_1396_);
v___x_1398_ = lean_apply_4(v_toBind_1382_, lean_box(0), lean_box(0), v___x_1397_, v___f_1387_);
return v___x_1398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5___boxed(lean_object* v_declName_1399_, lean_object* v_toBind_1400_, lean_object* v_getEnv_1401_, lean_object* v___f_1402_, lean_object* v_inst_1403_, lean_object* v_inst_1404_, lean_object* v___f_1405_, lean_object* v_____do__lift_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_addInheritedDocString___redArg___lam__5(v_declName_1399_, v_toBind_1400_, v_getEnv_1401_, v___f_1402_, v_inst_1403_, v_inst_1404_, v___f_1405_, v_____do__lift_1406_);
lean_dec_ref(v_____do__lift_1406_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg(lean_object* v_inst_1409_, lean_object* v_inst_1410_, lean_object* v_inst_1411_, lean_object* v_declName_1412_, lean_object* v_target_1413_){
_start:
{
lean_object* v_toBind_1414_; lean_object* v_getEnv_1415_; lean_object* v_modifyEnv_1416_; lean_object* v___f_1417_; lean_object* v___f_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___f_1421_; lean_object* v___f_1422_; lean_object* v___f_1423_; lean_object* v___f_1424_; lean_object* v___f_1425_; lean_object* v___x_1426_; 
v_toBind_1414_ = lean_ctor_get(v_inst_1409_, 1);
lean_inc_n(v_toBind_1414_, 6);
v_getEnv_1415_ = lean_ctor_get(v_inst_1411_, 0);
lean_inc_n(v_getEnv_1415_, 5);
v_modifyEnv_1416_ = lean_ctor_get(v_inst_1411_, 1);
lean_inc_n(v_modifyEnv_1416_, 2);
lean_dec_ref(v_inst_1411_);
lean_inc(v_target_1413_);
lean_inc_n(v_declName_1412_, 3);
v___f_1417_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1417_, 0, v_declName_1412_);
lean_closure_set(v___f_1417_, 1, v_target_1413_);
lean_inc_ref(v___f_1417_);
v___f_1418_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1418_, 0, v_modifyEnv_1416_);
lean_closure_set(v___f_1418_, 1, v___f_1417_);
v___x_1419_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___closed__0));
v___x_1420_ = lean_box(0);
lean_inc_ref_n(v_inst_1410_, 2);
lean_inc_ref_n(v_inst_1409_, 2);
v___f_1421_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__2), 11, 10);
lean_closure_set(v___f_1421_, 0, v___x_1420_);
lean_closure_set(v___f_1421_, 1, v_target_1413_);
lean_closure_set(v___f_1421_, 2, v_declName_1412_);
lean_closure_set(v___f_1421_, 3, v___x_1419_);
lean_closure_set(v___f_1421_, 4, v_modifyEnv_1416_);
lean_closure_set(v___f_1421_, 5, v___f_1417_);
lean_closure_set(v___f_1421_, 6, v_inst_1409_);
lean_closure_set(v___f_1421_, 7, v_inst_1410_);
lean_closure_set(v___f_1421_, 8, v_toBind_1414_);
lean_closure_set(v___f_1421_, 9, v___f_1418_);
lean_inc_ref(v___f_1421_);
v___f_1422_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1422_, 0, v_toBind_1414_);
lean_closure_set(v___f_1422_, 1, v_getEnv_1415_);
lean_closure_set(v___f_1422_, 2, v___f_1421_);
v___f_1423_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__3), 9, 8);
lean_closure_set(v___f_1423_, 0, v___x_1420_);
lean_closure_set(v___f_1423_, 1, v_declName_1412_);
lean_closure_set(v___f_1423_, 2, v_toBind_1414_);
lean_closure_set(v___f_1423_, 3, v_getEnv_1415_);
lean_closure_set(v___f_1423_, 4, v___f_1421_);
lean_closure_set(v___f_1423_, 5, v_inst_1409_);
lean_closure_set(v___f_1423_, 6, v_inst_1410_);
lean_closure_set(v___f_1423_, 7, v___f_1422_);
lean_inc_ref(v___f_1423_);
v___f_1424_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1424_, 0, v_toBind_1414_);
lean_closure_set(v___f_1424_, 1, v_getEnv_1415_);
lean_closure_set(v___f_1424_, 2, v___f_1423_);
v___f_1425_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_1425_, 0, v_declName_1412_);
lean_closure_set(v___f_1425_, 1, v_toBind_1414_);
lean_closure_set(v___f_1425_, 2, v_getEnv_1415_);
lean_closure_set(v___f_1425_, 3, v___f_1423_);
lean_closure_set(v___f_1425_, 4, v_inst_1409_);
lean_closure_set(v___f_1425_, 5, v_inst_1410_);
lean_closure_set(v___f_1425_, 6, v___f_1424_);
v___x_1426_ = lean_apply_4(v_toBind_1414_, lean_box(0), lean_box(0), v_getEnv_1415_, v___f_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString(lean_object* v_m_1427_, lean_object* v_inst_1428_, lean_object* v_inst_1429_, lean_object* v_inst_1430_, lean_object* v_declName_1431_, lean_object* v_target_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_addInheritedDocString___redArg(v_inst_1428_, v_inst_1429_, v_inst_1430_, v_declName_1431_, v_target_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f(lean_object* v_env_1435_, lean_object* v_declName_1436_, uint8_t v_includeBuiltin_1437_){
_start:
{
lean_object* v_md_1440_; lean_object* v_v_1445_; lean_object* v___x_1452_; lean_object* v_toEnvExtension_1453_; lean_object* v_asyncMode_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; lean_object* v___x_1457_; 
v___x_1452_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1453_ = lean_ctor_get(v___x_1452_, 0);
v_asyncMode_1454_ = lean_ctor_get(v_toEnvExtension_1453_, 2);
v___x_1455_ = lean_box(0);
v___x_1456_ = 1;
lean_inc(v_declName_1436_);
lean_inc_ref(v_env_1435_);
v___x_1457_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1455_, v___x_1452_, v_env_1435_, v_declName_1436_, v_asyncMode_1454_, v___x_1456_);
if (lean_obj_tag(v___x_1457_) == 1)
{
lean_object* v_val_1458_; 
lean_dec(v_declName_1436_);
v_val_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_val_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v_declName_1436_ = v_val_1458_;
goto _start;
}
else
{
lean_object* v___x_1460_; lean_object* v_toEnvExtension_1461_; lean_object* v_asyncMode_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_dec(v___x_1457_);
v___x_1460_ = l_Lean_docStringExt;
v_toEnvExtension_1461_ = lean_ctor_get(v___x_1460_, 0);
v_asyncMode_1462_ = lean_ctor_get(v_toEnvExtension_1461_, 2);
v___x_1463_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
lean_inc(v_declName_1436_);
lean_inc_ref(v_env_1435_);
v___x_1464_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1463_, v___x_1460_, v_env_1435_, v_declName_1436_, v_asyncMode_1462_, v___x_1456_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1465_; lean_object* v_toEnvExtension_1466_; lean_object* v_asyncMode_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1465_ = l_Lean_versoDocStringExt;
v_toEnvExtension_1466_ = lean_ctor_get(v___x_1465_, 0);
v_asyncMode_1467_ = lean_ctor_get(v_toEnvExtension_1466_, 2);
v___x_1468_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default));
lean_inc(v_declName_1436_);
v___x_1469_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1468_, v___x_1465_, v_env_1435_, v_declName_1436_, v_asyncMode_1467_, v___x_1456_);
if (lean_obj_tag(v___x_1469_) == 0)
{
if (v_includeBuiltin_1437_ == 0)
{
lean_dec(v_declName_1436_);
goto v___jp_1449_;
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1470_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1471_ = lean_st_ref_get(v___x_1470_);
v___x_1472_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1471_, v_declName_1436_);
lean_dec(v___x_1471_);
if (lean_obj_tag(v___x_1472_) == 1)
{
lean_object* v_val_1473_; 
lean_dec(v_declName_1436_);
v_val_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_val_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v_md_1440_ = v_val_1473_;
goto v___jp_1439_;
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
lean_dec(v___x_1472_);
v___x_1474_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1475_ = lean_st_ref_get(v___x_1474_);
v___x_1476_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1475_, v_declName_1436_);
lean_dec(v_declName_1436_);
lean_dec(v___x_1475_);
if (lean_obj_tag(v___x_1476_) == 1)
{
lean_object* v_val_1477_; 
v_val_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_val_1477_);
lean_dec_ref_known(v___x_1476_, 1);
v_v_1445_ = v_val_1477_;
goto v___jp_1444_;
}
else
{
lean_dec(v___x_1476_);
goto v___jp_1449_;
}
}
}
}
else
{
lean_object* v_val_1478_; 
lean_dec(v_declName_1436_);
v_val_1478_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_val_1478_);
lean_dec_ref_known(v___x_1469_, 1);
v_v_1445_ = v_val_1478_;
goto v___jp_1444_;
}
}
else
{
lean_object* v_val_1479_; 
lean_dec(v_declName_1436_);
lean_dec_ref(v_env_1435_);
v_val_1479_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_val_1479_);
lean_dec_ref_known(v___x_1464_, 1);
v_md_1440_ = v_val_1479_;
goto v___jp_1439_;
}
}
v___jp_1439_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v_md_1440_);
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
return v___x_1443_;
}
v___jp_1444_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1446_, 0, v_v_1445_);
v___x_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
return v___x_1448_;
}
v___jp_1449_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_box(0);
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
return v___x_1451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f___boxed(lean_object* v_env_1480_, lean_object* v_declName_1481_, lean_object* v_includeBuiltin_1482_, lean_object* v_a_1483_){
_start:
{
uint8_t v_includeBuiltin_boxed_1484_; lean_object* v_res_1485_; 
v_includeBuiltin_boxed_1484_ = lean_unbox(v_includeBuiltin_1482_);
v_res_1485_ = l_Lean_findInternalDocString_x3f(v_env_1480_, v_declName_1481_, v_includeBuiltin_boxed_1484_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(lean_object* v_x_1486_, lean_object* v_x_1487_){
_start:
{
lean_object* v_zero_1488_; uint8_t v_isZero_1489_; 
v_zero_1488_ = lean_unsigned_to_nat(0u);
v_isZero_1489_ = lean_nat_dec_eq(v_x_1486_, v_zero_1488_);
if (v_isZero_1489_ == 1)
{
lean_dec(v_x_1486_);
return v_x_1487_;
}
else
{
uint32_t v___x_1490_; lean_object* v_one_1491_; lean_object* v_n_1492_; lean_object* v___x_1493_; 
v___x_1490_ = 32;
v_one_1491_ = lean_unsigned_to_nat(1u);
v_n_1492_ = lean_nat_sub(v_x_1486_, v_one_1491_);
lean_dec(v_x_1486_);
v___x_1493_ = lean_string_push(v_x_1487_, v___x_1490_);
v_x_1486_ = v_n_1492_;
v_x_1487_ = v___x_1493_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1521_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__9));
v___x_1522_ = lean_unsigned_to_nat(3u);
v___x_1523_ = lean_mk_empty_array_with_capacity(v___x_1522_);
v___x_1524_ = lean_array_push(v___x_1523_, v___x_1521_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(lean_object* v_x_1529_, lean_object* v_x_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v_pieces_1533_; lean_object* v___y_1534_; lean_object* v_pieces_1538_; lean_object* v___y_1539_; 
switch(lean_obj_tag(v_x_1530_))
{
case 0:
{
lean_object* v_string_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
lean_dec_ref(v_x_1529_);
v_string_1542_ = lean_ctor_get(v_x_1530_, 0);
lean_inc_ref(v_string_1542_);
lean_dec_ref_known(v_x_1530_, 1);
v___x_1543_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_string_1542_);
lean_dec_ref(v_string_1542_);
v___x_1544_ = lean_unsigned_to_nat(1u);
v___x_1545_ = lean_mk_empty_array_with_capacity(v___x_1544_);
v___x_1546_ = lean_array_push(v___x_1545_, v___x_1543_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v_a_1531_);
return v___x_1547_;
}
case 1:
{
lean_object* v_content_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1602_; 
v_content_1548_ = lean_ctor_get(v_x_1530_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_x_1530_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1550_ = v_x_1530_;
v_isShared_1551_ = v_isSharedCheck_1602_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_content_1548_);
lean_dec(v_x_1530_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1602_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set_tag(v___x_1550_, 9);
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_content_1548_);
v___x_1553_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1554_; lean_object* v_snd_1555_; lean_object* v_fst_1556_; lean_object* v_fst_1557_; lean_object* v_snd_1558_; lean_object* v_pieces_1560_; lean_object* v___y_1561_; uint8_t v_inEmph_1569_; uint8_t v_inBold_1570_; uint8_t v_inLink_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1600_; 
v___x_1554_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_1553_);
v_snd_1555_ = lean_ctor_get(v___x_1554_, 1);
lean_inc(v_snd_1555_);
v_fst_1556_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_fst_1556_);
lean_dec_ref(v___x_1554_);
v_fst_1557_ = lean_ctor_get(v_snd_1555_, 0);
lean_inc(v_fst_1557_);
v_snd_1558_ = lean_ctor_get(v_snd_1555_, 1);
lean_inc(v_snd_1558_);
lean_dec(v_snd_1555_);
v_inEmph_1569_ = lean_ctor_get_uint8(v_x_1529_, 0);
v_inBold_1570_ = lean_ctor_get_uint8(v_x_1529_, 1);
v_inLink_1571_ = lean_ctor_get_uint8(v_x_1529_, 2);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_x_1529_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1573_ = v_x_1529_;
v_isShared_1574_ = v_isSharedCheck_1600_;
goto v_resetjp_1572_;
}
else
{
lean_dec(v_x_1529_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1600_;
goto v_resetjp_1572_;
}
v___jp_1559_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1562_ = lean_string_utf8_byte_size(v_snd_1558_);
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = lean_nat_dec_eq(v___x_1562_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1565_ = lean_unsigned_to_nat(1u);
v___x_1566_ = lean_mk_empty_array_with_capacity(v___x_1565_);
v___x_1567_ = lean_array_push(v___x_1566_, v_snd_1558_);
v___x_1568_ = lean_array_push(v_pieces_1560_, v___x_1567_);
v_pieces_1538_ = v___x_1568_;
v___y_1539_ = v___y_1561_;
goto v___jp_1537_;
}
else
{
lean_dec(v_snd_1558_);
v_pieces_1538_ = v_pieces_1560_;
v___y_1539_ = v___y_1561_;
goto v___jp_1537_;
}
}
v_resetjp_1572_:
{
uint8_t v___x_1575_; lean_object* v___x_1577_; 
v___x_1575_ = 1;
if (v_isShared_1574_ == 0)
{
v___x_1577_ = v___x_1573_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1599_, 1, v_inBold_1570_);
lean_ctor_set_uint8(v_reuseFailAlloc_1599_, 2, v_inLink_1571_);
v___x_1577_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1578_; lean_object* v_fst_1579_; lean_object* v_snd_1580_; lean_object* v_pieces_1582_; lean_object* v___y_1583_; lean_object* v_pieces_1588_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
lean_ctor_set_uint8(v___x_1577_, 0, v___x_1575_);
v___x_1578_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(v___x_1577_, v_fst_1557_, v_a_1531_);
v_fst_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_fst_1579_);
v_snd_1580_ = lean_ctor_get(v___x_1578_, 1);
lean_inc(v_snd_1580_);
lean_dec_ref(v___x_1578_);
v___x_1591_ = lean_unsigned_to_nat(0u);
v___x_1592_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__2));
v___x_1593_ = lean_string_utf8_byte_size(v_fst_1556_);
v___x_1594_ = lean_nat_dec_eq(v___x_1593_, v___x_1591_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1595_ = lean_unsigned_to_nat(1u);
v___x_1596_ = lean_mk_empty_array_with_capacity(v___x_1595_);
v___x_1597_ = lean_array_push(v___x_1596_, v_fst_1556_);
v___x_1598_ = lean_array_push(v___x_1592_, v___x_1597_);
v_pieces_1588_ = v___x_1598_;
goto v___jp_1587_;
}
else
{
lean_dec(v_fst_1556_);
v_pieces_1588_ = v___x_1592_;
goto v___jp_1587_;
}
v___jp_1581_:
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_array_push(v_pieces_1582_, v_fst_1579_);
if (v_inEmph_1569_ == 0)
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__1));
v___x_1586_ = lean_array_push(v___x_1584_, v___x_1585_);
v_pieces_1560_ = v___x_1586_;
v___y_1561_ = v___y_1583_;
goto v___jp_1559_;
}
else
{
v_pieces_1560_ = v___x_1584_;
v___y_1561_ = v___y_1583_;
goto v___jp_1559_;
}
}
v___jp_1587_:
{
if (v_inEmph_1569_ == 0)
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__1));
v___x_1590_ = lean_array_push(v_pieces_1588_, v___x_1589_);
v_pieces_1582_ = v___x_1590_;
v___y_1583_ = v_snd_1580_;
goto v___jp_1581_;
}
else
{
v_pieces_1582_ = v_pieces_1588_;
v___y_1583_ = v_snd_1580_;
goto v___jp_1581_;
}
}
}
}
}
}
}
case 2:
{
lean_object* v_content_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1657_; 
v_content_1603_ = lean_ctor_get(v_x_1530_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_x_1530_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1605_ = v_x_1530_;
v_isShared_1606_ = v_isSharedCheck_1657_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_content_1603_);
lean_dec(v_x_1530_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1657_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
lean_ctor_set_tag(v___x_1605_, 9);
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_content_1603_);
v___x_1608_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1609_; lean_object* v_snd_1610_; lean_object* v_fst_1611_; lean_object* v_fst_1612_; lean_object* v_snd_1613_; lean_object* v_pieces_1615_; lean_object* v___y_1616_; uint8_t v_inEmph_1624_; uint8_t v_inBold_1625_; uint8_t v_inLink_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1655_; 
v___x_1609_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_trim(lean_box(0), v___x_1608_);
v_snd_1610_ = lean_ctor_get(v___x_1609_, 1);
lean_inc(v_snd_1610_);
v_fst_1611_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_fst_1611_);
lean_dec_ref(v___x_1609_);
v_fst_1612_ = lean_ctor_get(v_snd_1610_, 0);
lean_inc(v_fst_1612_);
v_snd_1613_ = lean_ctor_get(v_snd_1610_, 1);
lean_inc(v_snd_1613_);
lean_dec(v_snd_1610_);
v_inEmph_1624_ = lean_ctor_get_uint8(v_x_1529_, 0);
v_inBold_1625_ = lean_ctor_get_uint8(v_x_1529_, 1);
v_inLink_1626_ = lean_ctor_get_uint8(v_x_1529_, 2);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_x_1529_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1628_ = v_x_1529_;
v_isShared_1629_ = v_isSharedCheck_1655_;
goto v_resetjp_1627_;
}
else
{
lean_dec(v_x_1529_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1655_;
goto v_resetjp_1627_;
}
v___jp_1614_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1617_ = lean_string_utf8_byte_size(v_snd_1613_);
v___x_1618_ = lean_unsigned_to_nat(0u);
v___x_1619_ = lean_nat_dec_eq(v___x_1617_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1620_ = lean_unsigned_to_nat(1u);
v___x_1621_ = lean_mk_empty_array_with_capacity(v___x_1620_);
v___x_1622_ = lean_array_push(v___x_1621_, v_snd_1613_);
v___x_1623_ = lean_array_push(v_pieces_1615_, v___x_1622_);
v_pieces_1533_ = v___x_1623_;
v___y_1534_ = v___y_1616_;
goto v___jp_1532_;
}
else
{
lean_dec(v_snd_1613_);
v_pieces_1533_ = v_pieces_1615_;
v___y_1534_ = v___y_1616_;
goto v___jp_1532_;
}
}
v_resetjp_1627_:
{
uint8_t v___x_1630_; lean_object* v___x_1632_; 
v___x_1630_ = 1;
if (v_isShared_1629_ == 0)
{
v___x_1632_ = v___x_1628_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1654_, 0, v_inEmph_1624_);
lean_ctor_set_uint8(v_reuseFailAlloc_1654_, 2, v_inLink_1626_);
v___x_1632_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
lean_object* v___x_1633_; lean_object* v_fst_1634_; lean_object* v_snd_1635_; lean_object* v_pieces_1637_; lean_object* v___y_1638_; lean_object* v_pieces_1643_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
lean_ctor_set_uint8(v___x_1632_, 1, v___x_1630_);
v___x_1633_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(v___x_1632_, v_fst_1612_, v_a_1531_);
v_fst_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_fst_1634_);
v_snd_1635_ = lean_ctor_get(v___x_1633_, 1);
lean_inc(v_snd_1635_);
lean_dec_ref(v___x_1633_);
v___x_1646_ = lean_unsigned_to_nat(0u);
v___x_1647_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__2));
v___x_1648_ = lean_string_utf8_byte_size(v_fst_1611_);
v___x_1649_ = lean_nat_dec_eq(v___x_1648_, v___x_1646_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1650_ = lean_unsigned_to_nat(1u);
v___x_1651_ = lean_mk_empty_array_with_capacity(v___x_1650_);
v___x_1652_ = lean_array_push(v___x_1651_, v_fst_1611_);
v___x_1653_ = lean_array_push(v___x_1647_, v___x_1652_);
v_pieces_1643_ = v___x_1653_;
goto v___jp_1642_;
}
else
{
lean_dec(v_fst_1611_);
v_pieces_1643_ = v___x_1647_;
goto v___jp_1642_;
}
v___jp_1636_:
{
lean_object* v___x_1639_; 
v___x_1639_ = lean_array_push(v_pieces_1637_, v_fst_1634_);
if (v_inBold_1625_ == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__4));
v___x_1641_ = lean_array_push(v___x_1639_, v___x_1640_);
v_pieces_1615_ = v___x_1641_;
v___y_1616_ = v___y_1638_;
goto v___jp_1614_;
}
else
{
v_pieces_1615_ = v___x_1639_;
v___y_1616_ = v___y_1638_;
goto v___jp_1614_;
}
}
v___jp_1642_:
{
if (v_inBold_1625_ == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__4));
v___x_1645_ = lean_array_push(v_pieces_1643_, v___x_1644_);
v_pieces_1637_ = v___x_1645_;
v___y_1638_ = v_snd_1635_;
goto v___jp_1636_;
}
else
{
v_pieces_1637_ = v_pieces_1643_;
v___y_1638_ = v_snd_1635_;
goto v___jp_1636_;
}
}
}
}
}
}
}
case 3:
{
lean_object* v_string_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_dec_ref(v_x_1529_);
v_string_1658_ = lean_ctor_get(v_x_1530_, 0);
lean_inc_ref(v_string_1658_);
lean_dec_ref_known(v_x_1530_, 1);
v___x_1659_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_quoteCode(v_string_1658_);
v___x_1660_ = lean_unsigned_to_nat(1u);
v___x_1661_ = lean_mk_empty_array_with_capacity(v___x_1660_);
v___x_1662_ = lean_array_push(v___x_1661_, v___x_1659_);
v___x_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
lean_ctor_set(v___x_1663_, 1, v_a_1531_);
return v___x_1663_;
}
case 4:
{
uint8_t v_mode_1664_; 
lean_dec_ref(v_x_1529_);
v_mode_1664_ = lean_ctor_get_uint8(v_x_1530_, sizeof(void*)*1);
if (v_mode_1664_ == 0)
{
lean_object* v_string_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v_string_1665_ = lean_ctor_get(v_x_1530_, 0);
lean_inc_ref(v_string_1665_);
lean_dec_ref_known(v_x_1530_, 1);
v___x_1666_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__5));
v___x_1667_ = lean_string_append(v___x_1666_, v_string_1665_);
lean_dec_ref(v_string_1665_);
v___x_1668_ = lean_string_append(v___x_1667_, v___x_1666_);
v___x_1669_ = lean_unsigned_to_nat(1u);
v___x_1670_ = lean_mk_empty_array_with_capacity(v___x_1669_);
v___x_1671_ = lean_array_push(v___x_1670_, v___x_1668_);
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v_a_1531_);
return v___x_1672_;
}
else
{
lean_object* v_string_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v_string_1673_ = lean_ctor_get(v_x_1530_, 0);
lean_inc_ref(v_string_1673_);
lean_dec_ref_known(v_x_1530_, 1);
v___x_1674_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__6));
v___x_1675_ = lean_string_append(v___x_1674_, v_string_1673_);
lean_dec_ref(v_string_1673_);
v___x_1676_ = lean_string_append(v___x_1675_, v___x_1674_);
v___x_1677_ = lean_unsigned_to_nat(1u);
v___x_1678_ = lean_mk_empty_array_with_capacity(v___x_1677_);
v___x_1679_ = lean_array_push(v___x_1678_, v___x_1676_);
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v_a_1531_);
return v___x_1680_;
}
}
case 5:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_dec_ref_known(v_x_1530_, 1);
lean_dec_ref(v_x_1529_);
v___x_1681_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__7));
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
lean_ctor_set(v___x_1682_, 1, v_a_1531_);
return v___x_1682_;
}
case 6:
{
uint8_t v_inLink_1683_; 
v_inLink_1683_ = lean_ctor_get_uint8(v_x_1529_, 2);
if (v_inLink_1683_ == 0)
{
lean_object* v_content_1684_; lean_object* v_url_1685_; uint8_t v_inEmph_1686_; uint8_t v_inBold_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1717_; 
v_content_1684_ = lean_ctor_get(v_x_1530_, 0);
lean_inc_ref(v_content_1684_);
v_url_1685_ = lean_ctor_get(v_x_1530_, 1);
lean_inc_ref(v_url_1685_);
lean_dec_ref_known(v_x_1530_, 2);
v_inEmph_1686_ = lean_ctor_get_uint8(v_x_1529_, 0);
v_inBold_1687_ = lean_ctor_get_uint8(v_x_1529_, 1);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_x_1529_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1689_ = v_x_1529_;
v_isShared_1690_ = v_isSharedCheck_1717_;
goto v_resetjp_1688_;
}
else
{
lean_dec(v_x_1529_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1717_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
uint8_t v___x_1691_; lean_object* v___x_1693_; 
v___x_1691_ = 1;
if (v_isShared_1690_ == 0)
{
v___x_1693_ = v___x_1689_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v_reuseFailAlloc_1716_, 0, v_inEmph_1686_);
lean_ctor_set_uint8(v_reuseFailAlloc_1716_, 1, v_inBold_1687_);
v___x_1693_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v_fst_1696_; lean_object* v_snd_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1715_; 
lean_ctor_set_uint8(v___x_1693_, 2, v___x_1691_);
v___x_1694_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_1694_, 0, v_content_1684_);
v___x_1695_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(v___x_1693_, v___x_1694_, v_a_1531_);
v_fst_1696_ = lean_ctor_get(v___x_1695_, 0);
v_snd_1697_ = lean_ctor_get(v___x_1695_, 1);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1699_ = v___x_1695_;
v_isShared_1700_ = v_isSharedCheck_1715_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_snd_1697_);
lean_inc(v_fst_1696_);
lean_dec(v___x_1695_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1715_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1713_; 
v___x_1701_ = lean_unsigned_to_nat(1u);
v___x_1702_ = lean_mk_empty_array_with_capacity(v___x_1701_);
v___x_1703_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__10));
v___x_1704_ = lean_string_append(v___x_1703_, v_url_1685_);
lean_dec_ref(v_url_1685_);
v___x_1705_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__11));
v___x_1706_ = lean_string_append(v___x_1704_, v___x_1705_);
v___x_1707_ = lean_array_push(v___x_1702_, v___x_1706_);
v___x_1708_ = lean_obj_once(&l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__12, &l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__12_once, _init_l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__12);
v___x_1709_ = lean_array_push(v___x_1708_, v_fst_1696_);
v___x_1710_ = lean_array_push(v___x_1709_, v___x_1707_);
v___x_1711_ = l_Lean_Doc_joinInlines(v___x_1710_);
lean_dec_ref(v___x_1710_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v___x_1711_);
v___x_1713_ = v___x_1699_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_snd_1697_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
else
{
lean_object* v_content_1718_; size_t v_sz_1719_; size_t v___x_1720_; lean_object* v___x_1721_; lean_object* v_fst_1722_; lean_object* v_snd_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1731_; 
v_content_1718_ = lean_ctor_get(v_x_1530_, 0);
lean_inc_ref(v_content_1718_);
lean_dec_ref_known(v_x_1530_, 2);
v_sz_1719_ = lean_array_size(v_content_1718_);
v___x_1720_ = ((size_t)0ULL);
v___x_1721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__1(v_x_1529_, v_sz_1719_, v___x_1720_, v_content_1718_, v_a_1531_);
v_fst_1722_ = lean_ctor_get(v___x_1721_, 0);
v_snd_1723_ = lean_ctor_get(v___x_1721_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1725_ = v___x_1721_;
v_isShared_1726_ = v_isSharedCheck_1731_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_snd_1723_);
lean_inc(v_fst_1722_);
lean_dec(v___x_1721_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1731_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1727_ = l_Lean_Doc_joinInlines(v_fst_1722_);
lean_dec(v_fst_1722_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1727_);
v___x_1729_ = v___x_1725_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1727_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_snd_1723_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
case 7:
{
lean_object* v_name_1732_; lean_object* v_content_1733_; size_t v_sz_1734_; size_t v___x_1735_; lean_object* v___x_1736_; lean_object* v_fst_1737_; lean_object* v_snd_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1758_; 
v_name_1732_ = lean_ctor_get(v_x_1530_, 0);
lean_inc_ref(v_name_1732_);
v_content_1733_ = lean_ctor_get(v_x_1530_, 1);
lean_inc_ref(v_content_1733_);
lean_dec_ref_known(v_x_1530_, 2);
v_sz_1734_ = lean_array_size(v_content_1733_);
v___x_1735_ = ((size_t)0ULL);
v___x_1736_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__1(v_x_1529_, v_sz_1734_, v___x_1735_, v_content_1733_, v_a_1531_);
v_fst_1737_ = lean_ctor_get(v___x_1736_, 0);
v_snd_1738_ = lean_ctor_get(v___x_1736_, 1);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1740_ = v___x_1736_;
v_isShared_1741_ = v_isSharedCheck_1758_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_snd_1738_);
lean_inc(v_fst_1737_);
lean_dec(v___x_1736_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1758_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1742_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__13));
v___x_1743_ = l_Lean_Doc_joinInlines(v_fst_1737_);
lean_dec(v_fst_1737_);
v___x_1744_ = lean_array_to_list(v___x_1743_);
v___x_1745_ = l_String_intercalate(v___x_1742_, v___x_1744_);
lean_inc_ref(v_name_1732_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 1, v___x_1745_);
lean_ctor_set(v___x_1740_, 0, v_name_1732_);
v___x_1747_ = v___x_1740_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_name_1732_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1748_ = lean_array_push(v_snd_1738_, v___x_1747_);
v___x_1749_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__14));
v___x_1750_ = lean_string_append(v___x_1749_, v_name_1732_);
lean_dec_ref(v_name_1732_);
v___x_1751_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__15));
v___x_1752_ = lean_string_append(v___x_1750_, v___x_1751_);
v___x_1753_ = lean_unsigned_to_nat(1u);
v___x_1754_ = lean_mk_empty_array_with_capacity(v___x_1753_);
v___x_1755_ = lean_array_push(v___x_1754_, v___x_1752_);
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v___x_1748_);
return v___x_1756_;
}
}
}
case 8:
{
lean_object* v_alt_1759_; lean_object* v_url_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_dec_ref(v_x_1529_);
v_alt_1759_ = lean_ctor_get(v_x_1530_, 0);
lean_inc_ref(v_alt_1759_);
v_url_1760_ = lean_ctor_get(v_x_1530_, 1);
lean_inc_ref(v_url_1760_);
lean_dec_ref_known(v_x_1530_, 2);
v___x_1761_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__16));
v___x_1762_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_escape(v_alt_1759_);
lean_dec_ref(v_alt_1759_);
v___x_1763_ = lean_string_append(v___x_1761_, v___x_1762_);
lean_dec_ref(v___x_1762_);
v___x_1764_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__10));
v___x_1765_ = lean_string_append(v___x_1763_, v___x_1764_);
v___x_1766_ = lean_string_append(v___x_1765_, v_url_1760_);
lean_dec_ref(v_url_1760_);
v___x_1767_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__11));
v___x_1768_ = lean_string_append(v___x_1766_, v___x_1767_);
v___x_1769_ = lean_unsigned_to_nat(1u);
v___x_1770_ = lean_mk_empty_array_with_capacity(v___x_1769_);
v___x_1771_ = lean_array_push(v___x_1770_, v___x_1768_);
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
lean_ctor_set(v___x_1772_, 1, v_a_1531_);
return v___x_1772_;
}
case 9:
{
lean_object* v_content_1773_; size_t v_sz_1774_; size_t v___x_1775_; lean_object* v___x_1776_; lean_object* v_fst_1777_; lean_object* v_snd_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1786_; 
v_content_1773_ = lean_ctor_get(v_x_1530_, 0);
lean_inc_ref(v_content_1773_);
lean_dec_ref_known(v_x_1530_, 1);
v_sz_1774_ = lean_array_size(v_content_1773_);
v___x_1775_ = ((size_t)0ULL);
v___x_1776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__1(v_x_1529_, v_sz_1774_, v___x_1775_, v_content_1773_, v_a_1531_);
v_fst_1777_ = lean_ctor_get(v___x_1776_, 0);
v_snd_1778_ = lean_ctor_get(v___x_1776_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1780_ = v___x_1776_;
v_isShared_1781_ = v_isSharedCheck_1786_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_snd_1778_);
lean_inc(v_fst_1777_);
lean_dec(v___x_1776_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1786_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1782_ = l_Lean_Doc_joinInlines(v_fst_1777_);
lean_dec(v_fst_1777_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1782_);
v___x_1784_ = v___x_1780_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_snd_1778_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
default: 
{
lean_object* v_content_1787_; size_t v_sz_1788_; size_t v___x_1789_; lean_object* v___x_1790_; lean_object* v_fst_1791_; lean_object* v_snd_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1800_; 
v_content_1787_ = lean_ctor_get(v_x_1530_, 1);
lean_inc_ref(v_content_1787_);
lean_dec_ref_known(v_x_1530_, 2);
v_sz_1788_ = lean_array_size(v_content_1787_);
v___x_1789_ = ((size_t)0ULL);
v___x_1790_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__1(v_x_1529_, v_sz_1788_, v___x_1789_, v_content_1787_, v_a_1531_);
v_fst_1791_ = lean_ctor_get(v___x_1790_, 0);
v_snd_1792_ = lean_ctor_get(v___x_1790_, 1);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1794_ = v___x_1790_;
v_isShared_1795_ = v_isSharedCheck_1800_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_snd_1792_);
lean_inc(v_fst_1791_);
lean_dec(v___x_1790_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1800_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1796_; lean_object* v___x_1798_; 
v___x_1796_ = l_Lean_Doc_joinInlines(v_fst_1791_);
lean_dec(v_fst_1791_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1796_);
v___x_1798_ = v___x_1794_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_snd_1792_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
v___jp_1532_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = l_Lean_Doc_joinInlines(v_pieces_1533_);
lean_dec_ref(v_pieces_1533_);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
lean_ctor_set(v___x_1536_, 1, v___y_1534_);
return v___x_1536_;
}
v___jp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = l_Lean_Doc_joinInlines(v_pieces_1538_);
lean_dec_ref(v_pieces_1538_);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
lean_ctor_set(v___x_1541_, 1, v___y_1539_);
return v___x_1541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__1(lean_object* v_x_1801_, size_t v_sz_1802_, size_t v_i_1803_, lean_object* v_bs_1804_, lean_object* v___y_1805_){
_start:
{
uint8_t v___x_1806_; 
v___x_1806_ = lean_usize_dec_lt(v_i_1803_, v_sz_1802_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; 
lean_dec_ref(v_x_1801_);
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v_bs_1804_);
lean_ctor_set(v___x_1807_, 1, v___y_1805_);
return v___x_1807_;
}
else
{
lean_object* v_v_1808_; lean_object* v___x_1809_; lean_object* v_fst_1810_; lean_object* v_snd_1811_; lean_object* v___x_1812_; lean_object* v_bs_x27_1813_; size_t v___x_1814_; size_t v___x_1815_; lean_object* v___x_1816_; 
v_v_1808_ = lean_array_uget_borrowed(v_bs_1804_, v_i_1803_);
lean_inc(v_v_1808_);
lean_inc_ref(v_x_1801_);
v___x_1809_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(v_x_1801_, v_v_1808_, v___y_1805_);
v_fst_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_fst_1810_);
v_snd_1811_ = lean_ctor_get(v___x_1809_, 1);
lean_inc(v_snd_1811_);
lean_dec_ref(v___x_1809_);
v___x_1812_ = lean_unsigned_to_nat(0u);
v_bs_x27_1813_ = lean_array_uset(v_bs_1804_, v_i_1803_, v___x_1812_);
v___x_1814_ = ((size_t)1ULL);
v___x_1815_ = lean_usize_add(v_i_1803_, v___x_1814_);
v___x_1816_ = lean_array_uset(v_bs_x27_1813_, v_i_1803_, v_fst_1810_);
v_i_1803_ = v___x_1815_;
v_bs_1804_ = v___x_1816_;
v___y_1805_ = v_snd_1811_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1818_, lean_object* v_sz_1819_, lean_object* v_i_1820_, lean_object* v_bs_1821_, lean_object* v___y_1822_){
_start:
{
size_t v_sz_boxed_1823_; size_t v_i_boxed_1824_; lean_object* v_res_1825_; 
v_sz_boxed_1823_ = lean_unbox_usize(v_sz_1819_);
lean_dec(v_sz_1819_);
v_i_boxed_1824_ = lean_unbox_usize(v_i_1820_);
lean_dec(v_i_1820_);
v_res_1825_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0_spec__1(v_x_1818_, v_sz_boxed_1823_, v_i_boxed_1824_, v_bs_1821_, v___y_1822_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(size_t v_sz_1830_, size_t v_i_1831_, lean_object* v_bs_1832_, lean_object* v___y_1833_){
_start:
{
uint8_t v___x_1834_; 
v___x_1834_ = lean_usize_dec_lt(v_i_1831_, v_sz_1830_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1835_, 0, v_bs_1832_);
lean_ctor_set(v___x_1835_, 1, v___y_1833_);
return v___x_1835_;
}
else
{
lean_object* v_v_1836_; size_t v_sz_1837_; size_t v___x_1838_; lean_object* v___x_1839_; lean_object* v_fst_1840_; lean_object* v_snd_1841_; lean_object* v___x_1842_; lean_object* v_bs_x27_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; size_t v___x_1848_; size_t v___x_1849_; lean_object* v___x_1850_; 
v_v_1836_ = lean_array_uget_borrowed(v_bs_1832_, v_i_1831_);
v_sz_1837_ = lean_array_size(v_v_1836_);
v___x_1838_ = ((size_t)0ULL);
lean_inc(v_v_1836_);
v___x_1839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_sz_1837_, v___x_1838_, v_v_1836_, v___y_1833_);
v_fst_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_fst_1840_);
v_snd_1841_ = lean_ctor_get(v___x_1839_, 1);
lean_inc(v_snd_1841_);
lean_dec_ref(v___x_1839_);
v___x_1842_ = lean_unsigned_to_nat(0u);
v_bs_x27_1843_ = lean_array_uset(v_bs_1832_, v_i_1831_, v___x_1842_);
v___x_1844_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0));
v___x_1845_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__1));
v___x_1846_ = l_Lean_Doc_joinBlocks(v_fst_1840_);
lean_dec(v_fst_1840_);
v___x_1847_ = l_Lean_Doc_prefixListLines(v___x_1844_, v___x_1845_, v___x_1846_);
lean_dec_ref(v___x_1846_);
v___x_1848_ = ((size_t)1ULL);
v___x_1849_ = lean_usize_add(v_i_1831_, v___x_1848_);
v___x_1850_ = lean_array_uset(v_bs_x27_1843_, v_i_1831_, v___x_1847_);
v_i_1831_ = v___x_1849_;
v_bs_1832_ = v___x_1850_;
v___y_1833_ = v_snd_1841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(lean_object* v_as_1853_, size_t v_sz_1854_, size_t v_i_1855_, lean_object* v_b_1856_, lean_object* v___y_1857_){
_start:
{
uint8_t v___x_1858_; 
v___x_1858_ = lean_usize_dec_lt(v_i_1855_, v_sz_1854_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v_b_1856_);
lean_ctor_set(v___x_1859_, 1, v___y_1857_);
return v___x_1859_;
}
else
{
lean_object* v_a_1860_; size_t v_sz_1861_; size_t v___x_1862_; lean_object* v___x_1863_; lean_object* v_fst_1864_; lean_object* v_snd_1865_; lean_object* v_fst_1866_; lean_object* v_snd_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1888_; 
v_a_1860_ = lean_array_uget_borrowed(v_as_1853_, v_i_1855_);
v_sz_1861_ = lean_array_size(v_a_1860_);
v___x_1862_ = ((size_t)0ULL);
lean_inc(v_a_1860_);
v___x_1863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_sz_1861_, v___x_1862_, v_a_1860_, v___y_1857_);
v_fst_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_fst_1864_);
v_snd_1865_ = lean_ctor_get(v___x_1863_, 1);
lean_inc(v_snd_1865_);
lean_dec_ref(v___x_1863_);
v_fst_1866_ = lean_ctor_get(v_b_1856_, 0);
v_snd_1867_ = lean_ctor_get(v_b_1856_, 1);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_b_1856_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1869_ = v_b_1856_;
v_isShared_1870_ = v_isSharedCheck_1888_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_snd_1867_);
lean_inc(v_fst_1866_);
lean_dec(v_b_1856_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1888_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1871_ = lean_unsigned_to_nat(1u);
lean_inc(v_snd_1867_);
v___x_1872_ = l_Nat_reprFast(v_snd_1867_);
v___x_1873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8___closed__0));
v___x_1874_ = lean_string_append(v___x_1872_, v___x_1873_);
v___x_1875_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___x_1876_ = lean_string_utf8_byte_size(v___x_1874_);
v___x_1877_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__7(v___x_1876_, v___x_1875_);
v___x_1878_ = l_Lean_Doc_joinBlocks(v_fst_1864_);
lean_dec(v_fst_1864_);
v___x_1879_ = l_Lean_Doc_prefixListLines(v___x_1874_, v___x_1877_, v___x_1878_);
lean_dec_ref(v___x_1878_);
v___x_1880_ = lean_array_push(v_fst_1866_, v___x_1879_);
v___x_1881_ = lean_nat_add(v_snd_1867_, v___x_1871_);
lean_dec(v_snd_1867_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 1, v___x_1881_);
lean_ctor_set(v___x_1869_, 0, v___x_1880_);
v___x_1883_ = v___x_1869_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1880_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
size_t v___x_1884_; size_t v___x_1885_; 
v___x_1884_ = ((size_t)1ULL);
v___x_1885_ = lean_usize_add(v_i_1855_, v___x_1884_);
v_i_1855_ = v___x_1885_;
v_b_1856_ = v___x_1883_;
v___y_1857_ = v_snd_1865_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9(size_t v_sz_1894_, size_t v_i_1895_, lean_object* v_bs_1896_, lean_object* v___y_1897_){
_start:
{
uint8_t v___x_1898_; 
v___x_1898_ = lean_usize_dec_lt(v_i_1895_, v_sz_1894_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v_bs_1896_);
lean_ctor_set(v___x_1899_, 1, v___y_1897_);
return v___x_1899_;
}
else
{
lean_object* v_v_1900_; lean_object* v___x_1901_; lean_object* v_term_1902_; lean_object* v_desc_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v_fst_1906_; lean_object* v_snd_1907_; size_t v_sz_1908_; size_t v___x_1909_; lean_object* v___x_1910_; lean_object* v_fst_1911_; lean_object* v_snd_1912_; lean_object* v___x_1913_; lean_object* v_bs_x27_1914_; lean_object* v___y_1916_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; 
v_v_1900_ = lean_array_uget_borrowed(v_bs_1896_, v_i_1895_);
v___x_1901_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9___closed__0));
v_term_1902_ = lean_ctor_get(v_v_1900_, 0);
v_desc_1903_ = lean_ctor_get(v_v_1900_, 1);
lean_inc_ref_n(v_desc_1903_, 2);
lean_inc_ref(v_term_1902_);
v___x_1904_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1904_, 0, v_term_1902_);
v___x_1905_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(v___x_1901_, v___x_1904_, v___y_1897_);
v_fst_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_fst_1906_);
v_snd_1907_ = lean_ctor_get(v___x_1905_, 1);
lean_inc(v_snd_1907_);
lean_dec_ref(v___x_1905_);
v_sz_1908_ = lean_array_size(v_desc_1903_);
v___x_1909_ = ((size_t)0ULL);
v___x_1910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_sz_1908_, v___x_1909_, v_desc_1903_, v_snd_1907_);
v_fst_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_fst_1911_);
v_snd_1912_ = lean_ctor_get(v___x_1910_, 1);
lean_inc(v_snd_1912_);
lean_dec_ref(v___x_1910_);
v___x_1913_ = lean_unsigned_to_nat(0u);
v_bs_x27_1914_ = lean_array_uset(v_bs_1896_, v_i_1895_, v___x_1913_);
v___x_1924_ = lean_unsigned_to_nat(1u);
v___x_1925_ = lean_mk_empty_array_with_capacity(v___x_1924_);
v___x_1926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9___closed__2));
v___x_1927_ = lean_unsigned_to_nat(2u);
v___x_1928_ = lean_mk_empty_array_with_capacity(v___x_1927_);
v___x_1929_ = lean_array_push(v___x_1928_, v_fst_1906_);
v___x_1930_ = lean_array_push(v___x_1929_, v___x_1926_);
v___x_1931_ = l_Lean_Doc_joinInlines(v___x_1930_);
lean_dec_ref(v___x_1930_);
v___x_1932_ = lean_array_get_size(v_desc_1903_);
lean_dec_ref(v_desc_1903_);
v___x_1933_ = lean_nat_dec_le(v___x_1932_, v___x_1924_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1934_ = lean_array_push(v___x_1925_, v___x_1931_);
v___x_1935_ = l_Array_append___redArg(v___x_1934_, v_fst_1911_);
lean_dec(v_fst_1911_);
v___x_1936_ = l_Lean_Doc_joinBlocks(v___x_1935_);
lean_dec_ref(v___x_1935_);
v___y_1916_ = v___x_1936_;
goto v___jp_1915_;
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
lean_dec_ref(v___x_1925_);
v___x_1937_ = l_Lean_Doc_joinBlocks(v_fst_1911_);
lean_dec(v_fst_1911_);
v___x_1938_ = l_Array_append___redArg(v___x_1931_, v___x_1937_);
lean_dec_ref(v___x_1937_);
v___y_1916_ = v___x_1938_;
goto v___jp_1915_;
}
v___jp_1915_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; size_t v___x_1920_; size_t v___x_1921_; lean_object* v___x_1922_; 
v___x_1917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__0));
v___x_1918_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___closed__1));
v___x_1919_ = l_Lean_Doc_prefixListLines(v___x_1917_, v___x_1918_, v___y_1916_);
lean_dec_ref(v___y_1916_);
v___x_1920_ = ((size_t)1ULL);
v___x_1921_ = lean_usize_add(v_i_1895_, v___x_1920_);
v___x_1922_ = lean_array_uset(v_bs_x27_1914_, v_i_1895_, v___x_1919_);
v_i_1895_ = v___x_1921_;
v_bs_1896_ = v___x_1922_;
v___y_1897_ = v_snd_1912_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(lean_object* v_x_1940_, lean_object* v_a_1941_){
_start:
{
switch(lean_obj_tag(v_x_1940_))
{
case 0:
{
lean_object* v_contents_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1951_; 
v_contents_1942_ = lean_ctor_get(v_x_1940_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_x_1940_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1944_ = v_x_1940_;
v_isShared_1945_ = v_isSharedCheck_1951_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_contents_1942_);
lean_dec(v_x_1940_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1951_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1948_; 
v___x_1946_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9___closed__0));
if (v_isShared_1945_ == 0)
{
lean_ctor_set_tag(v___x_1944_, 9);
v___x_1948_ = v___x_1944_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_contents_1942_);
v___x_1948_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1949_; 
v___x_1949_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(v___x_1946_, v___x_1948_, v_a_1941_);
return v___x_1949_;
}
}
}
case 1:
{
lean_object* v_content_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v_content_1952_ = lean_ctor_get(v_x_1940_, 0);
lean_inc_ref(v_content_1952_);
lean_dec_ref_known(v_x_1940_, 1);
v___x_1953_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_codeBlockLines(v_content_1952_);
v___x_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
lean_ctor_set(v___x_1954_, 1, v_a_1941_);
return v___x_1954_;
}
case 2:
{
lean_object* v_items_1955_; size_t v_sz_1956_; size_t v___x_1957_; lean_object* v___x_1958_; lean_object* v_fst_1959_; lean_object* v_snd_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1968_; 
v_items_1955_ = lean_ctor_get(v_x_1940_, 0);
lean_inc_ref(v_items_1955_);
lean_dec_ref_known(v_x_1940_, 1);
v_sz_1956_ = lean_array_size(v_items_1955_);
v___x_1957_ = ((size_t)0ULL);
v___x_1958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(v_sz_1956_, v___x_1957_, v_items_1955_, v_a_1941_);
v_fst_1959_ = lean_ctor_get(v___x_1958_, 0);
v_snd_1960_ = lean_ctor_get(v___x_1958_, 1);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1962_ = v___x_1958_;
v_isShared_1963_ = v_isSharedCheck_1968_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_snd_1960_);
lean_inc(v_fst_1959_);
lean_dec(v___x_1958_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1968_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; lean_object* v___x_1966_; 
v___x_1964_ = l_Lean_Doc_joinBlocks(v_fst_1959_);
lean_dec(v_fst_1959_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1964_);
v___x_1966_ = v___x_1962_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_snd_1960_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
case 3:
{
lean_object* v_start_1969_; lean_object* v_items_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1998_; 
v_start_1969_ = lean_ctor_get(v_x_1940_, 0);
v_items_1970_ = lean_ctor_get(v_x_1940_, 1);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_x_1940_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1972_ = v_x_1940_;
v_isShared_1973_ = v_isSharedCheck_1998_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_items_1970_);
lean_inc(v_start_1969_);
lean_dec(v_x_1940_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1998_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_out_1974_; lean_object* v___y_1976_; lean_object* v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v_out_1974_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__2));
v___x_1995_ = lean_unsigned_to_nat(1u);
v___x_1996_ = l_Int_toNat(v_start_1969_);
lean_dec(v_start_1969_);
v___x_1997_ = lean_nat_dec_le(v___x_1995_, v___x_1996_);
if (v___x_1997_ == 0)
{
lean_dec(v___x_1996_);
v___y_1976_ = v___x_1995_;
goto v___jp_1975_;
}
else
{
v___y_1976_ = v___x_1996_;
goto v___jp_1975_;
}
v___jp_1975_:
{
lean_object* v___x_1978_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set_tag(v___x_1972_, 0);
lean_ctor_set(v___x_1972_, 1, v___y_1976_);
lean_ctor_set(v___x_1972_, 0, v_out_1974_);
v___x_1978_ = v___x_1972_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_out_1974_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___y_1976_);
v___x_1978_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
size_t v_sz_1979_; size_t v___x_1980_; lean_object* v___x_1981_; lean_object* v_fst_1982_; lean_object* v_snd_1983_; lean_object* v_fst_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1992_; 
v_sz_1979_ = lean_array_size(v_items_1970_);
v___x_1980_ = ((size_t)0ULL);
v___x_1981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(v_items_1970_, v_sz_1979_, v___x_1980_, v___x_1978_, v_a_1941_);
lean_dec_ref(v_items_1970_);
v_fst_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_fst_1982_);
v_snd_1983_ = lean_ctor_get(v___x_1981_, 1);
lean_inc(v_snd_1983_);
lean_dec_ref(v___x_1981_);
v_fst_1984_ = lean_ctor_get(v_fst_1982_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_fst_1982_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v_fst_1982_, 1);
lean_dec(v_unused_1993_);
v___x_1986_ = v_fst_1982_;
v_isShared_1987_ = v_isSharedCheck_1992_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_fst_1984_);
lean_dec(v_fst_1982_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1992_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1990_; 
v___x_1988_ = l_Lean_Doc_joinBlocks(v_fst_1984_);
lean_dec(v_fst_1984_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 1, v_snd_1983_);
lean_ctor_set(v___x_1986_, 0, v___x_1988_);
v___x_1990_ = v___x_1986_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_snd_1983_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
}
case 4:
{
lean_object* v_items_1999_; size_t v_sz_2000_; size_t v___x_2001_; lean_object* v___x_2002_; lean_object* v_fst_2003_; lean_object* v_snd_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2012_; 
v_items_1999_ = lean_ctor_get(v_x_1940_, 0);
lean_inc_ref(v_items_1999_);
lean_dec_ref_known(v_x_1940_, 1);
v_sz_2000_ = lean_array_size(v_items_1999_);
v___x_2001_ = ((size_t)0ULL);
v___x_2002_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9(v_sz_2000_, v___x_2001_, v_items_1999_, v_a_1941_);
v_fst_2003_ = lean_ctor_get(v___x_2002_, 0);
v_snd_2004_ = lean_ctor_get(v___x_2002_, 1);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2006_ = v___x_2002_;
v_isShared_2007_ = v_isSharedCheck_2012_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_snd_2004_);
lean_inc(v_fst_2003_);
lean_dec(v___x_2002_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2012_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2008_ = l_Lean_Doc_joinBlocks(v_fst_2003_);
lean_dec(v_fst_2003_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v___x_2008_);
v___x_2010_ = v___x_2006_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_snd_2004_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
case 5:
{
lean_object* v_items_2013_; size_t v_sz_2014_; size_t v___x_2015_; lean_object* v___x_2016_; lean_object* v_fst_2017_; lean_object* v_snd_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2028_; 
v_items_2013_ = lean_ctor_get(v_x_1940_, 0);
lean_inc_ref(v_items_2013_);
lean_dec_ref_known(v_x_1940_, 1);
v_sz_2014_ = lean_array_size(v_items_2013_);
v___x_2015_ = ((size_t)0ULL);
v___x_2016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_sz_2014_, v___x_2015_, v_items_2013_, v_a_1941_);
v_fst_2017_ = lean_ctor_get(v___x_2016_, 0);
v_snd_2018_ = lean_ctor_get(v___x_2016_, 1);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2020_ = v___x_2016_;
v_isShared_2021_ = v_isSharedCheck_2028_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_snd_2018_);
lean_inc(v_fst_2017_);
lean_dec(v___x_2016_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2028_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2022_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1___closed__0));
v___x_2023_ = l_Lean_Doc_joinBlocks(v_fst_2017_);
lean_dec(v_fst_2017_);
v___x_2024_ = l_Lean_Doc_prefixLines(v___x_2022_, v___x_2023_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2024_);
v___x_2026_ = v___x_2020_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_snd_2018_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
case 6:
{
lean_object* v_content_2029_; size_t v_sz_2030_; size_t v___x_2031_; lean_object* v___x_2032_; lean_object* v_fst_2033_; lean_object* v_snd_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2042_; 
v_content_2029_ = lean_ctor_get(v_x_1940_, 0);
lean_inc_ref(v_content_2029_);
lean_dec_ref_known(v_x_1940_, 1);
v_sz_2030_ = lean_array_size(v_content_2029_);
v___x_2031_ = ((size_t)0ULL);
v___x_2032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_sz_2030_, v___x_2031_, v_content_2029_, v_a_1941_);
v_fst_2033_ = lean_ctor_get(v___x_2032_, 0);
v_snd_2034_ = lean_ctor_get(v___x_2032_, 1);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2036_ = v___x_2032_;
v_isShared_2037_ = v_isSharedCheck_2042_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_snd_2034_);
lean_inc(v_fst_2033_);
lean_dec(v___x_2032_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2042_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2038_ = l_Lean_Doc_joinBlocks(v_fst_2033_);
lean_dec(v_fst_2033_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2038_);
v___x_2040_ = v___x_2036_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_snd_2034_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
default: 
{
lean_object* v_content_2043_; size_t v_sz_2044_; size_t v___x_2045_; lean_object* v___x_2046_; lean_object* v_fst_2047_; lean_object* v_snd_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2056_; 
v_content_2043_ = lean_ctor_get(v_x_1940_, 1);
lean_inc_ref(v_content_2043_);
lean_dec_ref_known(v_x_1940_, 2);
v_sz_2044_ = lean_array_size(v_content_2043_);
v___x_2045_ = ((size_t)0ULL);
v___x_2046_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_sz_2044_, v___x_2045_, v_content_2043_, v_a_1941_);
v_fst_2047_ = lean_ctor_get(v___x_2046_, 0);
v_snd_2048_ = lean_ctor_get(v___x_2046_, 1);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2050_ = v___x_2046_;
v_isShared_2051_ = v_isSharedCheck_2056_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_snd_2048_);
lean_inc(v_fst_2047_);
lean_dec(v___x_2046_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2056_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2052_ = l_Lean_Doc_joinBlocks(v_fst_2047_);
lean_dec(v_fst_2047_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 0, v___x_2052_);
v___x_2054_ = v___x_2050_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_snd_2048_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(size_t v_sz_2057_, size_t v_i_2058_, lean_object* v_bs_2059_, lean_object* v___y_2060_){
_start:
{
uint8_t v___x_2061_; 
v___x_2061_ = lean_usize_dec_lt(v_i_2058_, v_sz_2057_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; 
v___x_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2062_, 0, v_bs_2059_);
lean_ctor_set(v___x_2062_, 1, v___y_2060_);
return v___x_2062_;
}
else
{
lean_object* v_v_2063_; lean_object* v___x_2064_; lean_object* v_fst_2065_; lean_object* v_snd_2066_; lean_object* v___x_2067_; lean_object* v_bs_x27_2068_; size_t v___x_2069_; size_t v___x_2070_; lean_object* v___x_2071_; 
v_v_2063_ = lean_array_uget_borrowed(v_bs_2059_, v_i_2058_);
lean_inc(v_v_2063_);
v___x_2064_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v_v_2063_, v___y_2060_);
v_fst_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_fst_2065_);
v_snd_2066_ = lean_ctor_get(v___x_2064_, 1);
lean_inc(v_snd_2066_);
lean_dec_ref(v___x_2064_);
v___x_2067_ = lean_unsigned_to_nat(0u);
v_bs_x27_2068_ = lean_array_uset(v_bs_2059_, v_i_2058_, v___x_2067_);
v___x_2069_ = ((size_t)1ULL);
v___x_2070_ = lean_usize_add(v_i_2058_, v___x_2069_);
v___x_2071_ = lean_array_uset(v_bs_x27_2068_, v_i_2058_, v_fst_2065_);
v_i_2058_ = v___x_2070_;
v_bs_2059_ = v___x_2071_;
v___y_2060_ = v_snd_2066_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5___boxed(lean_object* v_sz_2073_, lean_object* v_i_2074_, lean_object* v_bs_2075_, lean_object* v___y_2076_){
_start:
{
size_t v_sz_boxed_2077_; size_t v_i_boxed_2078_; lean_object* v_res_2079_; 
v_sz_boxed_2077_ = lean_unbox_usize(v_sz_2073_);
lean_dec(v_sz_2073_);
v_i_boxed_2078_ = lean_unbox_usize(v_i_2074_);
lean_dec(v_i_2074_);
v_res_2079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__5(v_sz_boxed_2077_, v_i_boxed_2078_, v_bs_2075_, v___y_2076_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6___boxed(lean_object* v_sz_2080_, lean_object* v_i_2081_, lean_object* v_bs_2082_, lean_object* v___y_2083_){
_start:
{
size_t v_sz_boxed_2084_; size_t v_i_boxed_2085_; lean_object* v_res_2086_; 
v_sz_boxed_2084_ = lean_unbox_usize(v_sz_2080_);
lean_dec(v_sz_2080_);
v_i_boxed_2085_ = lean_unbox_usize(v_i_2081_);
lean_dec(v_i_2081_);
v_res_2086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__6(v_sz_boxed_2084_, v_i_boxed_2085_, v_bs_2082_, v___y_2083_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8___boxed(lean_object* v_as_2087_, lean_object* v_sz_2088_, lean_object* v_i_2089_, lean_object* v_b_2090_, lean_object* v___y_2091_){
_start:
{
size_t v_sz_boxed_2092_; size_t v_i_boxed_2093_; lean_object* v_res_2094_; 
v_sz_boxed_2092_ = lean_unbox_usize(v_sz_2088_);
lean_dec(v_sz_2088_);
v_i_boxed_2093_ = lean_unbox_usize(v_i_2089_);
lean_dec(v_i_2089_);
v_res_2094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__8(v_as_2087_, v_sz_boxed_2092_, v_i_boxed_2093_, v_b_2090_, v___y_2091_);
lean_dec_ref(v_as_2087_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9___boxed(lean_object* v_sz_2095_, lean_object* v_i_2096_, lean_object* v_bs_2097_, lean_object* v___y_2098_){
_start:
{
size_t v_sz_boxed_2099_; size_t v_i_boxed_2100_; lean_object* v_res_2101_; 
v_sz_boxed_2099_ = lean_unbox_usize(v_sz_2095_);
lean_dec(v_sz_2095_);
v_i_boxed_2100_ = lean_unbox_usize(v_i_2096_);
lean_dec(v_i_2096_);
v_res_2101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9(v_sz_boxed_2099_, v_i_boxed_2100_, v_bs_2097_, v___y_2098_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(size_t v_sz_2102_, size_t v_i_2103_, lean_object* v_bs_2104_, lean_object* v___y_2105_){
_start:
{
uint8_t v___x_2106_; 
v___x_2106_ = lean_usize_dec_lt(v_i_2103_, v_sz_2102_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; 
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v_bs_2104_);
lean_ctor_set(v___x_2107_, 1, v___y_2105_);
return v___x_2107_;
}
else
{
lean_object* v_v_2108_; lean_object* v___x_2109_; lean_object* v_fst_2110_; lean_object* v_snd_2111_; lean_object* v___x_2112_; lean_object* v_bs_x27_2113_; size_t v___x_2114_; size_t v___x_2115_; lean_object* v___x_2116_; 
v_v_2108_ = lean_array_uget_borrowed(v_bs_2104_, v_i_2103_);
lean_inc(v_v_2108_);
v___x_2109_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1(v_v_2108_, v___y_2105_);
v_fst_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_fst_2110_);
v_snd_2111_ = lean_ctor_get(v___x_2109_, 1);
lean_inc(v_snd_2111_);
lean_dec_ref(v___x_2109_);
v___x_2112_ = lean_unsigned_to_nat(0u);
v_bs_x27_2113_ = lean_array_uset(v_bs_2104_, v_i_2103_, v___x_2112_);
v___x_2114_ = ((size_t)1ULL);
v___x_2115_ = lean_usize_add(v_i_2103_, v___x_2114_);
v___x_2116_ = lean_array_uset(v_bs_x27_2113_, v_i_2103_, v_fst_2110_);
v_i_2103_ = v___x_2115_;
v_bs_2104_ = v___x_2116_;
v___y_2105_ = v_snd_2111_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2___boxed(lean_object* v_sz_2118_, lean_object* v_i_2119_, lean_object* v_bs_2120_, lean_object* v___y_2121_){
_start:
{
size_t v_sz_boxed_2122_; size_t v_i_boxed_2123_; lean_object* v_res_2124_; 
v_sz_boxed_2122_ = lean_unbox_usize(v_sz_2118_);
lean_dec(v_sz_2118_);
v_i_boxed_2123_ = lean_unbox_usize(v_i_2119_);
lean_dec(v_i_2119_);
v_res_2124_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_sz_boxed_2122_, v_i_boxed_2123_, v_bs_2120_, v___y_2121_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(lean_object* v_x_2125_, lean_object* v_x_2126_){
_start:
{
lean_object* v_zero_2127_; uint8_t v_isZero_2128_; 
v_zero_2127_ = lean_unsigned_to_nat(0u);
v_isZero_2128_ = lean_nat_dec_eq(v_x_2125_, v_zero_2127_);
if (v_isZero_2128_ == 1)
{
lean_dec(v_x_2125_);
return v_x_2126_;
}
else
{
uint32_t v___x_2129_; lean_object* v_one_2130_; lean_object* v_n_2131_; lean_object* v___x_2132_; 
v___x_2129_ = 35;
v_one_2130_ = lean_unsigned_to_nat(1u);
v_n_2131_ = lean_nat_sub(v_x_2125_, v_one_2130_);
lean_dec(v_x_2125_);
v___x_2132_ = lean_string_push(v_x_2126_, v___x_2129_);
v_x_2125_ = v_n_2131_;
v_x_2126_ = v___x_2132_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(size_t v_sz_2134_, size_t v_i_2135_, lean_object* v_bs_2136_, lean_object* v___y_2137_){
_start:
{
uint8_t v___x_2138_; 
v___x_2138_ = lean_usize_dec_lt(v_i_2135_, v_sz_2134_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; 
v___x_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2139_, 0, v_bs_2136_);
lean_ctor_set(v___x_2139_, 1, v___y_2137_);
return v___x_2139_;
}
else
{
lean_object* v_v_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v_fst_2143_; lean_object* v_snd_2144_; lean_object* v___x_2145_; lean_object* v_bs_x27_2146_; size_t v___x_2147_; size_t v___x_2148_; lean_object* v___x_2149_; 
v_v_2140_ = lean_array_uget_borrowed(v_bs_2136_, v_i_2135_);
v___x_2141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Markdown_0__Lean_Doc_blockMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__1_spec__9___closed__0));
lean_inc(v_v_2140_);
v___x_2142_ = l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0(v___x_2141_, v_v_2140_, v___y_2137_);
v_fst_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_fst_2143_);
v_snd_2144_ = lean_ctor_get(v___x_2142_, 1);
lean_inc(v_snd_2144_);
lean_dec_ref(v___x_2142_);
v___x_2145_ = lean_unsigned_to_nat(0u);
v_bs_x27_2146_ = lean_array_uset(v_bs_2136_, v_i_2135_, v___x_2145_);
v___x_2147_ = ((size_t)1ULL);
v___x_2148_ = lean_usize_add(v_i_2135_, v___x_2147_);
v___x_2149_ = lean_array_uset(v_bs_x27_2146_, v_i_2135_, v_fst_2143_);
v_i_2135_ = v___x_2148_;
v_bs_2136_ = v___x_2149_;
v___y_2137_ = v_snd_2144_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1___boxed(lean_object* v_sz_2151_, lean_object* v_i_2152_, lean_object* v_bs_2153_, lean_object* v___y_2154_){
_start:
{
size_t v_sz_boxed_2155_; size_t v_i_boxed_2156_; lean_object* v_res_2157_; 
v_sz_boxed_2155_ = lean_unbox_usize(v_sz_2151_);
lean_dec(v_sz_2151_);
v_i_boxed_2156_ = lean_unbox_usize(v_i_2152_);
lean_dec(v_i_2152_);
v_res_2157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_sz_boxed_2155_, v_i_boxed_2156_, v_bs_2153_, v___y_2154_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(lean_object* v_level_2159_, lean_object* v_part_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v_title_2162_; lean_object* v_content_2163_; lean_object* v_subParts_2164_; size_t v_sz_2165_; size_t v___x_2166_; lean_object* v___x_2167_; lean_object* v_fst_2168_; lean_object* v_snd_2169_; size_t v_sz_2170_; lean_object* v___x_2171_; lean_object* v_fst_2172_; lean_object* v_snd_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; size_t v_sz_2178_; lean_object* v___x_2179_; lean_object* v_fst_2180_; lean_object* v_snd_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2199_; 
v_title_2162_ = lean_ctor_get(v_part_2160_, 0);
lean_inc_ref(v_title_2162_);
v_content_2163_ = lean_ctor_get(v_part_2160_, 3);
lean_inc_ref(v_content_2163_);
v_subParts_2164_ = lean_ctor_get(v_part_2160_, 4);
lean_inc_ref(v_subParts_2164_);
lean_dec_ref(v_part_2160_);
v_sz_2165_ = lean_array_size(v_title_2162_);
v___x_2166_ = ((size_t)0ULL);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__1(v_sz_2165_, v___x_2166_, v_title_2162_, v_a_2161_);
v_fst_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_fst_2168_);
v_snd_2169_ = lean_ctor_get(v___x_2167_, 1);
lean_inc(v_snd_2169_);
lean_dec_ref(v___x_2167_);
v_sz_2170_ = lean_array_size(v_content_2163_);
v___x_2171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_sz_2170_, v___x_2166_, v_content_2163_, v_snd_2169_);
v_fst_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_fst_2172_);
v_snd_2173_ = lean_ctor_get(v___x_2171_, 1);
lean_inc(v_snd_2173_);
lean_dec_ref(v___x_2171_);
v___x_2174_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___x_2175_ = lean_unsigned_to_nat(1u);
v___x_2176_ = lean_nat_add(v_level_2159_, v___x_2175_);
lean_inc(v___x_2176_);
v___x_2177_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__2(v___x_2176_, v___x_2174_);
v_sz_2178_ = lean_array_size(v_subParts_2164_);
v___x_2179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2176_, v_sz_2178_, v___x_2166_, v_subParts_2164_, v_snd_2173_);
lean_dec(v___x_2176_);
v_fst_2180_ = lean_ctor_get(v___x_2179_, 0);
v_snd_2181_ = lean_ctor_get(v___x_2179_, 1);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2183_ = v___x_2179_;
v_isShared_2184_ = v_isSharedCheck_2199_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_snd_2181_);
lean_inc(v_fst_2180_);
lean_dec(v___x_2179_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2199_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2185_ = ((lean_object*)(l_Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___closed__0));
v___x_2186_ = lean_string_append(v___x_2177_, v___x_2185_);
v___x_2187_ = lean_mk_empty_array_with_capacity(v___x_2175_);
lean_inc_ref_n(v___x_2187_, 2);
v___x_2188_ = lean_array_push(v___x_2187_, v___x_2186_);
v___x_2189_ = lean_array_push(v___x_2187_, v___x_2188_);
v___x_2190_ = l_Array_append___redArg(v___x_2189_, v_fst_2168_);
lean_dec(v_fst_2168_);
v___x_2191_ = l_Lean_Doc_joinInlines(v___x_2190_);
lean_dec_ref(v___x_2190_);
v___x_2192_ = lean_array_push(v___x_2187_, v___x_2191_);
v___x_2193_ = l_Array_append___redArg(v___x_2192_, v_fst_2172_);
lean_dec(v_fst_2172_);
v___x_2194_ = l_Array_append___redArg(v___x_2193_, v_fst_2180_);
lean_dec(v_fst_2180_);
v___x_2195_ = l_Lean_Doc_joinBlocks(v___x_2194_);
lean_dec_ref(v___x_2194_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2195_);
v___x_2197_ = v___x_2183_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_snd_2181_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(lean_object* v___x_2200_, size_t v_sz_2201_, size_t v_i_2202_, lean_object* v_bs_2203_, lean_object* v___y_2204_){
_start:
{
uint8_t v___x_2205_; 
v___x_2205_ = lean_usize_dec_lt(v_i_2202_, v_sz_2201_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; 
v___x_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2206_, 0, v_bs_2203_);
lean_ctor_set(v___x_2206_, 1, v___y_2204_);
return v___x_2206_;
}
else
{
lean_object* v_v_2207_; lean_object* v___x_2208_; lean_object* v_fst_2209_; lean_object* v_snd_2210_; lean_object* v___x_2211_; lean_object* v_bs_x27_2212_; size_t v___x_2213_; size_t v___x_2214_; lean_object* v___x_2215_; 
v_v_2207_ = lean_array_uget_borrowed(v_bs_2203_, v_i_2202_);
lean_inc(v_v_2207_);
v___x_2208_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v___x_2200_, v_v_2207_, v___y_2204_);
v_fst_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_fst_2209_);
v_snd_2210_ = lean_ctor_get(v___x_2208_, 1);
lean_inc(v_snd_2210_);
lean_dec_ref(v___x_2208_);
v___x_2211_ = lean_unsigned_to_nat(0u);
v_bs_x27_2212_ = lean_array_uset(v_bs_2203_, v_i_2202_, v___x_2211_);
v___x_2213_ = ((size_t)1ULL);
v___x_2214_ = lean_usize_add(v_i_2202_, v___x_2213_);
v___x_2215_ = lean_array_uset(v_bs_x27_2212_, v_i_2202_, v_fst_2209_);
v_i_2202_ = v___x_2214_;
v_bs_2203_ = v___x_2215_;
v___y_2204_ = v_snd_2210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg___boxed(lean_object* v___x_2217_, lean_object* v_sz_2218_, lean_object* v_i_2219_, lean_object* v_bs_2220_, lean_object* v___y_2221_){
_start:
{
size_t v_sz_boxed_2222_; size_t v_i_boxed_2223_; lean_object* v_res_2224_; 
v_sz_boxed_2222_ = lean_unbox_usize(v_sz_2218_);
lean_dec(v_sz_2218_);
v_i_boxed_2223_ = lean_unbox_usize(v_i_2219_);
lean_dec(v_i_2219_);
v_res_2224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2217_, v_sz_boxed_2222_, v_i_boxed_2223_, v_bs_2220_, v___y_2221_);
lean_dec(v___x_2217_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg___boxed(lean_object* v_level_2225_, lean_object* v_part_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v_level_2225_, v_part_2226_, v_a_2227_);
lean_dec(v_level_2225_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(size_t v_sz_2229_, size_t v_i_2230_, lean_object* v_bs_2231_, lean_object* v___y_2232_){
_start:
{
uint8_t v___x_2233_; 
v___x_2233_ = lean_usize_dec_lt(v_i_2230_, v_sz_2229_);
if (v___x_2233_ == 0)
{
lean_object* v___x_2234_; 
v___x_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2234_, 0, v_bs_2231_);
lean_ctor_set(v___x_2234_, 1, v___y_2232_);
return v___x_2234_;
}
else
{
lean_object* v_v_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v_fst_2238_; lean_object* v_snd_2239_; lean_object* v_bs_x27_2240_; size_t v___x_2241_; size_t v___x_2242_; lean_object* v___x_2243_; 
v_v_2235_ = lean_array_uget_borrowed(v_bs_2231_, v_i_2230_);
v___x_2236_ = lean_unsigned_to_nat(0u);
lean_inc(v_v_2235_);
v___x_2237_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v___x_2236_, v_v_2235_, v___y_2232_);
v_fst_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_fst_2238_);
v_snd_2239_ = lean_ctor_get(v___x_2237_, 1);
lean_inc(v_snd_2239_);
lean_dec_ref(v___x_2237_);
v_bs_x27_2240_ = lean_array_uset(v_bs_2231_, v_i_2230_, v___x_2236_);
v___x_2241_ = ((size_t)1ULL);
v___x_2242_ = lean_usize_add(v_i_2230_, v___x_2241_);
v___x_2243_ = lean_array_uset(v_bs_x27_2240_, v_i_2230_, v_fst_2238_);
v_i_2230_ = v___x_2242_;
v_bs_2231_ = v___x_2243_;
v___y_2232_ = v_snd_2239_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3___boxed(lean_object* v_sz_2245_, lean_object* v_i_2246_, lean_object* v_bs_2247_, lean_object* v___y_2248_){
_start:
{
size_t v_sz_boxed_2249_; size_t v_i_boxed_2250_; lean_object* v_res_2251_; 
v_sz_boxed_2249_ = lean_unbox_usize(v_sz_2245_);
lean_dec(v_sz_2245_);
v_i_boxed_2250_ = lean_unbox_usize(v_i_2246_);
lean_dec(v_i_2246_);
v_res_2251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(v_sz_boxed_2249_, v_i_boxed_2250_, v_bs_2247_, v___y_2248_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(size_t v_sz_2252_, size_t v___x_2253_, lean_object* v_text_2254_, lean_object* v_subsections_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v___x_2257_; lean_object* v_fst_2258_; lean_object* v_snd_2259_; size_t v_sz_2260_; lean_object* v___x_2261_; lean_object* v_fst_2262_; lean_object* v_snd_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2272_; 
v___x_2257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__2(v_sz_2252_, v___x_2253_, v_text_2254_, v___y_2256_);
v_fst_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_fst_2258_);
v_snd_2259_ = lean_ctor_get(v___x_2257_, 1);
lean_inc(v_snd_2259_);
lean_dec_ref(v___x_2257_);
v_sz_2260_ = lean_array_size(v_subsections_2255_);
v___x_2261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__3(v_sz_2260_, v___x_2253_, v_subsections_2255_, v_snd_2259_);
v_fst_2262_ = lean_ctor_get(v___x_2261_, 0);
v_snd_2263_ = lean_ctor_get(v___x_2261_, 1);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2265_ = v___x_2261_;
v_isShared_2266_ = v_isSharedCheck_2272_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_snd_2263_);
lean_inc(v_fst_2262_);
lean_dec(v___x_2261_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2272_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2270_; 
v___x_2267_ = l_Array_append___redArg(v_fst_2258_, v_fst_2262_);
lean_dec(v_fst_2262_);
v___x_2268_ = l_Lean_Doc_joinBlocks(v___x_2267_);
lean_dec_ref(v___x_2267_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 0, v___x_2268_);
v___x_2270_ = v___x_2265_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2268_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_snd_2263_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0___boxed(lean_object* v_sz_2273_, lean_object* v___x_2274_, lean_object* v_text_2275_, lean_object* v_subsections_2276_, lean_object* v___y_2277_){
_start:
{
size_t v_sz_boxed_2278_; size_t v___x_6057__boxed_2279_; lean_object* v_res_2280_; 
v_sz_boxed_2278_ = lean_unbox_usize(v_sz_2273_);
lean_dec(v_sz_2273_);
v___x_6057__boxed_2279_ = lean_unbox_usize(v___x_2274_);
lean_dec(v___x_2274_);
v_res_2280_ = l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0(v_sz_boxed_2278_, v___x_6057__boxed_2279_, v_text_2275_, v_subsections_2276_, v___y_2277_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown(lean_object* v_a_2283_){
_start:
{
lean_object* v_text_2284_; lean_object* v_subsections_2285_; size_t v_sz_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___f_2289_; lean_object* v___x_2290_; 
v_text_2284_ = lean_ctor_get(v_a_2283_, 0);
lean_inc_ref(v_text_2284_);
v_subsections_2285_ = lean_ctor_get(v_a_2283_, 1);
lean_inc_ref(v_subsections_2285_);
lean_dec_ref(v_a_2283_);
v_sz_2286_ = lean_array_size(v_text_2284_);
v___x_2287_ = lean_box_usize(v_sz_2286_);
v___x_2288_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___boxed__const__1));
v___f_2289_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2289_, 0, v___x_2287_);
lean_closure_set(v___f_2289_, 1, v___x_2288_);
lean_closure_set(v___f_2289_, 2, v_text_2284_);
lean_closure_set(v___f_2289_, 3, v_subsections_2285_);
v___x_2290_ = l_Lean_Doc_MarkdownM_run_x27(v___f_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(lean_object* v_p_2291_, lean_object* v_level_2292_, lean_object* v_part_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___redArg(v_level_2292_, v_part_2293_, v_a_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0___boxed(lean_object* v_p_2296_, lean_object* v_level_2297_, lean_object* v_part_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0(v_p_2296_, v_level_2297_, v_part_2298_, v_a_2299_);
lean_dec(v_level_2297_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3(lean_object* v_p_2301_, lean_object* v___x_2302_, size_t v_sz_2303_, size_t v_i_2304_, lean_object* v_bs_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___redArg(v___x_2302_, v_sz_2303_, v_i_2304_, v_bs_2305_, v___y_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3___boxed(lean_object* v_p_2308_, lean_object* v___x_2309_, lean_object* v_sz_2310_, lean_object* v_i_2311_, lean_object* v_bs_2312_, lean_object* v___y_2313_){
_start:
{
size_t v_sz_boxed_2314_; size_t v_i_boxed_2315_; lean_object* v_res_2316_; 
v_sz_boxed_2314_ = lean_unbox_usize(v_sz_2310_);
lean_dec(v_sz_2310_);
v_i_boxed_2315_ = lean_unbox_usize(v_i_2311_);
lean_dec(v_i_2311_);
v_res_2316_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__3(v_p_2308_, v___x_2309_, v_sz_boxed_2314_, v_i_boxed_2315_, v_bs_2312_, v___y_2313_);
lean_dec(v___x_2309_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f(lean_object* v_env_2317_, lean_object* v_declName_2318_, uint8_t v_includeBuiltin_2319_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_findInternalDocString_x3f(v_env_2317_, v_declName_2318_, v_includeBuiltin_2319_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2350_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2324_ = v___x_2321_;
v_isShared_2325_ = v_isSharedCheck_2350_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2321_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2350_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
if (lean_obj_tag(v_a_2322_) == 0)
{
lean_object* v___x_2326_; lean_object* v___x_2328_; 
v___x_2326_ = lean_box(0);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2326_);
v___x_2328_ = v___x_2324_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
else
{
lean_object* v_val_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2349_; 
v_val_2330_ = lean_ctor_get(v_a_2322_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_a_2322_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2332_ = v_a_2322_;
v_isShared_2333_ = v_isSharedCheck_2349_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_val_2330_);
lean_dec(v_a_2322_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2349_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
if (lean_obj_tag(v_val_2330_) == 0)
{
lean_object* v_val_2334_; lean_object* v___x_2336_; 
v_val_2334_ = lean_ctor_get(v_val_2330_, 0);
lean_inc(v_val_2334_);
lean_dec_ref_known(v_val_2330_, 1);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v_val_2334_);
v___x_2336_ = v___x_2332_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_val_2334_);
v___x_2336_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2338_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2336_);
v___x_2338_ = v___x_2324_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
else
{
lean_object* v_val_2341_; lean_object* v___x_2342_; lean_object* v___x_2344_; 
v_val_2341_ = lean_ctor_get(v_val_2330_, 0);
lean_inc(v_val_2341_);
lean_dec_ref_known(v_val_2330_, 1);
v___x_2342_ = l___private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown(v_val_2341_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2342_);
v___x_2344_ = v___x_2332_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2346_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2344_);
v___x_2346_ = v___x_2324_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2344_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
v_a_2351_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2321_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2321_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSimpleDocString_x3f___boxed(lean_object* v_env_2359_, lean_object* v_declName_2360_, lean_object* v_includeBuiltin_2361_, lean_object* v_a_2362_){
_start:
{
uint8_t v_includeBuiltin_boxed_2363_; lean_object* v_res_2364_; 
v_includeBuiltin_boxed_2363_ = lean_unbox(v_includeBuiltin_2361_);
v_res_2364_ = l_Lean_findSimpleDocString_x3f(v_env_2359_, v_declName_2360_, v_includeBuiltin_boxed_2363_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v_es_2365_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_array_mk(v_es_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v_x_2369_, lean_object* v_x_2370_, lean_object* v_es_2371_){
_start:
{
lean_object* v_ents_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v_ents_2372_ = lean_array_mk(v_es_2371_);
v___x_2373_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_));
lean_inc_ref(v_ents_2372_);
v___x_2374_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
lean_ctor_set(v___x_2374_, 1, v_ents_2372_);
lean_ctor_set(v___x_2374_, 2, v_ents_2372_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v_x_2375_, lean_object* v_x_2376_, lean_object* v_es_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(v_x_2375_, v_x_2376_, v_es_2377_);
lean_dec_ref(v_x_2376_);
lean_dec_ref(v_x_2375_);
return v_res_2378_;
}
}
static lean_object* _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2379_ = lean_unsigned_to_nat(32u);
v___x_2380_ = lean_mk_empty_array_with_capacity(v___x_2379_);
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v___x_2382_, lean_object* v_x_2383_){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; size_t v___x_2387_; lean_object* v___x_2388_; 
v___x_2384_ = lean_unsigned_to_nat(32u);
v___x_2385_ = lean_mk_empty_array_with_capacity(v___x_2384_);
v___x_2386_ = lean_obj_once(&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_, &l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_);
v___x_2387_ = ((size_t)5ULL);
lean_inc(v___x_2382_);
v___x_2388_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2388_, 0, v___x_2386_);
lean_ctor_set(v___x_2388_, 1, v___x_2385_);
lean_ctor_set(v___x_2388_, 2, v___x_2382_);
lean_ctor_set(v___x_2388_, 3, v___x_2382_);
lean_ctor_set_usize(v___x_2388_, 4, v___x_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v___x_2389_, lean_object* v_x_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(v___x_2389_, v_x_2390_);
lean_dec_ref(v_x_2390_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_));
v___x_2413_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v_a_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_();
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMainModuleDoc(lean_object* v_env_2416_, lean_object* v_doc_2417_){
_start:
{
lean_object* v___x_2418_; lean_object* v_toEnvExtension_2419_; lean_object* v_asyncMode_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2418_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_2419_ = lean_ctor_get(v___x_2418_, 0);
v_asyncMode_2420_ = lean_ctor_get(v_toEnvExtension_2419_, 2);
v___x_2421_ = lean_box(0);
v___x_2422_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2418_, v_env_2416_, v_doc_2417_, v_asyncMode_2420_, v___x_2421_);
return v___x_2422_;
}
}
static lean_object* _init_l_Lean_getMainModuleDoc___closed__0(void){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModuleDoc(lean_object* v_env_2424_){
_start:
{
lean_object* v___x_2425_; lean_object* v_toEnvExtension_2426_; lean_object* v_asyncMode_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2425_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_2426_ = lean_ctor_get(v___x_2425_, 0);
v_asyncMode_2427_ = lean_ctor_get(v_toEnvExtension_2426_, 2);
v___x_2428_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_2429_ = lean_box(0);
v___x_2430_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2428_, v___x_2425_, v_env_2424_, v_asyncMode_2427_, v___x_2429_);
return v___x_2430_;
}
}
static lean_object* _init_l_Lean_getModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2431_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_2432_ = lean_box(0);
v___x_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
lean_ctor_set(v___x_2433_, 1, v___x_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f(lean_object* v_env_2434_, lean_object* v_moduleName_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_Environment_getModuleIdx_x3f(v_env_2434_, v_moduleName_2435_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v___x_2437_; 
v___x_2437_ = lean_box(0);
return v___x_2437_;
}
else
{
lean_object* v_val_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2449_; 
v_val_2438_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2440_ = v___x_2436_;
v_isShared_2441_ = v_isSharedCheck_2449_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_val_2438_);
lean_dec(v___x_2436_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2449_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; uint8_t v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2447_; 
v___x_2442_ = lean_obj_once(&l_Lean_getModuleDoc_x3f___closed__0, &l_Lean_getModuleDoc_x3f___closed__0_once, _init_l_Lean_getModuleDoc_x3f___closed__0);
v___x_2443_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v___x_2444_ = 1;
v___x_2445_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2442_, v___x_2443_, v_env_2434_, v_val_2438_, v___x_2444_);
lean_dec(v_val_2438_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2445_);
v___x_2447_ = v___x_2440_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f___boxed(lean_object* v_env_2450_, lean_object* v_moduleName_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_getModuleDoc_x3f(v_env_2450_, v_moduleName_2451_);
lean_dec(v_moduleName_2451_);
lean_dec_ref(v_env_2450_);
return v_res_2452_;
}
}
static lean_object* _init_l_Lean_getDocStringText___redArg___closed__1(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__0));
v___x_2455_ = l_Lean_stringToMessageData(v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___redArg(lean_object* v_inst_2459_, lean_object* v_inst_2460_, lean_object* v_stx_2461_){
_start:
{
lean_object* v_toApplicative_2468_; lean_object* v_toPure_2469_; lean_object* v_val_2471_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v_toApplicative_2468_ = lean_ctor_get(v_inst_2459_, 0);
v_toPure_2469_ = lean_ctor_get(v_toApplicative_2468_, 1);
v___x_2478_ = lean_unsigned_to_nat(1u);
v___x_2479_ = l_Lean_Syntax_getArg(v_stx_2461_, v___x_2478_);
switch(lean_obj_tag(v___x_2479_))
{
case 2:
{
lean_object* v_val_2480_; 
lean_inc(v_toPure_2469_);
lean_dec(v_stx_2461_);
lean_dec_ref(v_inst_2460_);
lean_dec_ref(v_inst_2459_);
v_val_2480_ = lean_ctor_get(v___x_2479_, 1);
lean_inc_ref(v_val_2480_);
lean_dec_ref_known(v___x_2479_, 2);
v_val_2471_ = v_val_2480_;
goto v___jp_2470_;
}
case 1:
{
lean_object* v_kind_2481_; 
v_kind_2481_ = lean_ctor_get(v___x_2479_, 1);
lean_inc(v_kind_2481_);
if (lean_obj_tag(v_kind_2481_) == 1)
{
lean_object* v_pre_2482_; 
v_pre_2482_ = lean_ctor_get(v_kind_2481_, 0);
lean_inc(v_pre_2482_);
if (lean_obj_tag(v_pre_2482_) == 1)
{
lean_object* v_pre_2483_; 
v_pre_2483_ = lean_ctor_get(v_pre_2482_, 0);
lean_inc(v_pre_2483_);
if (lean_obj_tag(v_pre_2483_) == 1)
{
lean_object* v_pre_2484_; 
v_pre_2484_ = lean_ctor_get(v_pre_2483_, 0);
lean_inc(v_pre_2484_);
if (lean_obj_tag(v_pre_2484_) == 1)
{
lean_object* v_pre_2485_; 
v_pre_2485_ = lean_ctor_get(v_pre_2484_, 0);
if (lean_obj_tag(v_pre_2485_) == 0)
{
lean_object* v_str_2486_; lean_object* v_str_2487_; lean_object* v_str_2488_; lean_object* v_str_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; 
v_str_2486_ = lean_ctor_get(v_kind_2481_, 1);
lean_inc_ref(v_str_2486_);
lean_dec_ref_known(v_kind_2481_, 2);
v_str_2487_ = lean_ctor_get(v_pre_2482_, 1);
lean_inc_ref(v_str_2487_);
lean_dec_ref_known(v_pre_2482_, 2);
v_str_2488_ = lean_ctor_get(v_pre_2483_, 1);
lean_inc_ref(v_str_2488_);
lean_dec_ref_known(v_pre_2483_, 2);
v_str_2489_ = lean_ctor_get(v_pre_2484_, 1);
lean_inc_ref(v_str_2489_);
lean_dec_ref_known(v_pre_2484_, 2);
v___x_2490_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_2491_ = lean_string_dec_eq(v_str_2489_, v___x_2490_);
lean_dec_ref(v_str_2489_);
if (v___x_2491_ == 0)
{
lean_dec_ref(v_str_2488_);
lean_dec_ref(v_str_2487_);
lean_dec_ref(v_str_2486_);
lean_dec_ref_known(v___x_2479_, 3);
goto v___jp_2462_;
}
else
{
lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2492_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__2));
v___x_2493_ = lean_string_dec_eq(v_str_2488_, v___x_2492_);
lean_dec_ref(v_str_2488_);
if (v___x_2493_ == 0)
{
lean_dec_ref(v_str_2487_);
lean_dec_ref(v_str_2486_);
lean_dec_ref_known(v___x_2479_, 3);
goto v___jp_2462_;
}
else
{
lean_object* v___x_2494_; uint8_t v___x_2495_; 
v___x_2494_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__3));
v___x_2495_ = lean_string_dec_eq(v_str_2487_, v___x_2494_);
lean_dec_ref(v_str_2487_);
if (v___x_2495_ == 0)
{
lean_dec_ref(v_str_2486_);
lean_dec_ref_known(v___x_2479_, 3);
goto v___jp_2462_;
}
else
{
lean_object* v___x_2496_; uint8_t v___x_2497_; 
v___x_2496_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__4));
v___x_2497_ = lean_string_dec_eq(v_str_2486_, v___x_2496_);
lean_dec_ref(v_str_2486_);
if (v___x_2497_ == 0)
{
lean_dec_ref_known(v___x_2479_, 3);
goto v___jp_2462_;
}
else
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = lean_unsigned_to_nat(0u);
v___x_2499_ = l_Lean_Syntax_getArg(v___x_2479_, v___x_2498_);
lean_dec_ref_known(v___x_2479_, 3);
if (lean_obj_tag(v___x_2499_) == 2)
{
lean_object* v_val_2500_; 
lean_inc(v_toPure_2469_);
lean_dec(v_stx_2461_);
lean_dec_ref(v_inst_2460_);
lean_dec_ref(v_inst_2459_);
v_val_2500_ = lean_ctor_get(v___x_2499_, 1);
lean_inc_ref(v_val_2500_);
lean_dec_ref_known(v___x_2499_, 2);
v_val_2471_ = v_val_2500_;
goto v___jp_2470_;
}
else
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_dec(v___x_2499_);
v___x_2501_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_2461_);
v___x_2502_ = l_Lean_MessageData_ofSyntax(v_stx_2461_);
v___x_2503_ = l_Lean_indentD(v___x_2502_);
v___x_2504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2501_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = l_Lean_throwErrorAt___redArg(v_inst_2459_, v_inst_2460_, v_stx_2461_, v___x_2504_);
return v___x_2505_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2484_, 2);
lean_dec_ref_known(v_pre_2483_, 2);
lean_dec_ref_known(v_pre_2482_, 2);
lean_dec_ref_known(v_kind_2481_, 2);
lean_dec_ref_known(v___x_2479_, 3);
goto v___jp_2462_;
}
}
else
{
lean_dec_ref_known(v_pre_2483_, 2);
lean_dec(v_pre_2484_);
lean_dec_ref_known(v_pre_2482_, 2);
lean_dec_ref_known(v_kind_2481_, 2);
lean_dec_ref_known(v___x_2479_, 3);
goto v___jp_2462_;
}
}
else
{
lean_dec_ref_known(v_pre_2482_, 2);
lean_dec(v_pre_2483_);
lean_dec_ref_known(v_kind_2481_, 2);
lean_dec_ref_known(v___x_2479_, 3);
goto v___jp_2462_;
}
}
else
{
lean_dec_ref_known(v_kind_2481_, 2);
lean_dec(v_pre_2482_);
lean_dec_ref_known(v___x_2479_, 3);
goto v___jp_2462_;
}
}
else
{
lean_dec(v_kind_2481_);
lean_dec_ref_known(v___x_2479_, 3);
goto v___jp_2462_;
}
}
default: 
{
lean_dec(v___x_2479_);
goto v___jp_2462_;
}
}
v___jp_2462_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2463_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_2461_);
v___x_2464_ = l_Lean_MessageData_ofSyntax(v_stx_2461_);
v___x_2465_ = l_Lean_indentD(v___x_2464_);
v___x_2466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2463_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = l_Lean_throwErrorAt___redArg(v_inst_2459_, v_inst_2460_, v_stx_2461_, v___x_2466_);
return v___x_2467_;
}
v___jp_2470_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2472_ = lean_unsigned_to_nat(0u);
v___x_2473_ = lean_string_utf8_byte_size(v_val_2471_);
v___x_2474_ = lean_unsigned_to_nat(2u);
v___x_2475_ = lean_nat_sub(v___x_2473_, v___x_2474_);
v___x_2476_ = lean_string_utf8_extract(v_val_2471_, v___x_2472_, v___x_2475_);
lean_dec(v___x_2475_);
lean_dec_ref(v_val_2471_);
v___x_2477_ = lean_apply_2(v_toPure_2469_, lean_box(0), v___x_2476_);
return v___x_2477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText(lean_object* v_m_2506_, lean_object* v_inst_2507_, lean_object* v_inst_2508_, lean_object* v_stx_2509_){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l_Lean_getDocStringText___redArg(v_inst_2507_, v_inst_2508_, v_stx_2509_);
return v___x_2510_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = l_Lean_instInhabitedDeclarationRange_default;
v___x_2514_ = ((lean_object*)(l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0));
v___x_2515_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
lean_ctor_set(v___x_2515_, 2, v___x_2513_);
return v___x_2515_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default(void){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = lean_obj_once(&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1, &l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1_once, _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1);
return v___x_2516_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet(void){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_VersoModuleDocs_instInhabitedSnippet_default;
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__2(lean_object* v_a_2518_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = lean_nat_to_int(v_a_2518_);
return v___x_2519_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = lean_unsigned_to_nat(2u);
v___x_2527_ = lean_nat_to_int(v___x_2526_);
return v___x_2527_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_unsigned_to_nat(1u);
v___x_2529_ = lean_nat_to_int(v___x_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(lean_object* v_x_2542_, lean_object* v_x_2543_, lean_object* v_x_2544_){
_start:
{
if (lean_obj_tag(v_x_2544_) == 0)
{
lean_dec(v_x_2542_);
return v_x_2543_;
}
else
{
lean_object* v_head_2545_; lean_object* v_tail_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2557_; 
v_head_2545_ = lean_ctor_get(v_x_2544_, 0);
v_tail_2546_ = lean_ctor_get(v_x_2544_, 1);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_x_2544_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2548_ = v_x_2544_;
v_isShared_2549_ = v_isSharedCheck_2557_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_tail_2546_);
lean_inc(v_head_2545_);
lean_dec(v_x_2544_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2557_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
lean_inc(v_x_2542_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set_tag(v___x_2548_, 5);
lean_ctor_set(v___x_2548_, 1, v_x_2542_);
lean_ctor_set(v___x_2548_, 0, v_x_2543_);
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_x_2543_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_x_2542_);
v___x_2551_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = lean_unsigned_to_nat(0u);
v___x_2553_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_2545_, v___x_2552_);
v___x_2554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2551_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v_x_2543_ = v___x_2554_;
v_x_2544_ = v_tail_2546_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(lean_object* v_x_2558_, lean_object* v_x_2559_, lean_object* v_x_2560_){
_start:
{
if (lean_obj_tag(v_x_2560_) == 0)
{
lean_dec(v_x_2558_);
return v_x_2559_;
}
else
{
lean_object* v_head_2561_; lean_object* v_tail_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2573_; 
v_head_2561_ = lean_ctor_get(v_x_2560_, 0);
v_tail_2562_ = lean_ctor_get(v_x_2560_, 1);
v_isSharedCheck_2573_ = !lean_is_exclusive(v_x_2560_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2564_ = v_x_2560_;
v_isShared_2565_ = v_isSharedCheck_2573_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_tail_2562_);
lean_inc(v_head_2561_);
lean_dec(v_x_2560_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2573_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
lean_inc(v_x_2558_);
if (v_isShared_2565_ == 0)
{
lean_ctor_set_tag(v___x_2564_, 5);
lean_ctor_set(v___x_2564_, 1, v_x_2558_);
lean_ctor_set(v___x_2564_, 0, v_x_2559_);
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_x_2559_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_x_2558_);
v___x_2567_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2568_ = lean_unsigned_to_nat(0u);
v___x_2569_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_2561_, v___x_2568_);
v___x_2570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2567_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(v_x_2558_, v___x_2570_, v_tail_2562_);
return v___x_2571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_2574_, lean_object* v_x_2575_){
_start:
{
if (lean_obj_tag(v_x_2574_) == 0)
{
lean_object* v___x_2576_; 
lean_dec(v_x_2575_);
v___x_2576_ = lean_box(0);
return v___x_2576_;
}
else
{
lean_object* v_tail_2577_; 
v_tail_2577_ = lean_ctor_get(v_x_2574_, 1);
if (lean_obj_tag(v_tail_2577_) == 0)
{
lean_object* v_head_2578_; lean_object* v___x_2579_; 
lean_dec(v_x_2575_);
v_head_2578_ = lean_ctor_get(v_x_2574_, 0);
lean_inc(v_head_2578_);
lean_dec_ref_known(v_x_2574_, 2);
v___x_2579_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2578_);
return v___x_2579_;
}
else
{
lean_object* v_head_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
lean_inc(v_tail_2577_);
v_head_2580_ = lean_ctor_get(v_x_2574_, 0);
lean_inc(v_head_2580_);
lean_dec_ref_known(v_x_2574_, 2);
v___x_2581_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_2580_);
v___x_2582_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(v_x_2575_, v___x_2581_, v_tail_2577_);
return v___x_2582_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4(void){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0));
v___x_2585_ = lean_string_length(v___x_2584_);
return v___x_2585_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5(void){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4);
v___x_2587_ = lean_nat_to_int(v___x_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_xs_2595_){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___x_2596_ = lean_array_get_size(v_xs_2595_);
v___x_2597_ = lean_unsigned_to_nat(0u);
v___x_2598_ = lean_nat_dec_eq(v___x_2596_, v___x_2597_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2599_ = lean_array_to_list(v_xs_2595_);
v___x_2600_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2601_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_2599_, v___x_2600_);
v___x_2602_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_2603_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_2604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
lean_ctor_set(v___x_2604_, 1, v___x_2601_);
v___x_2605_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2604_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
v___x_2607_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2602_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = l_Std_Format_fill(v___x_2607_);
return v___x_2608_;
}
else
{
lean_object* v___x_2609_; 
lean_dec_ref(v_xs_2595_);
v___x_2609_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_2609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_2664_, lean_object* v_prec_2665_){
_start:
{
switch(lean_obj_tag(v_x_2664_))
{
case 0:
{
lean_object* v_string_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2686_; 
v_string_2666_ = lean_ctor_get(v_x_2664_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_x_2664_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2668_ = v_x_2664_;
v_isShared_2669_ = v_isSharedCheck_2686_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_string_2666_);
lean_dec(v_x_2664_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2686_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___y_2671_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v___x_2682_ = lean_unsigned_to_nat(1024u);
v___x_2683_ = lean_nat_dec_le(v___x_2682_, v_prec_2665_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; 
v___x_2684_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2671_ = v___x_2684_;
goto v___jp_2670_;
}
else
{
lean_object* v___x_2685_; 
v___x_2685_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2671_ = v___x_2685_;
goto v___jp_2670_;
}
v___jp_2670_:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2672_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__2));
v___x_2673_ = l_String_quote(v_string_2666_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set_tag(v___x_2668_, 3);
lean_ctor_set(v___x_2668_, 0, v___x_2673_);
v___x_2675_ = v___x_2668_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2672_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
lean_inc(v___y_2671_);
v___x_2677_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___y_2671_);
lean_ctor_set(v___x_2677_, 1, v___x_2676_);
v___x_2678_ = 0;
v___x_2679_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2679_, 0, v___x_2677_);
lean_ctor_set_uint8(v___x_2679_, sizeof(void*)*1, v___x_2678_);
v___x_2680_ = l_Repr_addAppParen(v___x_2679_, v_prec_2665_);
return v___x_2680_;
}
}
}
}
case 1:
{
lean_object* v_content_2687_; lean_object* v___y_2689_; lean_object* v___x_2697_; uint8_t v___x_2698_; 
v_content_2687_ = lean_ctor_get(v_x_2664_, 0);
lean_inc_ref(v_content_2687_);
lean_dec_ref_known(v_x_2664_, 1);
v___x_2697_ = lean_unsigned_to_nat(1024u);
v___x_2698_ = lean_nat_dec_le(v___x_2697_, v_prec_2665_);
if (v___x_2698_ == 0)
{
lean_object* v___x_2699_; 
v___x_2699_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2689_ = v___x_2699_;
goto v___jp_2688_;
}
else
{
lean_object* v___x_2700_; 
v___x_2700_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2689_ = v___x_2700_;
goto v___jp_2688_;
}
v___jp_2688_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2690_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__7));
v___x_2691_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2687_);
v___x_2692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2690_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
lean_inc(v___y_2689_);
v___x_2693_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___y_2689_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = 0;
v___x_2695_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set_uint8(v___x_2695_, sizeof(void*)*1, v___x_2694_);
v___x_2696_ = l_Repr_addAppParen(v___x_2695_, v_prec_2665_);
return v___x_2696_;
}
}
case 2:
{
lean_object* v_content_2701_; lean_object* v___y_2703_; lean_object* v___x_2711_; uint8_t v___x_2712_; 
v_content_2701_ = lean_ctor_get(v_x_2664_, 0);
lean_inc_ref(v_content_2701_);
lean_dec_ref_known(v_x_2664_, 1);
v___x_2711_ = lean_unsigned_to_nat(1024u);
v___x_2712_ = lean_nat_dec_le(v___x_2711_, v_prec_2665_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; 
v___x_2713_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2703_ = v___x_2713_;
goto v___jp_2702_;
}
else
{
lean_object* v___x_2714_; 
v___x_2714_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2703_ = v___x_2714_;
goto v___jp_2702_;
}
v___jp_2702_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2704_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__10));
v___x_2705_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2701_);
v___x_2706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2704_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
lean_inc(v___y_2703_);
v___x_2707_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___y_2703_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = 0;
v___x_2709_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set_uint8(v___x_2709_, sizeof(void*)*1, v___x_2708_);
v___x_2710_ = l_Repr_addAppParen(v___x_2709_, v_prec_2665_);
return v___x_2710_;
}
}
case 3:
{
lean_object* v_string_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2735_; 
v_string_2715_ = lean_ctor_get(v_x_2664_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_x_2664_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2717_ = v_x_2664_;
v_isShared_2718_ = v_isSharedCheck_2735_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_string_2715_);
lean_dec(v_x_2664_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2735_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___y_2720_; lean_object* v___x_2731_; uint8_t v___x_2732_; 
v___x_2731_ = lean_unsigned_to_nat(1024u);
v___x_2732_ = lean_nat_dec_le(v___x_2731_, v_prec_2665_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; 
v___x_2733_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2720_ = v___x_2733_;
goto v___jp_2719_;
}
else
{
lean_object* v___x_2734_; 
v___x_2734_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2720_ = v___x_2734_;
goto v___jp_2719_;
}
v___jp_2719_:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2721_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__13));
v___x_2722_ = l_String_quote(v_string_2715_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 0, v___x_2722_);
v___x_2724_ = v___x_2717_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; uint8_t v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2721_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
lean_inc(v___y_2720_);
v___x_2726_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___y_2720_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = 0;
v___x_2728_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2728_, 0, v___x_2726_);
lean_ctor_set_uint8(v___x_2728_, sizeof(void*)*1, v___x_2727_);
v___x_2729_ = l_Repr_addAppParen(v___x_2728_, v_prec_2665_);
return v___x_2729_;
}
}
}
}
case 4:
{
uint8_t v_mode_2736_; lean_object* v_string_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2762_; 
v_mode_2736_ = lean_ctor_get_uint8(v_x_2664_, sizeof(void*)*1);
v_string_2737_ = lean_ctor_get(v_x_2664_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_x_2664_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2739_ = v_x_2664_;
v_isShared_2740_ = v_isSharedCheck_2762_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_string_2737_);
lean_dec(v_x_2664_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2762_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___y_2742_; lean_object* v___x_2758_; uint8_t v___x_2759_; 
v___x_2758_ = lean_unsigned_to_nat(1024u);
v___x_2759_ = lean_nat_dec_le(v___x_2758_, v_prec_2665_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2760_; 
v___x_2760_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2742_ = v___x_2760_;
goto v___jp_2741_;
}
else
{
lean_object* v___x_2761_; 
v___x_2761_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2742_ = v___x_2761_;
goto v___jp_2741_;
}
v___jp_2741_:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; lean_object* v___x_2755_; 
v___x_2743_ = lean_box(1);
v___x_2744_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__16));
v___x_2745_ = lean_unsigned_to_nat(1024u);
v___x_2746_ = l_Lean_Doc_instReprMathMode_repr(v_mode_2736_, v___x_2745_);
v___x_2747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2744_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
lean_ctor_set(v___x_2748_, 1, v___x_2743_);
v___x_2749_ = l_String_quote(v_string_2737_);
v___x_2750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
v___x_2751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2748_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
lean_inc(v___y_2742_);
v___x_2752_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___y_2742_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = 0;
if (v_isShared_2740_ == 0)
{
lean_ctor_set_tag(v___x_2739_, 6);
lean_ctor_set(v___x_2739_, 0, v___x_2752_);
v___x_2755_ = v___x_2739_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2752_);
v___x_2755_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___x_2756_; 
lean_ctor_set_uint8(v___x_2755_, sizeof(void*)*1, v___x_2753_);
v___x_2756_ = l_Repr_addAppParen(v___x_2755_, v_prec_2665_);
return v___x_2756_;
}
}
}
}
case 5:
{
lean_object* v_string_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2783_; 
v_string_2763_ = lean_ctor_get(v_x_2664_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_x_2664_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2765_ = v_x_2664_;
v_isShared_2766_ = v_isSharedCheck_2783_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_string_2763_);
lean_dec(v_x_2664_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2783_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___y_2768_; lean_object* v___x_2779_; uint8_t v___x_2780_; 
v___x_2779_ = lean_unsigned_to_nat(1024u);
v___x_2780_ = lean_nat_dec_le(v___x_2779_, v_prec_2665_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2781_; 
v___x_2781_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2768_ = v___x_2781_;
goto v___jp_2767_;
}
else
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2768_ = v___x_2782_;
goto v___jp_2767_;
}
v___jp_2767_:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2769_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__19));
v___x_2770_ = l_String_quote(v_string_2763_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set_tag(v___x_2765_, 3);
lean_ctor_set(v___x_2765_, 0, v___x_2770_);
v___x_2772_ = v___x_2765_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2769_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
lean_inc(v___y_2768_);
v___x_2774_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___y_2768_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
v___x_2775_ = 0;
v___x_2776_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2776_, 0, v___x_2774_);
lean_ctor_set_uint8(v___x_2776_, sizeof(void*)*1, v___x_2775_);
v___x_2777_ = l_Repr_addAppParen(v___x_2776_, v_prec_2665_);
return v___x_2777_;
}
}
}
}
case 6:
{
lean_object* v_content_2784_; lean_object* v_url_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2809_; 
v_content_2784_ = lean_ctor_get(v_x_2664_, 0);
v_url_2785_ = lean_ctor_get(v_x_2664_, 1);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_x_2664_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2787_ = v_x_2664_;
v_isShared_2788_ = v_isSharedCheck_2809_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_url_2785_);
lean_inc(v_content_2784_);
lean_dec(v_x_2664_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2809_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___y_2790_; lean_object* v___x_2805_; uint8_t v___x_2806_; 
v___x_2805_ = lean_unsigned_to_nat(1024u);
v___x_2806_ = lean_nat_dec_le(v___x_2805_, v_prec_2665_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2807_; 
v___x_2807_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2790_ = v___x_2807_;
goto v___jp_2789_;
}
else
{
lean_object* v___x_2808_; 
v___x_2808_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2790_ = v___x_2808_;
goto v___jp_2789_;
}
v___jp_2789_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2791_ = lean_box(1);
v___x_2792_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__22));
v___x_2793_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2784_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set_tag(v___x_2787_, 5);
lean_ctor_set(v___x_2787_, 1, v___x_2793_);
lean_ctor_set(v___x_2787_, 0, v___x_2792_);
v___x_2795_ = v___x_2787_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
lean_ctor_set(v___x_2796_, 1, v___x_2791_);
v___x_2797_ = l_String_quote(v_url_2785_);
v___x_2798_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
v___x_2799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2796_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
lean_inc(v___y_2790_);
v___x_2800_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___y_2790_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = 0;
v___x_2802_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2802_, 0, v___x_2800_);
lean_ctor_set_uint8(v___x_2802_, sizeof(void*)*1, v___x_2801_);
v___x_2803_ = l_Repr_addAppParen(v___x_2802_, v_prec_2665_);
return v___x_2803_;
}
}
}
}
case 7:
{
lean_object* v_name_2810_; lean_object* v_content_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2835_; 
v_name_2810_ = lean_ctor_get(v_x_2664_, 0);
v_content_2811_ = lean_ctor_get(v_x_2664_, 1);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_x_2664_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2813_ = v_x_2664_;
v_isShared_2814_ = v_isSharedCheck_2835_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_content_2811_);
lean_inc(v_name_2810_);
lean_dec(v_x_2664_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2835_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___y_2816_; lean_object* v___x_2831_; uint8_t v___x_2832_; 
v___x_2831_ = lean_unsigned_to_nat(1024u);
v___x_2832_ = lean_nat_dec_le(v___x_2831_, v_prec_2665_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; 
v___x_2833_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2816_ = v___x_2833_;
goto v___jp_2815_;
}
else
{
lean_object* v___x_2834_; 
v___x_2834_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2816_ = v___x_2834_;
goto v___jp_2815_;
}
v___jp_2815_:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2822_; 
v___x_2817_ = lean_box(1);
v___x_2818_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__25));
v___x_2819_ = l_String_quote(v_name_2810_);
v___x_2820_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2819_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set_tag(v___x_2813_, 5);
lean_ctor_set(v___x_2813_, 1, v___x_2820_);
lean_ctor_set(v___x_2813_, 0, v___x_2818_);
v___x_2822_ = v___x_2813_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2818_);
lean_ctor_set(v_reuseFailAlloc_2830_, 1, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
lean_ctor_set(v___x_2823_, 1, v___x_2817_);
v___x_2824_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2811_);
v___x_2825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2823_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
lean_inc(v___y_2816_);
v___x_2826_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___y_2816_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = 0;
v___x_2828_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2828_, 0, v___x_2826_);
lean_ctor_set_uint8(v___x_2828_, sizeof(void*)*1, v___x_2827_);
v___x_2829_ = l_Repr_addAppParen(v___x_2828_, v_prec_2665_);
return v___x_2829_;
}
}
}
}
case 8:
{
lean_object* v_alt_2836_; lean_object* v_url_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2862_; 
v_alt_2836_ = lean_ctor_get(v_x_2664_, 0);
v_url_2837_ = lean_ctor_get(v_x_2664_, 1);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_x_2664_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2839_ = v_x_2664_;
v_isShared_2840_ = v_isSharedCheck_2862_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_url_2837_);
lean_inc(v_alt_2836_);
lean_dec(v_x_2664_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2862_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___y_2842_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2858_ = lean_unsigned_to_nat(1024u);
v___x_2859_ = lean_nat_dec_le(v___x_2858_, v_prec_2665_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; 
v___x_2860_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2842_ = v___x_2860_;
goto v___jp_2841_;
}
else
{
lean_object* v___x_2861_; 
v___x_2861_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2842_ = v___x_2861_;
goto v___jp_2841_;
}
v___jp_2841_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2848_; 
v___x_2843_ = lean_box(1);
v___x_2844_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__28));
v___x_2845_ = l_String_quote(v_alt_2836_);
v___x_2846_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set_tag(v___x_2839_, 5);
lean_ctor_set(v___x_2839_, 1, v___x_2846_);
lean_ctor_set(v___x_2839_, 0, v___x_2844_);
v___x_2848_ = v___x_2839_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2844_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v___x_2846_);
v___x_2848_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2849_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
lean_ctor_set(v___x_2849_, 1, v___x_2843_);
v___x_2850_ = l_String_quote(v_url_2837_);
v___x_2851_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
v___x_2852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2849_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
lean_inc(v___y_2842_);
v___x_2853_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___y_2842_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
v___x_2854_ = 0;
v___x_2855_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2855_, 0, v___x_2853_);
lean_ctor_set_uint8(v___x_2855_, sizeof(void*)*1, v___x_2854_);
v___x_2856_ = l_Repr_addAppParen(v___x_2855_, v_prec_2665_);
return v___x_2856_;
}
}
}
}
case 9:
{
lean_object* v_content_2863_; lean_object* v___y_2865_; lean_object* v___x_2873_; uint8_t v___x_2874_; 
v_content_2863_ = lean_ctor_get(v_x_2664_, 0);
lean_inc_ref(v_content_2863_);
lean_dec_ref_known(v_x_2664_, 1);
v___x_2873_ = lean_unsigned_to_nat(1024u);
v___x_2874_ = lean_nat_dec_le(v___x_2873_, v_prec_2665_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; 
v___x_2875_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2865_ = v___x_2875_;
goto v___jp_2864_;
}
else
{
lean_object* v___x_2876_; 
v___x_2876_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2865_ = v___x_2876_;
goto v___jp_2864_;
}
v___jp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2866_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__31));
v___x_2867_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2863_);
v___x_2868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
lean_inc(v___y_2865_);
v___x_2869_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___y_2865_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v___x_2870_ = 0;
v___x_2871_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2871_, 0, v___x_2869_);
lean_ctor_set_uint8(v___x_2871_, sizeof(void*)*1, v___x_2870_);
v___x_2872_ = l_Repr_addAppParen(v___x_2871_, v_prec_2665_);
return v___x_2872_;
}
}
default: 
{
lean_object* v_container_2877_; lean_object* v_content_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2926_; 
v_container_2877_ = lean_ctor_get(v_x_2664_, 0);
v_content_2878_ = lean_ctor_get(v_x_2664_, 1);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_x_2664_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2880_ = v_x_2664_;
v_isShared_2881_ = v_isSharedCheck_2926_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_content_2878_);
lean_inc(v_container_2877_);
lean_dec(v_x_2664_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2926_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___y_2883_; lean_object* v___x_2922_; uint8_t v___x_2923_; 
v___x_2922_ = lean_unsigned_to_nat(1024u);
v___x_2923_ = lean_nat_dec_le(v___x_2922_, v_prec_2665_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; 
v___x_2924_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2883_ = v___x_2924_;
goto v___jp_2882_;
}
else
{
lean_object* v___x_2925_; 
v___x_2925_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2883_ = v___x_2925_;
goto v___jp_2882_;
}
v___jp_2882_:
{
lean_object* v_name_2884_; lean_object* v_val_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2921_; 
v_name_2884_ = lean_ctor_get(v_container_2877_, 0);
v_val_2885_ = lean_ctor_get(v_container_2877_, 1);
v_isSharedCheck_2921_ = !lean_is_exclusive(v_container_2877_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2887_ = v_container_2877_;
v_isShared_2888_ = v_isSharedCheck_2921_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_val_2885_);
lean_inc(v_name_2884_);
lean_dec(v_container_2877_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2921_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2895_; 
v___x_2889_ = lean_box(1);
v___x_2890_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__34));
v___x_2891_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_2892_ = lean_unsigned_to_nat(0u);
v___x_2893_ = l_Lean_Name_reprPrec(v_name_2884_, v___x_2892_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set_tag(v___x_2887_, 5);
lean_ctor_set(v___x_2887_, 1, v___x_2893_);
lean_ctor_set(v___x_2887_, 0, v___x_2891_);
v___x_2895_ = v___x_2887_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2891_);
lean_ctor_set(v_reuseFailAlloc_2920_, 1, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; uint8_t v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2896_ = l_Std_Format_nestD(v___x_2895_);
v___x_2897_ = 0;
v___x_2898_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2898_, 0, v___x_2896_);
lean_ctor_set_uint8(v___x_2898_, sizeof(void*)*1, v___x_2897_);
if (v_isShared_2881_ == 0)
{
lean_ctor_set_tag(v___x_2880_, 5);
lean_ctor_set(v___x_2880_, 1, v___x_2889_);
lean_ctor_set(v___x_2880_, 0, v___x_2898_);
v___x_2900_ = v___x_2880_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v___x_2889_);
v___x_2900_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2901_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_2902_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_2885_);
lean_dec(v_val_2885_);
v___x_2903_ = l_Lean_Name_reprPrec(v___x_2902_, v___x_2892_);
v___x_2904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2901_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
v___x_2905_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_2906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2904_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = l_Std_Format_nestD(v___x_2906_);
v___x_2908_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
lean_ctor_set_uint8(v___x_2908_, sizeof(void*)*1, v___x_2897_);
v___x_2909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2900_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
v___x_2910_ = l_Std_Format_nestD(v___x_2909_);
v___x_2911_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
lean_ctor_set_uint8(v___x_2911_, sizeof(void*)*1, v___x_2897_);
v___x_2912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2890_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
lean_ctor_set(v___x_2913_, 1, v___x_2889_);
v___x_2914_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2878_);
v___x_2915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2913_);
lean_ctor_set(v___x_2915_, 1, v___x_2914_);
lean_inc(v___y_2883_);
v___x_2916_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2916_, 0, v___y_2883_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
v___x_2917_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
lean_ctor_set_uint8(v___x_2917_, sizeof(void*)*1, v___x_2897_);
v___x_2918_ = l_Repr_addAppParen(v___x_2917_, v_prec_2665_);
return v___x_2918_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2928_ = lean_unsigned_to_nat(0u);
v___x_2929_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v___y_2927_, v___x_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_2930_, lean_object* v_prec_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_x_2930_, v_prec_2931_);
lean_dec(v_prec_2931_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(lean_object* v_xs_2933_){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; 
v___x_2934_ = lean_array_get_size(v_xs_2933_);
v___x_2935_ = lean_unsigned_to_nat(0u);
v___x_2936_ = lean_nat_dec_eq(v___x_2934_, v___x_2935_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2937_ = lean_array_to_list(v_xs_2933_);
v___x_2938_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2939_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_2937_, v___x_2938_);
v___x_2940_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_2941_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_2942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v___x_2939_);
v___x_2943_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2942_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
v___x_2945_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2940_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
v___x_2946_ = l_Std_Format_fill(v___x_2945_);
return v___x_2946_;
}
else
{
lean_object* v___x_2947_; 
lean_dec_ref(v_xs_2933_);
v___x_2947_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_2947_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = lean_unsigned_to_nat(12u);
v___x_2979_ = lean_nat_to_int(v___x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(lean_object* v_x_2980_, lean_object* v_x_2981_, lean_object* v_x_2982_){
_start:
{
if (lean_obj_tag(v_x_2982_) == 0)
{
lean_dec(v_x_2980_);
return v_x_2981_;
}
else
{
lean_object* v_head_2983_; lean_object* v_tail_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2995_; 
v_head_2983_ = lean_ctor_get(v_x_2982_, 0);
v_tail_2984_ = lean_ctor_get(v_x_2982_, 1);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_x_2982_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2986_ = v_x_2982_;
v_isShared_2987_ = v_isSharedCheck_2995_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_tail_2984_);
lean_inc(v_head_2983_);
lean_dec(v_x_2982_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2995_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
lean_inc(v_x_2980_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set_tag(v___x_2986_, 5);
lean_ctor_set(v___x_2986_, 1, v_x_2980_);
lean_ctor_set(v___x_2986_, 0, v_x_2981_);
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_x_2981_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_x_2980_);
v___x_2989_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2990_ = lean_unsigned_to_nat(0u);
v___x_2991_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_2983_, v___x_2990_);
v___x_2992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2989_);
lean_ctor_set(v___x_2992_, 1, v___x_2991_);
v_x_2981_ = v___x_2992_;
v_x_2982_ = v_tail_2984_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(lean_object* v_x_2996_, lean_object* v_x_2997_, lean_object* v_x_2998_){
_start:
{
if (lean_obj_tag(v_x_2998_) == 0)
{
lean_dec(v_x_2996_);
return v_x_2997_;
}
else
{
lean_object* v_head_2999_; lean_object* v_tail_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3011_; 
v_head_2999_ = lean_ctor_get(v_x_2998_, 0);
v_tail_3000_ = lean_ctor_get(v_x_2998_, 1);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_x_2998_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3002_ = v_x_2998_;
v_isShared_3003_ = v_isSharedCheck_3011_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_tail_3000_);
lean_inc(v_head_2999_);
lean_dec(v_x_2998_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3011_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
lean_inc(v_x_2996_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set_tag(v___x_3002_, 5);
lean_ctor_set(v___x_3002_, 1, v_x_2996_);
lean_ctor_set(v___x_3002_, 0, v_x_2997_);
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_x_2997_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v_x_2996_);
v___x_3005_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3006_ = lean_unsigned_to_nat(0u);
v___x_3007_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_2999_, v___x_3006_);
v___x_3008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3005_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(v_x_2996_, v___x_3008_, v_tail_3000_);
return v___x_3009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(lean_object* v_x_3012_, lean_object* v_x_3013_){
_start:
{
if (lean_obj_tag(v_x_3012_) == 0)
{
lean_object* v___x_3014_; 
lean_dec(v_x_3013_);
v___x_3014_ = lean_box(0);
return v___x_3014_;
}
else
{
lean_object* v_tail_3015_; 
v_tail_3015_ = lean_ctor_get(v_x_3012_, 1);
if (lean_obj_tag(v_tail_3015_) == 0)
{
lean_object* v_head_3016_; lean_object* v___x_3017_; 
lean_dec(v_x_3013_);
v_head_3016_ = lean_ctor_get(v_x_3012_, 0);
lean_inc(v_head_3016_);
lean_dec_ref_known(v_x_3012_, 2);
v___x_3017_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_3016_);
return v___x_3017_;
}
else
{
lean_object* v_head_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
lean_inc(v_tail_3015_);
v_head_3018_ = lean_ctor_get(v_x_3012_, 0);
lean_inc(v_head_3018_);
lean_dec_ref_known(v_x_3012_, 2);
v___x_3019_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_3018_);
v___x_3020_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(v_x_3013_, v___x_3019_, v_tail_3015_);
return v___x_3020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(lean_object* v_xs_3021_){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; uint8_t v___x_3024_; 
v___x_3022_ = lean_array_get_size(v_xs_3021_);
v___x_3023_ = lean_unsigned_to_nat(0u);
v___x_3024_ = lean_nat_dec_eq(v___x_3022_, v___x_3023_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3025_ = lean_array_to_list(v_xs_3021_);
v___x_3026_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3027_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_3025_, v___x_3026_);
v___x_3028_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3029_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
lean_ctor_set(v___x_3030_, 1, v___x_3027_);
v___x_3031_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3030_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3028_);
lean_ctor_set(v___x_3033_, 1, v___x_3032_);
v___x_3034_ = l_Std_Format_fill(v___x_3033_);
return v___x_3034_;
}
else
{
lean_object* v___x_3035_; 
lean_dec_ref(v_xs_3021_);
v___x_3035_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3035_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0));
v___x_3038_ = lean_string_length(v___x_3037_);
return v___x_3038_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10(void){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9);
v___x_3040_ = lean_nat_to_int(v___x_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_x_3046_){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3047_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__6));
v___x_3048_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3049_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_x_3046_);
v___x_3050_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3048_);
lean_ctor_set(v___x_3050_, 1, v___x_3049_);
v___x_3051_ = 0;
v___x_3052_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3052_, 0, v___x_3050_);
lean_ctor_set_uint8(v___x_3052_, sizeof(void*)*1, v___x_3051_);
v___x_3053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3047_);
lean_ctor_set(v___x_3053_, 1, v___x_3052_);
v___x_3054_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3055_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
lean_ctor_set(v___x_3056_, 1, v___x_3053_);
v___x_3057_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3056_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
v___x_3059_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3054_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
v___x_3060_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3060_, 0, v___x_3059_);
lean_ctor_set_uint8(v___x_3060_, sizeof(void*)*1, v___x_3051_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(lean_object* v_x_3061_, lean_object* v_x_3062_, lean_object* v_x_3063_){
_start:
{
if (lean_obj_tag(v_x_3063_) == 0)
{
lean_dec(v_x_3061_);
return v_x_3062_;
}
else
{
lean_object* v_head_3064_; lean_object* v_tail_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3075_; 
v_head_3064_ = lean_ctor_get(v_x_3063_, 0);
v_tail_3065_ = lean_ctor_get(v_x_3063_, 1);
v_isSharedCheck_3075_ = !lean_is_exclusive(v_x_3063_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3067_ = v_x_3063_;
v_isShared_3068_ = v_isSharedCheck_3075_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_tail_3065_);
lean_inc(v_head_3064_);
lean_dec(v_x_3063_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3075_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
lean_inc(v_x_3061_);
if (v_isShared_3068_ == 0)
{
lean_ctor_set_tag(v___x_3067_, 5);
lean_ctor_set(v___x_3067_, 1, v_x_3061_);
lean_ctor_set(v___x_3067_, 0, v_x_3062_);
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_x_3062_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_x_3061_);
v___x_3070_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3064_);
v___x_3072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3070_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
v_x_3062_ = v___x_3072_;
v_x_3063_ = v_tail_3065_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(lean_object* v_x_3076_, lean_object* v_x_3077_, lean_object* v_x_3078_){
_start:
{
if (lean_obj_tag(v_x_3078_) == 0)
{
lean_dec(v_x_3076_);
return v_x_3077_;
}
else
{
lean_object* v_head_3079_; lean_object* v_tail_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3090_; 
v_head_3079_ = lean_ctor_get(v_x_3078_, 0);
v_tail_3080_ = lean_ctor_get(v_x_3078_, 1);
v_isSharedCheck_3090_ = !lean_is_exclusive(v_x_3078_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3082_ = v_x_3078_;
v_isShared_3083_ = v_isSharedCheck_3090_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_tail_3080_);
lean_inc(v_head_3079_);
lean_dec(v_x_3078_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3090_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
lean_inc(v_x_3076_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set_tag(v___x_3082_, 5);
lean_ctor_set(v___x_3082_, 1, v_x_3076_);
lean_ctor_set(v___x_3082_, 0, v_x_3077_);
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_x_3077_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_x_3076_);
v___x_3085_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3079_);
v___x_3087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3085_);
lean_ctor_set(v___x_3087_, 1, v___x_3086_);
v___x_3088_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(v_x_3076_, v___x_3087_, v_tail_3080_);
return v___x_3088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(lean_object* v_x_3091_, lean_object* v_x_3092_){
_start:
{
if (lean_obj_tag(v_x_3091_) == 0)
{
lean_object* v___x_3093_; 
lean_dec(v_x_3092_);
v___x_3093_ = lean_box(0);
return v___x_3093_;
}
else
{
lean_object* v_tail_3094_; 
v_tail_3094_ = lean_ctor_get(v_x_3091_, 1);
if (lean_obj_tag(v_tail_3094_) == 0)
{
lean_object* v_head_3095_; lean_object* v___x_3096_; 
lean_dec(v_x_3092_);
v_head_3095_ = lean_ctor_get(v_x_3091_, 0);
lean_inc(v_head_3095_);
lean_dec_ref_known(v_x_3091_, 2);
v___x_3096_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3095_);
return v___x_3096_;
}
else
{
lean_object* v_head_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_inc(v_tail_3094_);
v_head_3097_ = lean_ctor_get(v_x_3091_, 0);
lean_inc(v_head_3097_);
lean_dec_ref_known(v_x_3091_, 2);
v___x_3098_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_3097_);
v___x_3099_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(v_x_3092_, v___x_3098_, v_tail_3094_);
return v___x_3099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(lean_object* v_xs_3100_){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___x_3101_ = lean_array_get_size(v_xs_3100_);
v___x_3102_ = lean_unsigned_to_nat(0u);
v___x_3103_ = lean_nat_dec_eq(v___x_3101_, v___x_3102_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3104_ = lean_array_to_list(v_xs_3100_);
v___x_3105_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3106_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(v___x_3104_, v___x_3105_);
v___x_3107_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3108_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
lean_ctor_set(v___x_3109_, 1, v___x_3106_);
v___x_3110_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3109_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
v___x_3112_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3107_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
v___x_3113_ = l_Std_Format_fill(v___x_3112_);
return v___x_3113_;
}
else
{
lean_object* v___x_3114_; 
lean_dec_ref(v_xs_3100_);
v___x_3114_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3114_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = lean_unsigned_to_nat(0u);
v___x_3122_ = lean_nat_to_int(v___x_3121_);
return v___x_3122_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3138_ = lean_unsigned_to_nat(8u);
v___x_3139_ = lean_nat_to_int(v___x_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_x_3143_){
_start:
{
lean_object* v_term_3144_; lean_object* v_desc_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3177_; 
v_term_3144_ = lean_ctor_get(v_x_3143_, 0);
v_desc_3145_ = lean_ctor_get(v_x_3143_, 1);
v_isSharedCheck_3177_ = !lean_is_exclusive(v_x_3143_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3147_ = v_x_3143_;
v_isShared_3148_ = v_isSharedCheck_3177_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_desc_3145_);
lean_inc(v_term_3144_);
lean_dec(v_x_3143_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3177_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3154_; 
v___x_3149_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3150_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__3));
v___x_3151_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_3152_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_term_3144_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set_tag(v___x_3147_, 4);
lean_ctor_set(v___x_3147_, 1, v___x_3152_);
lean_ctor_set(v___x_3147_, 0, v___x_3151_);
v___x_3154_ = v___x_3147_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3151_);
lean_ctor_set(v_reuseFailAlloc_3176_, 1, v___x_3152_);
v___x_3154_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
uint8_t v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3155_ = 0;
v___x_3156_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3156_, 0, v___x_3154_);
lean_ctor_set_uint8(v___x_3156_, sizeof(void*)*1, v___x_3155_);
v___x_3157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3150_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
v___x_3158_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3157_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = lean_box(1);
v___x_3161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3159_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__6));
v___x_3163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3161_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
lean_ctor_set(v___x_3164_, 1, v___x_3149_);
v___x_3165_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_desc_3145_);
v___x_3166_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3151_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
v___x_3167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
lean_ctor_set_uint8(v___x_3167_, sizeof(void*)*1, v___x_3155_);
v___x_3168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3164_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
v___x_3169_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3170_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
lean_ctor_set(v___x_3171_, 1, v___x_3168_);
v___x_3172_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3171_);
lean_ctor_set(v___x_3173_, 1, v___x_3172_);
v___x_3174_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3169_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
v___x_3175_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3175_, 0, v___x_3174_);
lean_ctor_set_uint8(v___x_3175_, sizeof(void*)*1, v___x_3155_);
return v___x_3175_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(lean_object* v_x_3178_, lean_object* v_x_3179_, lean_object* v_x_3180_){
_start:
{
if (lean_obj_tag(v_x_3180_) == 0)
{
lean_dec(v_x_3178_);
return v_x_3179_;
}
else
{
lean_object* v_head_3181_; lean_object* v_tail_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3192_; 
v_head_3181_ = lean_ctor_get(v_x_3180_, 0);
v_tail_3182_ = lean_ctor_get(v_x_3180_, 1);
v_isSharedCheck_3192_ = !lean_is_exclusive(v_x_3180_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3184_ = v_x_3180_;
v_isShared_3185_ = v_isSharedCheck_3192_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_tail_3182_);
lean_inc(v_head_3181_);
lean_dec(v_x_3180_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3192_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
lean_inc(v_x_3178_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set_tag(v___x_3184_, 5);
lean_ctor_set(v___x_3184_, 1, v_x_3178_);
lean_ctor_set(v___x_3184_, 0, v_x_3179_);
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_x_3179_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v_x_3178_);
v___x_3187_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3181_);
v___x_3189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3187_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
v_x_3179_ = v___x_3189_;
v_x_3180_ = v_tail_3182_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(lean_object* v_x_3193_, lean_object* v_x_3194_, lean_object* v_x_3195_){
_start:
{
if (lean_obj_tag(v_x_3195_) == 0)
{
lean_dec(v_x_3193_);
return v_x_3194_;
}
else
{
lean_object* v_head_3196_; lean_object* v_tail_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3207_; 
v_head_3196_ = lean_ctor_get(v_x_3195_, 0);
v_tail_3197_ = lean_ctor_get(v_x_3195_, 1);
v_isSharedCheck_3207_ = !lean_is_exclusive(v_x_3195_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3199_ = v_x_3195_;
v_isShared_3200_ = v_isSharedCheck_3207_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_tail_3197_);
lean_inc(v_head_3196_);
lean_dec(v_x_3195_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3207_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
lean_inc(v_x_3193_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set_tag(v___x_3199_, 5);
lean_ctor_set(v___x_3199_, 1, v_x_3193_);
lean_ctor_set(v___x_3199_, 0, v_x_3194_);
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_x_3194_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_x_3193_);
v___x_3202_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3203_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3196_);
v___x_3204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3202_);
lean_ctor_set(v___x_3204_, 1, v___x_3203_);
v___x_3205_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(v_x_3193_, v___x_3204_, v_tail_3197_);
return v___x_3205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(lean_object* v_x_3208_, lean_object* v_x_3209_){
_start:
{
if (lean_obj_tag(v_x_3208_) == 0)
{
lean_object* v___x_3210_; 
lean_dec(v_x_3209_);
v___x_3210_ = lean_box(0);
return v___x_3210_;
}
else
{
lean_object* v_tail_3211_; 
v_tail_3211_ = lean_ctor_get(v_x_3208_, 1);
if (lean_obj_tag(v_tail_3211_) == 0)
{
lean_object* v_head_3212_; lean_object* v___x_3213_; 
lean_dec(v_x_3209_);
v_head_3212_ = lean_ctor_get(v_x_3208_, 0);
lean_inc(v_head_3212_);
lean_dec_ref_known(v_x_3208_, 2);
v___x_3213_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3212_);
return v___x_3213_;
}
else
{
lean_object* v_head_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
lean_inc(v_tail_3211_);
v_head_3214_ = lean_ctor_get(v_x_3208_, 0);
lean_inc(v_head_3214_);
lean_dec_ref_known(v_x_3208_, 2);
v___x_3215_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_3214_);
v___x_3216_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(v_x_3209_, v___x_3215_, v_tail_3211_);
return v___x_3216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(lean_object* v_xs_3217_){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; uint8_t v___x_3220_; 
v___x_3218_ = lean_array_get_size(v_xs_3217_);
v___x_3219_ = lean_unsigned_to_nat(0u);
v___x_3220_ = lean_nat_dec_eq(v___x_3218_, v___x_3219_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3221_ = lean_array_to_list(v_xs_3217_);
v___x_3222_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3223_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(v___x_3221_, v___x_3222_);
v___x_3224_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3225_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
lean_ctor_set(v___x_3226_, 1, v___x_3223_);
v___x_3227_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3226_);
lean_ctor_set(v___x_3228_, 1, v___x_3227_);
v___x_3229_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3224_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
v___x_3230_ = l_Std_Format_fill(v___x_3229_);
return v___x_3230_;
}
else
{
lean_object* v___x_3231_; 
lean_dec_ref(v_xs_3217_);
v___x_3231_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(lean_object* v_x_3250_, lean_object* v_prec_3251_){
_start:
{
switch(lean_obj_tag(v_x_3250_))
{
case 0:
{
lean_object* v_contents_3252_; lean_object* v___y_3254_; lean_object* v___x_3262_; uint8_t v___x_3263_; 
v_contents_3252_ = lean_ctor_get(v_x_3250_, 0);
lean_inc_ref(v_contents_3252_);
lean_dec_ref_known(v_x_3250_, 1);
v___x_3262_ = lean_unsigned_to_nat(1024u);
v___x_3263_ = lean_nat_dec_le(v___x_3262_, v_prec_3251_);
if (v___x_3263_ == 0)
{
lean_object* v___x_3264_; 
v___x_3264_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3254_ = v___x_3264_;
goto v___jp_3253_;
}
else
{
lean_object* v___x_3265_; 
v___x_3265_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3254_ = v___x_3265_;
goto v___jp_3253_;
}
v___jp_3253_:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3255_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__2));
v___x_3256_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_contents_3252_);
v___x_3257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3255_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
lean_inc(v___y_3254_);
v___x_3258_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___y_3254_);
lean_ctor_set(v___x_3258_, 1, v___x_3257_);
v___x_3259_ = 0;
v___x_3260_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3260_, 0, v___x_3258_);
lean_ctor_set_uint8(v___x_3260_, sizeof(void*)*1, v___x_3259_);
v___x_3261_ = l_Repr_addAppParen(v___x_3260_, v_prec_3251_);
return v___x_3261_;
}
}
case 1:
{
lean_object* v_content_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3286_; 
v_content_3266_ = lean_ctor_get(v_x_3250_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v_x_3250_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3268_ = v_x_3250_;
v_isShared_3269_ = v_isSharedCheck_3286_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_content_3266_);
lean_dec(v_x_3250_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3286_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___y_3271_; lean_object* v___x_3282_; uint8_t v___x_3283_; 
v___x_3282_ = lean_unsigned_to_nat(1024u);
v___x_3283_ = lean_nat_dec_le(v___x_3282_, v_prec_3251_);
if (v___x_3283_ == 0)
{
lean_object* v___x_3284_; 
v___x_3284_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3271_ = v___x_3284_;
goto v___jp_3270_;
}
else
{
lean_object* v___x_3285_; 
v___x_3285_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3271_ = v___x_3285_;
goto v___jp_3270_;
}
v___jp_3270_:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3275_; 
v___x_3272_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__5));
v___x_3273_ = l_String_quote(v_content_3266_);
if (v_isShared_3269_ == 0)
{
lean_ctor_set_tag(v___x_3268_, 3);
lean_ctor_set(v___x_3268_, 0, v___x_3273_);
v___x_3275_ = v___x_3268_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3273_);
v___x_3275_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; uint8_t v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3276_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3272_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
lean_inc(v___y_3271_);
v___x_3277_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___y_3271_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
v___x_3278_ = 0;
v___x_3279_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3279_, 0, v___x_3277_);
lean_ctor_set_uint8(v___x_3279_, sizeof(void*)*1, v___x_3278_);
v___x_3280_ = l_Repr_addAppParen(v___x_3279_, v_prec_3251_);
return v___x_3280_;
}
}
}
}
case 2:
{
lean_object* v_items_3287_; lean_object* v___y_3289_; lean_object* v___x_3297_; uint8_t v___x_3298_; 
v_items_3287_ = lean_ctor_get(v_x_3250_, 0);
lean_inc_ref(v_items_3287_);
lean_dec_ref_known(v_x_3250_, 1);
v___x_3297_ = lean_unsigned_to_nat(1024u);
v___x_3298_ = lean_nat_dec_le(v___x_3297_, v_prec_3251_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; 
v___x_3299_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3289_ = v___x_3299_;
goto v___jp_3288_;
}
else
{
lean_object* v___x_3300_; 
v___x_3300_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3289_ = v___x_3300_;
goto v___jp_3288_;
}
v___jp_3288_:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; uint8_t v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3290_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__8));
v___x_3291_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_3287_);
v___x_3292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3290_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
lean_inc(v___y_3289_);
v___x_3293_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___y_3289_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = 0;
v___x_3295_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3295_, 0, v___x_3293_);
lean_ctor_set_uint8(v___x_3295_, sizeof(void*)*1, v___x_3294_);
v___x_3296_ = l_Repr_addAppParen(v___x_3295_, v_prec_3251_);
return v___x_3296_;
}
}
case 3:
{
lean_object* v_start_3301_; lean_object* v_items_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3337_; 
v_start_3301_ = lean_ctor_get(v_x_3250_, 0);
v_items_3302_ = lean_ctor_get(v_x_3250_, 1);
v_isSharedCheck_3337_ = !lean_is_exclusive(v_x_3250_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3304_ = v_x_3250_;
v_isShared_3305_ = v_isSharedCheck_3337_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_items_3302_);
lean_inc(v_start_3301_);
lean_dec(v_x_3250_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3337_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3322_; lean_object* v___x_3333_; uint8_t v___x_3334_; 
v___x_3333_ = lean_unsigned_to_nat(1024u);
v___x_3334_ = lean_nat_dec_le(v___x_3333_, v_prec_3251_);
if (v___x_3334_ == 0)
{
lean_object* v___x_3335_; 
v___x_3335_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3322_ = v___x_3335_;
goto v___jp_3321_;
}
else
{
lean_object* v___x_3336_; 
v___x_3336_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3322_ = v___x_3336_;
goto v___jp_3321_;
}
v___jp_3306_:
{
lean_object* v___x_3312_; 
lean_inc(v___y_3308_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set_tag(v___x_3304_, 5);
lean_ctor_set(v___x_3304_, 1, v___y_3310_);
lean_ctor_set(v___x_3304_, 0, v___y_3308_);
v___x_3312_ = v___x_3304_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___y_3308_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v___y_3310_);
v___x_3312_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; uint8_t v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
lean_inc(v___y_3309_);
v___x_3313_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
lean_ctor_set(v___x_3313_, 1, v___y_3309_);
v___x_3314_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_3302_);
v___x_3315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3313_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
lean_inc(v___y_3307_);
v___x_3316_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___y_3307_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
v___x_3317_ = 0;
v___x_3318_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3318_, 0, v___x_3316_);
lean_ctor_set_uint8(v___x_3318_, sizeof(void*)*1, v___x_3317_);
v___x_3319_ = l_Repr_addAppParen(v___x_3318_, v_prec_3251_);
return v___x_3319_;
}
}
v___jp_3321_:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; 
v___x_3323_ = lean_box(1);
v___x_3324_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__11));
v___x_3325_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12, &l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12);
v___x_3326_ = lean_int_dec_lt(v_start_3301_, v___x_3325_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = l_Int_repr(v_start_3301_);
lean_dec(v_start_3301_);
v___x_3328_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3327_);
v___y_3307_ = v___y_3322_;
v___y_3308_ = v___x_3324_;
v___y_3309_ = v___x_3323_;
v___y_3310_ = v___x_3328_;
goto v___jp_3306_;
}
else
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3329_ = lean_unsigned_to_nat(1024u);
v___x_3330_ = l_Int_repr(v_start_3301_);
lean_dec(v_start_3301_);
v___x_3331_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
v___x_3332_ = l_Repr_addAppParen(v___x_3331_, v___x_3329_);
v___y_3307_ = v___y_3322_;
v___y_3308_ = v___x_3324_;
v___y_3309_ = v___x_3323_;
v___y_3310_ = v___x_3332_;
goto v___jp_3306_;
}
}
}
}
case 4:
{
lean_object* v_items_3338_; lean_object* v___y_3340_; lean_object* v___x_3348_; uint8_t v___x_3349_; 
v_items_3338_ = lean_ctor_get(v_x_3250_, 0);
lean_inc_ref(v_items_3338_);
lean_dec_ref_known(v_x_3250_, 1);
v___x_3348_ = lean_unsigned_to_nat(1024u);
v___x_3349_ = lean_nat_dec_le(v___x_3348_, v_prec_3251_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; 
v___x_3350_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3340_ = v___x_3350_;
goto v___jp_3339_;
}
else
{
lean_object* v___x_3351_; 
v___x_3351_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3340_ = v___x_3351_;
goto v___jp_3339_;
}
v___jp_3339_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3341_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__15));
v___x_3342_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(v_items_3338_);
v___x_3343_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3341_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
lean_inc(v___y_3340_);
v___x_3344_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___y_3340_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = 0;
v___x_3346_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3346_, 0, v___x_3344_);
lean_ctor_set_uint8(v___x_3346_, sizeof(void*)*1, v___x_3345_);
v___x_3347_ = l_Repr_addAppParen(v___x_3346_, v_prec_3251_);
return v___x_3347_;
}
}
case 5:
{
lean_object* v_items_3352_; lean_object* v___y_3354_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v_items_3352_ = lean_ctor_get(v_x_3250_, 0);
lean_inc_ref(v_items_3352_);
lean_dec_ref_known(v_x_3250_, 1);
v___x_3362_ = lean_unsigned_to_nat(1024u);
v___x_3363_ = lean_nat_dec_le(v___x_3362_, v_prec_3251_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; 
v___x_3364_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3354_ = v___x_3364_;
goto v___jp_3353_;
}
else
{
lean_object* v___x_3365_; 
v___x_3365_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3354_ = v___x_3365_;
goto v___jp_3353_;
}
v___jp_3353_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; uint8_t v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3355_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__18));
v___x_3356_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_items_3352_);
v___x_3357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3355_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
lean_inc(v___y_3354_);
v___x_3358_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___y_3354_);
lean_ctor_set(v___x_3358_, 1, v___x_3357_);
v___x_3359_ = 0;
v___x_3360_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3360_, 0, v___x_3358_);
lean_ctor_set_uint8(v___x_3360_, sizeof(void*)*1, v___x_3359_);
v___x_3361_ = l_Repr_addAppParen(v___x_3360_, v_prec_3251_);
return v___x_3361_;
}
}
case 6:
{
lean_object* v_content_3366_; lean_object* v___y_3368_; lean_object* v___x_3376_; uint8_t v___x_3377_; 
v_content_3366_ = lean_ctor_get(v_x_3250_, 0);
lean_inc_ref(v_content_3366_);
lean_dec_ref_known(v_x_3250_, 1);
v___x_3376_ = lean_unsigned_to_nat(1024u);
v___x_3377_ = lean_nat_dec_le(v___x_3376_, v_prec_3251_);
if (v___x_3377_ == 0)
{
lean_object* v___x_3378_; 
v___x_3378_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3368_ = v___x_3378_;
goto v___jp_3367_;
}
else
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3368_ = v___x_3379_;
goto v___jp_3367_;
}
v___jp_3367_:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3369_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__21));
v___x_3370_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_3366_);
v___x_3371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3369_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
lean_inc(v___y_3368_);
v___x_3372_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___y_3368_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
v___x_3373_ = 0;
v___x_3374_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3374_, 0, v___x_3372_);
lean_ctor_set_uint8(v___x_3374_, sizeof(void*)*1, v___x_3373_);
v___x_3375_ = l_Repr_addAppParen(v___x_3374_, v_prec_3251_);
return v___x_3375_;
}
}
default: 
{
lean_object* v_container_3380_; lean_object* v_content_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3429_; 
v_container_3380_ = lean_ctor_get(v_x_3250_, 0);
v_content_3381_ = lean_ctor_get(v_x_3250_, 1);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_x_3250_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3383_ = v_x_3250_;
v_isShared_3384_ = v_isSharedCheck_3429_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_content_3381_);
lean_inc(v_container_3380_);
lean_dec(v_x_3250_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3429_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___y_3386_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v___x_3425_ = lean_unsigned_to_nat(1024u);
v___x_3426_ = lean_nat_dec_le(v___x_3425_, v_prec_3251_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_3386_ = v___x_3427_;
goto v___jp_3385_;
}
else
{
lean_object* v___x_3428_; 
v___x_3428_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_3386_ = v___x_3428_;
goto v___jp_3385_;
}
v___jp_3385_:
{
lean_object* v_name_3387_; lean_object* v_val_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3424_; 
v_name_3387_ = lean_ctor_get(v_container_3380_, 0);
v_val_3388_ = lean_ctor_get(v_container_3380_, 1);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_container_3380_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3390_ = v_container_3380_;
v_isShared_3391_ = v_isSharedCheck_3424_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_val_3388_);
lean_inc(v_name_3387_);
lean_dec(v_container_3380_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3424_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3398_; 
v___x_3392_ = lean_box(1);
v___x_3393_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__24));
v___x_3394_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__2));
v___x_3395_ = lean_unsigned_to_nat(0u);
v___x_3396_ = l_Lean_Name_reprPrec(v_name_3387_, v___x_3395_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set_tag(v___x_3390_, 5);
lean_ctor_set(v___x_3390_, 1, v___x_3396_);
lean_ctor_set(v___x_3390_, 0, v___x_3394_);
v___x_3398_ = v___x_3390_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3394_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3399_; uint8_t v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3403_; 
v___x_3399_ = l_Std_Format_nestD(v___x_3398_);
v___x_3400_ = 0;
v___x_3401_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3401_, 0, v___x_3399_);
lean_ctor_set_uint8(v___x_3401_, sizeof(void*)*1, v___x_3400_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set_tag(v___x_3383_, 5);
lean_ctor_set(v___x_3383_, 1, v___x_3392_);
lean_ctor_set(v___x_3383_, 0, v___x_3401_);
v___x_3403_ = v___x_3383_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3401_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v___x_3392_);
v___x_3403_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3404_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__8));
v___x_3405_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_3388_);
lean_dec(v_val_3388_);
v___x_3406_ = l_Lean_Name_reprPrec(v___x_3405_, v___x_3395_);
v___x_3407_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3404_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
v___x_3408_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_3409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3407_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___x_3410_ = l_Std_Format_nestD(v___x_3409_);
v___x_3411_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
lean_ctor_set_uint8(v___x_3411_, sizeof(void*)*1, v___x_3400_);
v___x_3412_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3403_);
lean_ctor_set(v___x_3412_, 1, v___x_3411_);
v___x_3413_ = l_Std_Format_nestD(v___x_3412_);
v___x_3414_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
lean_ctor_set_uint8(v___x_3414_, sizeof(void*)*1, v___x_3400_);
v___x_3415_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3393_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
v___x_3416_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
lean_ctor_set(v___x_3416_, 1, v___x_3392_);
v___x_3417_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_3381_);
v___x_3418_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
lean_inc(v___y_3386_);
v___x_3419_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___y_3386_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
v___x_3420_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3420_, 0, v___x_3419_);
lean_ctor_set_uint8(v___x_3420_, sizeof(void*)*1, v___x_3400_);
v___x_3421_ = l_Repr_addAppParen(v___x_3420_, v_prec_3251_);
return v___x_3421_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(lean_object* v___y_3430_){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = lean_unsigned_to_nat(0u);
v___x_3432_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v___y_3430_, v___x_3431_);
return v___x_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___boxed(lean_object* v_x_3433_, lean_object* v_prec_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_x_3433_, v_prec_3434_);
lean_dec(v_prec_3434_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(lean_object* v_xs_3436_){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; 
v___x_3437_ = lean_array_get_size(v_xs_3436_);
v___x_3438_ = lean_unsigned_to_nat(0u);
v___x_3439_ = lean_nat_dec_eq(v___x_3437_, v___x_3438_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3440_ = lean_array_to_list(v_xs_3436_);
v___x_3441_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3442_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_3440_, v___x_3441_);
v___x_3443_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3444_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3444_);
lean_ctor_set(v___x_3445_, 1, v___x_3442_);
v___x_3446_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3445_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___x_3448_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3443_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
v___x_3449_ = l_Std_Format_fill(v___x_3448_);
return v___x_3449_;
}
else
{
lean_object* v___x_3450_; 
lean_dec_ref(v_xs_3436_);
v___x_3450_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3450_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(lean_object* v_x_3454_){
_start:
{
lean_object* v___x_3455_; 
v___x_3455_ = ((lean_object*)(l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__1));
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___boxed(lean_object* v_x_3456_){
_start:
{
lean_object* v_res_3457_; 
v_res_3457_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_3456_);
lean_dec(v_x_3456_);
return v_res_3457_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3467_ = lean_unsigned_to_nat(9u);
v___x_3468_ = lean_nat_to_int(v___x_3467_);
return v___x_3468_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3472_ = lean_unsigned_to_nat(15u);
v___x_3473_ = lean_nat_to_int(v___x_3472_);
return v___x_3473_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12(void){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3480_ = lean_unsigned_to_nat(11u);
v___x_3481_ = lean_nat_to_int(v___x_3480_);
return v___x_3481_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(lean_object* v_x_3485_, lean_object* v_x_3486_, lean_object* v_x_3487_){
_start:
{
if (lean_obj_tag(v_x_3487_) == 0)
{
lean_dec(v_x_3485_);
return v_x_3486_;
}
else
{
lean_object* v_head_3488_; lean_object* v_tail_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3499_; 
v_head_3488_ = lean_ctor_get(v_x_3487_, 0);
v_tail_3489_ = lean_ctor_get(v_x_3487_, 1);
v_isSharedCheck_3499_ = !lean_is_exclusive(v_x_3487_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3491_ = v_x_3487_;
v_isShared_3492_ = v_isSharedCheck_3499_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_tail_3489_);
lean_inc(v_head_3488_);
lean_dec(v_x_3487_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3499_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
lean_inc(v_x_3485_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set_tag(v___x_3491_, 5);
lean_ctor_set(v___x_3491_, 1, v_x_3485_);
lean_ctor_set(v___x_3491_, 0, v_x_3486_);
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_x_3486_);
lean_ctor_set(v_reuseFailAlloc_3498_, 1, v_x_3485_);
v___x_3494_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3495_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3488_);
v___x_3496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3494_);
lean_ctor_set(v___x_3496_, 1, v___x_3495_);
v___x_3497_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(v_x_3485_, v___x_3496_, v_tail_3489_);
return v___x_3497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(lean_object* v_x_3500_, lean_object* v_x_3501_){
_start:
{
if (lean_obj_tag(v_x_3500_) == 0)
{
lean_object* v___x_3502_; 
lean_dec(v_x_3501_);
v___x_3502_ = lean_box(0);
return v___x_3502_;
}
else
{
lean_object* v_tail_3503_; 
v_tail_3503_ = lean_ctor_get(v_x_3500_, 1);
if (lean_obj_tag(v_tail_3503_) == 0)
{
lean_object* v_head_3504_; lean_object* v___x_3505_; 
lean_dec(v_x_3501_);
v_head_3504_ = lean_ctor_get(v_x_3500_, 0);
lean_inc(v_head_3504_);
lean_dec_ref_known(v_x_3500_, 2);
v___x_3505_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3504_);
return v___x_3505_;
}
else
{
lean_object* v_head_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
lean_inc(v_tail_3503_);
v_head_3506_ = lean_ctor_get(v_x_3500_, 0);
lean_inc(v_head_3506_);
lean_dec_ref_known(v_x_3500_, 2);
v___x_3507_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3506_);
v___x_3508_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(v_x_3501_, v___x_3507_, v_tail_3503_);
return v___x_3508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(lean_object* v_xs_3509_){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; uint8_t v___x_3512_; 
v___x_3510_ = lean_array_get_size(v_xs_3509_);
v___x_3511_ = lean_unsigned_to_nat(0u);
v___x_3512_ = lean_nat_dec_eq(v___x_3510_, v___x_3511_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3513_ = lean_array_to_list(v_xs_3509_);
v___x_3514_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3515_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(v___x_3513_, v___x_3514_);
v___x_3516_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3517_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
lean_ctor_set(v___x_3518_, 1, v___x_3515_);
v___x_3519_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3518_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v___x_3521_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3516_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
v___x_3522_ = l_Std_Format_fill(v___x_3521_);
return v___x_3522_;
}
else
{
lean_object* v___x_3523_; 
lean_dec_ref(v_xs_3509_);
v___x_3523_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(lean_object* v_x_3524_){
_start:
{
lean_object* v_title_3525_; lean_object* v_titleString_3526_; lean_object* v_metadata_3527_; lean_object* v_content_3528_; lean_object* v_subParts_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; uint8_t v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v_title_3525_ = lean_ctor_get(v_x_3524_, 0);
lean_inc_ref(v_title_3525_);
v_titleString_3526_ = lean_ctor_get(v_x_3524_, 1);
lean_inc_ref(v_titleString_3526_);
v_metadata_3527_ = lean_ctor_get(v_x_3524_, 2);
lean_inc(v_metadata_3527_);
v_content_3528_ = lean_ctor_get(v_x_3524_, 3);
lean_inc_ref(v_content_3528_);
v_subParts_3529_ = lean_ctor_get(v_x_3524_, 4);
lean_inc_ref(v_subParts_3529_);
lean_dec_ref(v_x_3524_);
v___x_3530_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3531_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__3));
v___x_3532_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4);
v___x_3533_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_title_3525_);
v___x_3534_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3532_);
lean_ctor_set(v___x_3534_, 1, v___x_3533_);
v___x_3535_ = 0;
v___x_3536_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3536_, 0, v___x_3534_);
lean_ctor_set_uint8(v___x_3536_, sizeof(void*)*1, v___x_3535_);
v___x_3537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3531_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
v___x_3538_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3537_);
lean_ctor_set(v___x_3539_, 1, v___x_3538_);
v___x_3540_ = lean_box(1);
v___x_3541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3539_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
v___x_3542_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__6));
v___x_3543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3541_);
lean_ctor_set(v___x_3543_, 1, v___x_3542_);
v___x_3544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
lean_ctor_set(v___x_3544_, 1, v___x_3530_);
v___x_3545_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7);
v___x_3546_ = l_String_quote(v_titleString_3526_);
v___x_3547_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3546_);
v___x_3548_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3545_);
lean_ctor_set(v___x_3548_, 1, v___x_3547_);
v___x_3549_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
lean_ctor_set_uint8(v___x_3549_, sizeof(void*)*1, v___x_3535_);
v___x_3550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3544_);
lean_ctor_set(v___x_3550_, 1, v___x_3549_);
v___x_3551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
lean_ctor_set(v___x_3551_, 1, v___x_3538_);
v___x_3552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3551_);
lean_ctor_set(v___x_3552_, 1, v___x_3540_);
v___x_3553_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__9));
v___x_3554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3552_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
v___x_3555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3554_);
lean_ctor_set(v___x_3555_, 1, v___x_3530_);
v___x_3556_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3557_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_metadata_3527_);
lean_dec(v_metadata_3527_);
v___x_3558_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3556_);
lean_ctor_set(v___x_3558_, 1, v___x_3557_);
v___x_3559_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3559_, 0, v___x_3558_);
lean_ctor_set_uint8(v___x_3559_, sizeof(void*)*1, v___x_3535_);
v___x_3560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3555_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
v___x_3561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3560_);
lean_ctor_set(v___x_3561_, 1, v___x_3538_);
v___x_3562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3561_);
lean_ctor_set(v___x_3562_, 1, v___x_3540_);
v___x_3563_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__11));
v___x_3564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3562_);
lean_ctor_set(v___x_3564_, 1, v___x_3563_);
v___x_3565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3564_);
lean_ctor_set(v___x_3565_, 1, v___x_3530_);
v___x_3566_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12);
v___x_3567_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_content_3528_);
v___x_3568_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3566_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3569_, 0, v___x_3568_);
lean_ctor_set_uint8(v___x_3569_, sizeof(void*)*1, v___x_3535_);
v___x_3570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3565_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3570_);
lean_ctor_set(v___x_3571_, 1, v___x_3538_);
v___x_3572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
lean_ctor_set(v___x_3572_, 1, v___x_3540_);
v___x_3573_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__14));
v___x_3574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3572_);
lean_ctor_set(v___x_3574_, 1, v___x_3573_);
v___x_3575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
lean_ctor_set(v___x_3575_, 1, v___x_3530_);
v___x_3576_ = l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(v_subParts_3529_);
v___x_3577_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3556_);
lean_ctor_set(v___x_3577_, 1, v___x_3576_);
v___x_3578_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
lean_ctor_set_uint8(v___x_3578_, sizeof(void*)*1, v___x_3535_);
v___x_3579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3575_);
lean_ctor_set(v___x_3579_, 1, v___x_3578_);
v___x_3580_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3581_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
lean_ctor_set(v___x_3582_, 1, v___x_3579_);
v___x_3583_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3582_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3580_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
v___x_3586_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3586_, 0, v___x_3585_);
lean_ctor_set_uint8(v___x_3586_, sizeof(void*)*1, v___x_3535_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(lean_object* v_x_3587_, lean_object* v_x_3588_, lean_object* v_x_3589_){
_start:
{
if (lean_obj_tag(v_x_3589_) == 0)
{
lean_dec(v_x_3587_);
return v_x_3588_;
}
else
{
lean_object* v_head_3590_; lean_object* v_tail_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3601_; 
v_head_3590_ = lean_ctor_get(v_x_3589_, 0);
v_tail_3591_ = lean_ctor_get(v_x_3589_, 1);
v_isSharedCheck_3601_ = !lean_is_exclusive(v_x_3589_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3593_ = v_x_3589_;
v_isShared_3594_ = v_isSharedCheck_3601_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_tail_3591_);
lean_inc(v_head_3590_);
lean_dec(v_x_3589_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3601_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
lean_inc(v_x_3587_);
if (v_isShared_3594_ == 0)
{
lean_ctor_set_tag(v___x_3593_, 5);
lean_ctor_set(v___x_3593_, 1, v_x_3587_);
lean_ctor_set(v___x_3593_, 0, v_x_3588_);
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_x_3588_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_x_3587_);
v___x_3596_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3597_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_3590_);
v___x_3598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3596_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
v_x_3588_ = v___x_3598_;
v_x_3589_ = v_tail_3591_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(lean_object* v_x_3602_, lean_object* v_x_3603_){
_start:
{
lean_object* v_fst_3604_; lean_object* v_snd_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3615_; 
v_fst_3604_ = lean_ctor_get(v_x_3602_, 0);
v_snd_3605_ = lean_ctor_get(v_x_3602_, 1);
v_isSharedCheck_3615_ = !lean_is_exclusive(v_x_3602_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3607_ = v_x_3602_;
v_isShared_3608_ = v_isSharedCheck_3615_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_snd_3605_);
lean_inc(v_fst_3604_);
lean_dec(v_x_3602_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3615_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3609_; lean_object* v___x_3611_; 
v___x_3609_ = l_Lean_instReprDeclarationRange_repr___redArg(v_fst_3604_);
if (v_isShared_3608_ == 0)
{
lean_ctor_set_tag(v___x_3607_, 1);
lean_ctor_set(v___x_3607_, 1, v_x_3603_);
lean_ctor_set(v___x_3607_, 0, v___x_3609_);
v___x_3611_ = v___x_3607_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3609_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v_x_3603_);
v___x_3611_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3612_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_snd_3605_);
v___x_3613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3612_);
lean_ctor_set(v___x_3613_, 1, v___x_3611_);
return v___x_3613_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(lean_object* v_x_3616_, lean_object* v_x_3617_, lean_object* v_x_3618_){
_start:
{
if (lean_obj_tag(v_x_3618_) == 0)
{
lean_dec(v_x_3616_);
return v_x_3617_;
}
else
{
lean_object* v_head_3619_; lean_object* v_tail_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3629_; 
v_head_3619_ = lean_ctor_get(v_x_3618_, 0);
v_tail_3620_ = lean_ctor_get(v_x_3618_, 1);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_x_3618_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3622_ = v_x_3618_;
v_isShared_3623_ = v_isSharedCheck_3629_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_tail_3620_);
lean_inc(v_head_3619_);
lean_dec(v_x_3618_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3629_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
lean_inc(v_x_3616_);
if (v_isShared_3623_ == 0)
{
lean_ctor_set_tag(v___x_3622_, 5);
lean_ctor_set(v___x_3622_, 1, v_x_3616_);
lean_ctor_set(v___x_3622_, 0, v_x_3617_);
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_x_3617_);
lean_ctor_set(v_reuseFailAlloc_3628_, 1, v_x_3616_);
v___x_3625_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
lean_object* v___x_3626_; 
v___x_3626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3625_);
lean_ctor_set(v___x_3626_, 1, v_head_3619_);
v_x_3617_ = v___x_3626_;
v_x_3618_ = v_tail_3620_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(lean_object* v_x_3630_, lean_object* v_x_3631_){
_start:
{
if (lean_obj_tag(v_x_3630_) == 0)
{
lean_object* v___x_3632_; 
lean_dec(v_x_3631_);
v___x_3632_ = lean_box(0);
return v___x_3632_;
}
else
{
lean_object* v_tail_3633_; 
v_tail_3633_ = lean_ctor_get(v_x_3630_, 1);
if (lean_obj_tag(v_tail_3633_) == 0)
{
lean_object* v_head_3634_; 
lean_dec(v_x_3631_);
v_head_3634_ = lean_ctor_get(v_x_3630_, 0);
lean_inc(v_head_3634_);
lean_dec_ref_known(v_x_3630_, 2);
return v_head_3634_;
}
else
{
lean_object* v_head_3635_; lean_object* v___x_3636_; 
lean_inc(v_tail_3633_);
v_head_3635_ = lean_ctor_get(v_x_3630_, 0);
lean_inc(v_head_3635_);
lean_dec_ref_known(v_x_3630_, 2);
v___x_3636_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(v_x_3631_, v_head_3635_, v_tail_3633_);
return v___x_3636_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3638_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0));
v___x_3639_ = lean_string_length(v___x_3638_);
return v___x_3639_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3640_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1);
v___x_3641_ = lean_nat_to_int(v___x_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(lean_object* v_x_3646_){
_start:
{
lean_object* v_fst_3647_; lean_object* v_snd_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3670_; 
v_fst_3647_ = lean_ctor_get(v_x_3646_, 0);
v_snd_3648_ = lean_ctor_get(v_x_3646_, 1);
v_isSharedCheck_3670_ = !lean_is_exclusive(v_x_3646_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3650_ = v_x_3646_;
v_isShared_3651_ = v_isSharedCheck_3670_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_snd_3648_);
lean_inc(v_fst_3647_);
lean_dec(v_x_3646_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3670_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3656_; 
v___x_3652_ = l_Nat_reprFast(v_fst_3647_);
v___x_3653_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
v___x_3654_ = lean_box(0);
if (v_isShared_3651_ == 0)
{
lean_ctor_set_tag(v___x_3650_, 1);
lean_ctor_set(v___x_3650_, 1, v___x_3654_);
lean_ctor_set(v___x_3650_, 0, v___x_3653_);
v___x_3656_ = v___x_3650_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v___x_3654_);
v___x_3656_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; lean_object* v___x_3668_; 
v___x_3657_ = l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(v_snd_3648_, v___x_3656_);
v___x_3658_ = l_List_reverse___redArg(v___x_3657_);
v___x_3659_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3660_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(v___x_3658_, v___x_3659_);
v___x_3661_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2);
v___x_3662_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3));
v___x_3663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
lean_ctor_set(v___x_3663_, 1, v___x_3660_);
v___x_3664_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4));
v___x_3665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3663_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
v___x_3666_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3661_);
lean_ctor_set(v___x_3666_, 1, v___x_3665_);
v___x_3667_ = 0;
v___x_3668_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3668_, 0, v___x_3666_);
lean_ctor_set_uint8(v___x_3668_, sizeof(void*)*1, v___x_3667_);
return v___x_3668_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(lean_object* v_x_3671_, lean_object* v_x_3672_, lean_object* v_x_3673_){
_start:
{
if (lean_obj_tag(v_x_3673_) == 0)
{
lean_dec(v_x_3671_);
return v_x_3672_;
}
else
{
lean_object* v_head_3674_; lean_object* v_tail_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3685_; 
v_head_3674_ = lean_ctor_get(v_x_3673_, 0);
v_tail_3675_ = lean_ctor_get(v_x_3673_, 1);
v_isSharedCheck_3685_ = !lean_is_exclusive(v_x_3673_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3677_ = v_x_3673_;
v_isShared_3678_ = v_isSharedCheck_3685_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_tail_3675_);
lean_inc(v_head_3674_);
lean_dec(v_x_3673_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3685_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
lean_inc(v_x_3671_);
if (v_isShared_3678_ == 0)
{
lean_ctor_set_tag(v___x_3677_, 5);
lean_ctor_set(v___x_3677_, 1, v_x_3671_);
lean_ctor_set(v___x_3677_, 0, v_x_3672_);
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_x_3672_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v_x_3671_);
v___x_3680_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3681_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3674_);
v___x_3682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3680_);
lean_ctor_set(v___x_3682_, 1, v___x_3681_);
v_x_3672_ = v___x_3682_;
v_x_3673_ = v_tail_3675_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(lean_object* v_x_3686_, lean_object* v_x_3687_, lean_object* v_x_3688_){
_start:
{
if (lean_obj_tag(v_x_3688_) == 0)
{
lean_dec(v_x_3686_);
return v_x_3687_;
}
else
{
lean_object* v_head_3689_; lean_object* v_tail_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3700_; 
v_head_3689_ = lean_ctor_get(v_x_3688_, 0);
v_tail_3690_ = lean_ctor_get(v_x_3688_, 1);
v_isSharedCheck_3700_ = !lean_is_exclusive(v_x_3688_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3692_ = v_x_3688_;
v_isShared_3693_ = v_isSharedCheck_3700_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_tail_3690_);
lean_inc(v_head_3689_);
lean_dec(v_x_3688_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3700_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
lean_inc(v_x_3686_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set_tag(v___x_3692_, 5);
lean_ctor_set(v___x_3692_, 1, v_x_3686_);
lean_ctor_set(v___x_3692_, 0, v_x_3687_);
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_x_3687_);
lean_ctor_set(v_reuseFailAlloc_3699_, 1, v_x_3686_);
v___x_3695_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3696_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3689_);
v___x_3697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3695_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
v___x_3698_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(v_x_3686_, v___x_3697_, v_tail_3690_);
return v___x_3698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(lean_object* v_x_3701_, lean_object* v_x_3702_){
_start:
{
if (lean_obj_tag(v_x_3701_) == 0)
{
lean_object* v___x_3703_; 
lean_dec(v_x_3702_);
v___x_3703_ = lean_box(0);
return v___x_3703_;
}
else
{
lean_object* v_tail_3704_; 
v_tail_3704_ = lean_ctor_get(v_x_3701_, 1);
if (lean_obj_tag(v_tail_3704_) == 0)
{
lean_object* v_head_3705_; lean_object* v___x_3706_; 
lean_dec(v_x_3702_);
v_head_3705_ = lean_ctor_get(v_x_3701_, 0);
lean_inc(v_head_3705_);
lean_dec_ref_known(v_x_3701_, 2);
v___x_3706_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3705_);
return v___x_3706_;
}
else
{
lean_object* v_head_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
lean_inc(v_tail_3704_);
v_head_3707_ = lean_ctor_get(v_x_3701_, 0);
lean_inc(v_head_3707_);
lean_dec_ref_known(v_x_3701_, 2);
v___x_3708_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3707_);
v___x_3709_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(v_x_3702_, v___x_3708_, v_tail_3704_);
return v___x_3709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(lean_object* v_xs_3710_){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; uint8_t v___x_3713_; 
v___x_3711_ = lean_array_get_size(v_xs_3710_);
v___x_3712_ = lean_unsigned_to_nat(0u);
v___x_3713_ = lean_nat_dec_eq(v___x_3711_, v___x_3712_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3714_ = lean_array_to_list(v_xs_3710_);
v___x_3715_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3716_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(v___x_3714_, v___x_3715_);
v___x_3717_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_3718_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6));
v___x_3719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3718_);
lean_ctor_set(v___x_3719_, 1, v___x_3716_);
v___x_3720_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3719_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3717_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
v___x_3723_ = l_Std_Format_fill(v___x_3722_);
return v___x_3723_;
}
else
{
lean_object* v___x_3724_; 
lean_dec_ref(v_xs_3710_);
v___x_3724_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9));
return v___x_3724_;
}
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
v___x_3740_ = lean_unsigned_to_nat(20u);
v___x_3741_ = lean_nat_to_int(v___x_3740_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(lean_object* v_x_3742_){
_start:
{
lean_object* v_text_3743_; lean_object* v_sections_3744_; lean_object* v_declarationRange_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; uint8_t v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
v_text_3743_ = lean_ctor_get(v_x_3742_, 0);
lean_inc_ref(v_text_3743_);
v_sections_3744_ = lean_ctor_get(v_x_3742_, 1);
lean_inc_ref(v_sections_3744_);
v_declarationRange_3745_ = lean_ctor_get(v_x_3742_, 2);
lean_inc_ref(v_declarationRange_3745_);
lean_dec_ref(v_x_3742_);
v___x_3746_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3747_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__3));
v___x_3748_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_3749_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_text_3743_);
v___x_3750_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3748_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = 0;
v___x_3752_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3752_, 0, v___x_3750_);
lean_ctor_set_uint8(v___x_3752_, sizeof(void*)*1, v___x_3751_);
v___x_3753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3747_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
v___x_3754_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3753_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v___x_3756_ = lean_box(1);
v___x_3757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3755_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
v___x_3758_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__5));
v___x_3759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3757_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
v___x_3760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
lean_ctor_set(v___x_3760_, 1, v___x_3746_);
v___x_3761_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3762_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(v_sections_3744_);
v___x_3763_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3761_);
lean_ctor_set(v___x_3763_, 1, v___x_3762_);
v___x_3764_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3764_, 0, v___x_3763_);
lean_ctor_set_uint8(v___x_3764_, sizeof(void*)*1, v___x_3751_);
v___x_3765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3760_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
lean_ctor_set(v___x_3766_, 1, v___x_3754_);
v___x_3767_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3766_);
lean_ctor_set(v___x_3767_, 1, v___x_3756_);
v___x_3768_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__7));
v___x_3769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3767_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
v___x_3770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3769_);
lean_ctor_set(v___x_3770_, 1, v___x_3746_);
v___x_3771_ = lean_obj_once(&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8, &l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8_once, _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8);
v___x_3772_ = l_Lean_instReprDeclarationRange_repr___redArg(v_declarationRange_3745_);
v___x_3773_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3771_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3774_, 0, v___x_3773_);
lean_ctor_set_uint8(v___x_3774_, sizeof(void*)*1, v___x_3751_);
v___x_3775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3770_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
v___x_3776_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3777_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3778_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3777_);
lean_ctor_set(v___x_3778_, 1, v___x_3775_);
v___x_3779_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3778_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
v___x_3781_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3776_);
lean_ctor_set(v___x_3781_, 1, v___x_3780_);
v___x_3782_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3782_, 0, v___x_3781_);
lean_ctor_set_uint8(v___x_3782_, sizeof(void*)*1, v___x_3751_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr(lean_object* v_x_3783_, lean_object* v_prec_3784_){
_start:
{
lean_object* v___x_3785_; 
v___x_3785_ = l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(v_x_3783_);
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___boxed(lean_object* v_x_3786_, lean_object* v_prec_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l_Lean_VersoModuleDocs_instReprSnippet_repr(v_x_3786_, v_prec_3787_);
lean_dec(v_prec_3787_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(lean_object* v_x_3789_, lean_object* v_x_3790_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_x_3789_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___boxed(lean_object* v_x_3792_, lean_object* v_x_3793_){
_start:
{
lean_object* v_res_3794_; 
v_res_3794_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(v_x_3792_, v_x_3793_);
lean_dec(v_x_3793_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_3795_, lean_object* v_prec_3796_){
_start:
{
lean_object* v___x_3797_; 
v___x_3797_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_x_3795_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_x_3798_, lean_object* v_prec_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(v_x_3798_, v_prec_3799_);
lean_dec(v_prec_3799_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(lean_object* v_x_3801_, lean_object* v_prec_3802_){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_x_3801_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_x_3804_, lean_object* v_prec_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(v_x_3804_, v_prec_3805_);
lean_dec(v_prec_3805_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(lean_object* v_x_3807_, lean_object* v_x_3808_){
_start:
{
lean_object* v___x_3809_; 
v___x_3809_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_3807_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___boxed(lean_object* v_x_3810_, lean_object* v_x_3811_){
_start:
{
lean_object* v_res_3812_; 
v_res_3812_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(v_x_3810_, v_x_3811_);
lean_dec(v_x_3811_);
lean_dec(v_x_3810_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(lean_object* v_x_3813_, lean_object* v_prec_3814_){
_start:
{
lean_object* v___x_3815_; 
v___x_3815_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_x_3813_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___boxed(lean_object* v_x_3816_, lean_object* v_prec_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(v_x_3816_, v_prec_3817_);
lean_dec(v_prec_3817_);
return v_res_3818_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_Snippet_canNestIn(lean_object* v_level_3821_, lean_object* v_snippet_3822_){
_start:
{
lean_object* v_sections_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; uint8_t v___x_3826_; 
v_sections_3823_ = lean_ctor_get(v_snippet_3822_, 1);
v___x_3824_ = lean_unsigned_to_nat(0u);
v___x_3825_ = lean_array_get_size(v_sections_3823_);
v___x_3826_ = lean_nat_dec_lt(v___x_3824_, v___x_3825_);
if (v___x_3826_ == 0)
{
uint8_t v___x_3827_; 
v___x_3827_ = 1;
return v___x_3827_;
}
else
{
lean_object* v___x_3828_; lean_object* v_fst_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; uint8_t v___x_3832_; 
v___x_3828_ = lean_array_fget_borrowed(v_sections_3823_, v___x_3824_);
v_fst_3829_ = lean_ctor_get(v___x_3828_, 0);
v___x_3830_ = lean_unsigned_to_nat(1u);
v___x_3831_ = lean_nat_add(v_level_3821_, v___x_3830_);
v___x_3832_ = lean_nat_dec_le(v_fst_3829_, v___x_3831_);
lean_dec(v___x_3831_);
return v___x_3832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_canNestIn___boxed(lean_object* v_level_3833_, lean_object* v_snippet_3834_){
_start:
{
uint8_t v_res_3835_; lean_object* v_r_3836_; 
v_res_3835_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_level_3833_, v_snippet_3834_);
lean_dec_ref(v_snippet_3834_);
lean_dec(v_level_3833_);
v_r_3836_ = lean_box(v_res_3835_);
return v_r_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting(lean_object* v_snippet_3837_){
_start:
{
lean_object* v_sections_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; uint8_t v___x_3842_; 
v_sections_3838_ = lean_ctor_get(v_snippet_3837_, 1);
v___x_3839_ = lean_array_get_size(v_sections_3838_);
v___x_3840_ = lean_unsigned_to_nat(1u);
v___x_3841_ = lean_nat_sub(v___x_3839_, v___x_3840_);
v___x_3842_ = lean_nat_dec_lt(v___x_3841_, v___x_3839_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3843_; 
lean_dec(v___x_3841_);
v___x_3843_ = lean_box(0);
return v___x_3843_;
}
else
{
lean_object* v___x_3844_; lean_object* v_fst_3845_; lean_object* v___x_3846_; 
v___x_3844_ = lean_array_fget_borrowed(v_sections_3838_, v___x_3841_);
lean_dec(v___x_3841_);
v_fst_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_fst_3845_);
v___x_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3846_, 0, v_fst_3845_);
return v___x_3846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting___boxed(lean_object* v_snippet_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_3847_);
lean_dec_ref(v_snippet_3847_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addBlock(lean_object* v_snippet_3849_, lean_object* v_block_3850_){
_start:
{
lean_object* v_text_3851_; lean_object* v_sections_3852_; lean_object* v_declarationRange_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; uint8_t v___x_3856_; 
v_text_3851_ = lean_ctor_get(v_snippet_3849_, 0);
v_sections_3852_ = lean_ctor_get(v_snippet_3849_, 1);
v_declarationRange_3853_ = lean_ctor_get(v_snippet_3849_, 2);
v___x_3854_ = lean_array_get_size(v_sections_3852_);
v___x_3855_ = lean_unsigned_to_nat(0u);
v___x_3856_ = lean_nat_dec_eq(v___x_3854_, v___x_3855_);
if (v___x_3856_ == 0)
{
lean_object* v___x_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; 
v___x_3857_ = lean_unsigned_to_nat(1u);
v___x_3858_ = lean_nat_sub(v___x_3854_, v___x_3857_);
v___x_3859_ = lean_nat_dec_lt(v___x_3858_, v___x_3854_);
if (v___x_3859_ == 0)
{
lean_dec(v___x_3858_);
lean_dec_ref(v_block_3850_);
return v_snippet_3849_;
}
else
{
lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3903_; 
lean_inc_ref(v_declarationRange_3853_);
lean_inc_ref(v_sections_3852_);
lean_inc_ref(v_text_3851_);
v_isSharedCheck_3903_ = !lean_is_exclusive(v_snippet_3849_);
if (v_isSharedCheck_3903_ == 0)
{
lean_object* v_unused_3904_; lean_object* v_unused_3905_; lean_object* v_unused_3906_; 
v_unused_3904_ = lean_ctor_get(v_snippet_3849_, 2);
lean_dec(v_unused_3904_);
v_unused_3905_ = lean_ctor_get(v_snippet_3849_, 1);
lean_dec(v_unused_3905_);
v_unused_3906_ = lean_ctor_get(v_snippet_3849_, 0);
lean_dec(v_unused_3906_);
v___x_3861_ = v_snippet_3849_;
v_isShared_3862_ = v_isSharedCheck_3903_;
goto v_resetjp_3860_;
}
else
{
lean_dec(v_snippet_3849_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3903_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v_v_3863_; lean_object* v_snd_3864_; lean_object* v_snd_3865_; lean_object* v_fst_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3901_; 
v_v_3863_ = lean_array_fget(v_sections_3852_, v___x_3858_);
v_snd_3864_ = lean_ctor_get(v_v_3863_, 1);
lean_inc(v_snd_3864_);
v_snd_3865_ = lean_ctor_get(v_snd_3864_, 1);
lean_inc(v_snd_3865_);
v_fst_3866_ = lean_ctor_get(v_v_3863_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v_v_3863_);
if (v_isSharedCheck_3901_ == 0)
{
lean_object* v_unused_3902_; 
v_unused_3902_ = lean_ctor_get(v_v_3863_, 1);
lean_dec(v_unused_3902_);
v___x_3868_ = v_v_3863_;
v_isShared_3869_ = v_isSharedCheck_3901_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_fst_3866_);
lean_dec(v_v_3863_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3901_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v_fst_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3899_; 
v_fst_3870_ = lean_ctor_get(v_snd_3864_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v_snd_3864_);
if (v_isSharedCheck_3899_ == 0)
{
lean_object* v_unused_3900_; 
v_unused_3900_ = lean_ctor_get(v_snd_3864_, 1);
lean_dec(v_unused_3900_);
v___x_3872_ = v_snd_3864_;
v_isShared_3873_ = v_isSharedCheck_3899_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_fst_3870_);
lean_dec(v_snd_3864_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3899_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v_title_3874_; lean_object* v_titleString_3875_; lean_object* v_metadata_3876_; lean_object* v_content_3877_; lean_object* v_subParts_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3898_; 
v_title_3874_ = lean_ctor_get(v_snd_3865_, 0);
v_titleString_3875_ = lean_ctor_get(v_snd_3865_, 1);
v_metadata_3876_ = lean_ctor_get(v_snd_3865_, 2);
v_content_3877_ = lean_ctor_get(v_snd_3865_, 3);
v_subParts_3878_ = lean_ctor_get(v_snd_3865_, 4);
v_isSharedCheck_3898_ = !lean_is_exclusive(v_snd_3865_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3880_ = v_snd_3865_;
v_isShared_3881_ = v_isSharedCheck_3898_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_subParts_3878_);
lean_inc(v_content_3877_);
lean_inc(v_metadata_3876_);
lean_inc(v_titleString_3875_);
lean_inc(v_title_3874_);
lean_dec(v_snd_3865_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3898_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3882_; lean_object* v_xs_x27_3883_; lean_object* v___x_3884_; lean_object* v___x_3886_; 
v___x_3882_ = lean_box(0);
v_xs_x27_3883_ = lean_array_fset(v_sections_3852_, v___x_3858_, v___x_3882_);
v___x_3884_ = lean_array_push(v_content_3877_, v_block_3850_);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 3, v___x_3884_);
v___x_3886_ = v___x_3880_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_title_3874_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v_titleString_3875_);
lean_ctor_set(v_reuseFailAlloc_3897_, 2, v_metadata_3876_);
lean_ctor_set(v_reuseFailAlloc_3897_, 3, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3897_, 4, v_subParts_3878_);
v___x_3886_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
lean_object* v___x_3888_; 
if (v_isShared_3873_ == 0)
{
lean_ctor_set(v___x_3872_, 1, v___x_3886_);
v___x_3888_ = v___x_3872_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_fst_3870_);
lean_ctor_set(v_reuseFailAlloc_3896_, 1, v___x_3886_);
v___x_3888_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_object* v___x_3890_; 
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 1, v___x_3888_);
v___x_3890_ = v___x_3868_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_fst_3866_);
lean_ctor_set(v_reuseFailAlloc_3895_, 1, v___x_3888_);
v___x_3890_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
lean_object* v___x_3891_; lean_object* v___x_3893_; 
v___x_3891_ = lean_array_fset(v_xs_x27_3883_, v___x_3858_, v___x_3890_);
lean_dec(v___x_3858_);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 1, v___x_3891_);
v___x_3893_ = v___x_3861_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_text_3851_);
lean_ctor_set(v_reuseFailAlloc_3894_, 1, v___x_3891_);
lean_ctor_set(v_reuseFailAlloc_3894_, 2, v_declarationRange_3853_);
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
}
}
}
}
}
}
else
{
lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3914_; 
lean_inc_ref(v_declarationRange_3853_);
lean_inc_ref(v_sections_3852_);
lean_inc_ref(v_text_3851_);
v_isSharedCheck_3914_ = !lean_is_exclusive(v_snippet_3849_);
if (v_isSharedCheck_3914_ == 0)
{
lean_object* v_unused_3915_; lean_object* v_unused_3916_; lean_object* v_unused_3917_; 
v_unused_3915_ = lean_ctor_get(v_snippet_3849_, 2);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_snippet_3849_, 1);
lean_dec(v_unused_3916_);
v_unused_3917_ = lean_ctor_get(v_snippet_3849_, 0);
lean_dec(v_unused_3917_);
v___x_3908_ = v_snippet_3849_;
v_isShared_3909_ = v_isSharedCheck_3914_;
goto v_resetjp_3907_;
}
else
{
lean_dec(v_snippet_3849_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3914_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3910_; lean_object* v___x_3912_; 
v___x_3910_ = lean_array_push(v_text_3851_, v_block_3850_);
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v___x_3910_);
v___x_3912_ = v___x_3908_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3910_);
lean_ctor_set(v_reuseFailAlloc_3913_, 1, v_sections_3852_);
lean_ctor_set(v_reuseFailAlloc_3913_, 2, v_declarationRange_3853_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addPart(lean_object* v_snippet_3918_, lean_object* v_level_3919_, lean_object* v_range_3920_, lean_object* v_part_3921_){
_start:
{
lean_object* v_text_3922_; lean_object* v_sections_3923_; lean_object* v_declarationRange_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3934_; 
v_text_3922_ = lean_ctor_get(v_snippet_3918_, 0);
v_sections_3923_ = lean_ctor_get(v_snippet_3918_, 1);
v_declarationRange_3924_ = lean_ctor_get(v_snippet_3918_, 2);
v_isSharedCheck_3934_ = !lean_is_exclusive(v_snippet_3918_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3926_ = v_snippet_3918_;
v_isShared_3927_ = v_isSharedCheck_3934_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_declarationRange_3924_);
lean_inc(v_sections_3923_);
lean_inc(v_text_3922_);
lean_dec(v_snippet_3918_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3934_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3932_; 
v___x_3928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3928_, 0, v_range_3920_);
lean_ctor_set(v___x_3928_, 1, v_part_3921_);
v___x_3929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3929_, 0, v_level_3919_);
lean_ctor_set(v___x_3929_, 1, v___x_3928_);
v___x_3930_ = lean_array_push(v_sections_3923_, v___x_3929_);
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 1, v___x_3930_);
v___x_3932_ = v___x_3926_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_text_3922_);
lean_ctor_set(v_reuseFailAlloc_3933_, 1, v___x_3930_);
lean_ctor_set(v_reuseFailAlloc_3933_, 2, v_declarationRange_3924_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__0(lean_object* v___x_3935_, lean_object* v___x_3936_, lean_object* v_x_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_snd_3939_; lean_object* v_fst_3940_; lean_object* v_snd_3941_; lean_object* v___x_3942_; 
v_snd_3939_ = lean_ctor_get(v_x_3937_, 1);
lean_inc(v_snd_3939_);
v_fst_3940_ = lean_ctor_get(v_x_3937_, 0);
lean_inc(v_fst_3940_);
lean_dec_ref(v_x_3937_);
v_snd_3941_ = lean_ctor_get(v_snd_3939_, 1);
lean_inc(v_snd_3941_);
lean_dec(v_snd_3939_);
v___x_3942_ = l_Lean_Doc_partMarkdown___redArg(v___x_3935_, v___x_3936_, v_fst_3940_, v_snd_3941_, v___y_3938_);
lean_dec(v_fst_3940_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMarkdownSnippet___lam__1(lean_object* v___x_3943_, lean_object* v___x_3944_, lean_object* v___x_3945_, lean_object* v___f_3946_, lean_object* v_x_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v_text_3949_; lean_object* v_sections_3950_; lean_object* v___x_3951_; size_t v_sz_3952_; size_t v___x_3953_; lean_object* v___x_506__overap_3954_; lean_object* v___x_3955_; lean_object* v_fst_3956_; lean_object* v_snd_3957_; size_t v_sz_3958_; lean_object* v___x_509__overap_3959_; lean_object* v___x_3960_; lean_object* v_fst_3961_; lean_object* v_snd_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3971_; 
v_text_3949_ = lean_ctor_get(v_x_3947_, 0);
lean_inc_ref(v_text_3949_);
v_sections_3950_ = lean_ctor_get(v_x_3947_, 1);
lean_inc_ref(v_sections_3950_);
lean_dec_ref(v_x_3947_);
v___x_3951_ = lean_alloc_closure((void*)(l_Lean_Doc_instToMarkdownBlockOfMarkdownInlineOfMarkdownBlock___private__1), 6, 4);
lean_closure_set(v___x_3951_, 0, lean_box(0));
lean_closure_set(v___x_3951_, 1, lean_box(0));
lean_closure_set(v___x_3951_, 2, v___x_3943_);
lean_closure_set(v___x_3951_, 3, v___x_3944_);
v_sz_3952_ = lean_array_size(v_text_3949_);
v___x_3953_ = ((size_t)0ULL);
lean_inc_ref(v___x_3945_);
v___x_506__overap_3954_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3945_, v___x_3951_, v_sz_3952_, v___x_3953_, v_text_3949_);
v___x_3955_ = lean_apply_1(v___x_506__overap_3954_, v___y_3948_);
v_fst_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc(v_fst_3956_);
v_snd_3957_ = lean_ctor_get(v___x_3955_, 1);
lean_inc(v_snd_3957_);
lean_dec_ref(v___x_3955_);
v_sz_3958_ = lean_array_size(v_sections_3950_);
v___x_509__overap_3959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3945_, v___f_3946_, v_sz_3958_, v___x_3953_, v_sections_3950_);
v___x_3960_ = lean_apply_1(v___x_509__overap_3959_, v_snd_3957_);
v_fst_3961_ = lean_ctor_get(v___x_3960_, 0);
v_snd_3962_ = lean_ctor_get(v___x_3960_, 1);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3964_ = v___x_3960_;
v_isShared_3965_ = v_isSharedCheck_3971_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_snd_3962_);
lean_inc(v_fst_3961_);
lean_dec(v___x_3960_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3971_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3969_; 
v___x_3966_ = l_Array_append___redArg(v_fst_3956_, v_fst_3961_);
lean_dec(v_fst_3961_);
v___x_3967_ = l_Lean_Doc_joinBlocks(v___x_3966_);
lean_dec_ref(v___x_3966_);
if (v_isShared_3965_ == 0)
{
lean_ctor_set(v___x_3964_, 0, v___x_3967_);
v___x_3969_ = v___x_3964_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3967_);
lean_ctor_set(v_reuseFailAlloc_3970_, 1, v_snd_3962_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0(void){
_start:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3981_ = lean_unsigned_to_nat(32u);
v___x_3982_ = lean_mk_empty_array_with_capacity(v___x_3981_);
v___x_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3982_);
return v___x_3983_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1(void){
_start:
{
size_t v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3984_ = ((size_t)5ULL);
v___x_3985_ = lean_unsigned_to_nat(0u);
v___x_3986_ = lean_unsigned_to_nat(32u);
v___x_3987_ = lean_mk_empty_array_with_capacity(v___x_3986_);
v___x_3988_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_3989_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3989_, 0, v___x_3988_);
lean_ctor_set(v___x_3989_, 1, v___x_3987_);
lean_ctor_set(v___x_3989_, 2, v___x_3985_);
lean_ctor_set(v___x_3989_, 3, v___x_3985_);
lean_ctor_set_usize(v___x_3989_, 4, v___x_3984_);
return v___x_3989_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default(void){
_start:
{
lean_object* v___x_3990_; 
v___x_3990_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__1, &l_Lean_instInhabitedVersoModuleDocs_default___closed__1_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1);
return v___x_3990_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs(void){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_Lean_instInhabitedVersoModuleDocs_default;
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(lean_object* v_as_3992_, lean_object* v_i_3993_){
_start:
{
lean_object* v_zero_3994_; uint8_t v_isZero_3995_; 
v_zero_3994_ = lean_unsigned_to_nat(0u);
v_isZero_3995_ = lean_nat_dec_eq(v_i_3993_, v_zero_3994_);
if (v_isZero_3995_ == 1)
{
lean_object* v___x_3996_; 
lean_dec(v_i_3993_);
v___x_3996_ = lean_box(0);
return v___x_3996_;
}
else
{
lean_object* v_one_3997_; lean_object* v_n_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v_one_3997_ = lean_unsigned_to_nat(1u);
v_n_3998_ = lean_nat_sub(v_i_3993_, v_one_3997_);
lean_dec(v_i_3993_);
v___x_3999_ = lean_array_fget_borrowed(v_as_3992_, v_n_3998_);
v___x_4000_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v___x_3999_);
if (lean_obj_tag(v___x_4000_) == 0)
{
v_i_3993_ = v_n_3998_;
goto _start;
}
else
{
lean_dec(v_n_3998_);
return v___x_4000_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg___boxed(lean_object* v_as_4002_, lean_object* v_i_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_as_4002_, v_i_4003_);
lean_dec_ref(v_as_4002_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(lean_object* v_as_4005_, lean_object* v_i_4006_){
_start:
{
lean_object* v_zero_4007_; uint8_t v_isZero_4008_; 
v_zero_4007_ = lean_unsigned_to_nat(0u);
v_isZero_4008_ = lean_nat_dec_eq(v_i_4006_, v_zero_4007_);
if (v_isZero_4008_ == 1)
{
lean_object* v___x_4009_; 
lean_dec(v_i_4006_);
v___x_4009_ = lean_box(0);
return v___x_4009_;
}
else
{
lean_object* v_one_4010_; lean_object* v_n_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v_one_4010_ = lean_unsigned_to_nat(1u);
v_n_4011_ = lean_nat_sub(v_i_4006_, v_one_4010_);
lean_dec(v_i_4006_);
v___x_4012_ = lean_array_fget_borrowed(v_as_4005_, v_n_4011_);
v___x_4013_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v___x_4012_);
if (lean_obj_tag(v___x_4013_) == 0)
{
v_i_4006_ = v_n_4011_;
goto _start;
}
else
{
lean_dec(v_n_4011_);
return v___x_4013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(lean_object* v_x_4015_){
_start:
{
if (lean_obj_tag(v_x_4015_) == 0)
{
lean_object* v_cs_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v_cs_4016_ = lean_ctor_get(v_x_4015_, 0);
v___x_4017_ = lean_array_get_size(v_cs_4016_);
v___x_4018_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_cs_4016_, v___x_4017_);
return v___x_4018_;
}
else
{
lean_object* v_vs_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v_vs_4019_ = lean_ctor_get(v_x_4015_, 0);
v___x_4020_ = lean_array_get_size(v_vs_4019_);
v___x_4021_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_vs_4019_, v___x_4020_);
return v___x_4021_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1___boxed(lean_object* v_x_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v_x_4022_);
lean_dec_ref(v_x_4022_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_as_4024_, lean_object* v_i_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_as_4024_, v_i_4025_);
lean_dec_ref(v_as_4024_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(lean_object* v_t_4027_){
_start:
{
lean_object* v_root_4028_; lean_object* v_tail_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v_root_4028_ = lean_ctor_get(v_t_4027_, 0);
v_tail_4029_ = lean_ctor_get(v_t_4027_, 1);
v___x_4030_ = lean_array_get_size(v_tail_4029_);
v___x_4031_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_tail_4029_, v___x_4030_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v___x_4032_; 
v___x_4032_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v_root_4028_);
return v___x_4032_;
}
else
{
return v___x_4031_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0___boxed(lean_object* v_t_4033_){
_start:
{
lean_object* v_res_4034_; 
v_res_4034_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_t_4033_);
lean_dec_ref(v_t_4033_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_terminalNesting(lean_object* v_x_4035_){
_start:
{
lean_object* v___x_4036_; 
v___x_4036_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_x_4035_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_terminalNesting___boxed(lean_object* v_x_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Lean_VersoModuleDocs_terminalNesting(v_x_4037_);
lean_dec_ref(v_x_4037_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0(lean_object* v_as_4039_, lean_object* v_i_4040_, lean_object* v_a_4041_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_as_4039_, v_i_4040_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___boxed(lean_object* v_as_4043_, lean_object* v_i_4044_, lean_object* v_a_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0(v_as_4043_, v_i_4044_, v_a_4045_);
lean_dec_ref(v_as_4043_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2(lean_object* v_as_4047_, lean_object* v_i_4048_, lean_object* v_a_4049_){
_start:
{
lean_object* v___x_4050_; 
v___x_4050_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_as_4047_, v_i_4048_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___boxed(lean_object* v_as_4051_, lean_object* v_i_4052_, lean_object* v_a_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2(v_as_4051_, v_i_4052_, v_a_4053_);
lean_dec_ref(v_as_4051_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0(lean_object* v___x_4061_, lean_object* v_v_4062_, lean_object* v_x_4063_){
_start:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; uint8_t v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4064_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___x_4065_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_4066_ = lean_box(1);
v___x_4067_ = ((lean_object*)(l_Lean_instReprVersoModuleDocs___lam__0___closed__2));
v___x_4068_ = l_Lean_PersistentArray_toArray___redArg(v_v_4062_);
v___x_4069_ = l_Array_repr___redArg(v___x_4061_, v___x_4068_);
v___x_4070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4067_);
lean_ctor_set(v___x_4070_, 1, v___x_4069_);
v___x_4071_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4064_);
lean_ctor_set(v___x_4071_, 1, v___x_4070_);
v___x_4072_ = 0;
v___x_4073_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4073_, 0, v___x_4071_);
lean_ctor_set_uint8(v___x_4073_, sizeof(void*)*1, v___x_4072_);
lean_inc_ref(v___x_4073_);
v___x_4074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4065_);
lean_ctor_set(v___x_4074_, 1, v___x_4073_);
v___x_4075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4074_);
lean_ctor_set(v___x_4075_, 1, v___x_4066_);
v___x_4076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
lean_ctor_set(v___x_4076_, 1, v___x_4073_);
v___x_4077_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_4078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4076_);
lean_ctor_set(v___x_4078_, 1, v___x_4077_);
v___x_4079_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4064_);
lean_ctor_set(v___x_4079_, 1, v___x_4078_);
v___x_4080_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4080_, 0, v___x_4079_);
lean_ctor_set_uint8(v___x_4080_, sizeof(void*)*1, v___x_4072_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0___boxed(lean_object* v___x_4081_, lean_object* v_v_4082_, lean_object* v_x_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Lean_instReprVersoModuleDocs___lam__0(v___x_4081_, v_v_4082_, v_x_4083_);
lean_dec(v_x_4083_);
lean_dec_ref(v_v_4082_);
return v_res_4084_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_isEmpty(lean_object* v_docs_4088_){
_start:
{
uint8_t v___x_4089_; 
v___x_4089_ = l_Lean_PersistentArray_isEmpty___redArg(v_docs_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_isEmpty___boxed(lean_object* v_docs_4090_){
_start:
{
uint8_t v_res_4091_; lean_object* v_r_4092_; 
v_res_4091_ = l_Lean_VersoModuleDocs_isEmpty(v_docs_4090_);
lean_dec_ref(v_docs_4090_);
v_r_4092_ = lean_box(v_res_4091_);
return v_r_4092_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_canAdd(lean_object* v_docs_4093_, lean_object* v_snippet_4094_){
_start:
{
lean_object* v___x_4095_; 
v___x_4095_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_4093_);
if (lean_obj_tag(v___x_4095_) == 1)
{
lean_object* v_val_4096_; uint8_t v___x_4097_; 
v_val_4096_ = lean_ctor_get(v___x_4095_, 0);
lean_inc(v_val_4096_);
lean_dec_ref_known(v___x_4095_, 1);
v___x_4097_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_4096_, v_snippet_4094_);
lean_dec(v_val_4096_);
return v___x_4097_;
}
else
{
uint8_t v___x_4098_; 
lean_dec(v___x_4095_);
v___x_4098_ = 1;
return v___x_4098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_canAdd___boxed(lean_object* v_docs_4099_, lean_object* v_snippet_4100_){
_start:
{
uint8_t v_res_4101_; lean_object* v_r_4102_; 
v_res_4101_ = l_Lean_VersoModuleDocs_canAdd(v_docs_4099_, v_snippet_4100_);
lean_dec_ref(v_snippet_4100_);
lean_dec_ref(v_docs_4099_);
v_r_4102_ = lean_box(v_res_4101_);
return v_r_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add(lean_object* v_docs_4106_, lean_object* v_snippet_4107_){
_start:
{
uint8_t v___x_4108_; 
v___x_4108_ = l_Lean_VersoModuleDocs_canAdd(v_docs_4106_, v_snippet_4107_);
if (v___x_4108_ == 0)
{
lean_object* v___x_4109_; 
lean_dec_ref(v_snippet_4107_);
lean_dec_ref(v_docs_4106_);
v___x_4109_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__1));
return v___x_4109_;
}
else
{
lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4110_ = l_Lean_PersistentArray_push___redArg(v_docs_4106_, v_snippet_4107_);
v___x_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4110_);
return v___x_4111_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(lean_object* v_msg_4112_){
_start:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4113_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_4114_ = lean_panic_fn_borrowed(v___x_4113_, v_msg_4112_);
return v___x_4114_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_add_x21___closed__2(void){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4117_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__0));
v___x_4118_ = lean_unsigned_to_nat(4u);
v___x_4119_ = lean_unsigned_to_nat(324u);
v___x_4120_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__1));
v___x_4121_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__0));
v___x_4122_ = l_mkPanicMessageWithDecl(v___x_4121_, v___x_4120_, v___x_4119_, v___x_4118_, v___x_4117_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add_x21(lean_object* v_docs_4123_, lean_object* v_snippet_4124_){
_start:
{
lean_object* v___x_4125_; 
v___x_4125_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_4123_);
if (lean_obj_tag(v___x_4125_) == 1)
{
lean_object* v_val_4126_; uint8_t v___x_4127_; 
v_val_4126_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_val_4126_);
lean_dec_ref_known(v___x_4125_, 1);
v___x_4127_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_4126_, v_snippet_4124_);
lean_dec(v_val_4126_);
if (v___x_4127_ == 0)
{
lean_object* v___x_4128_; lean_object* v___x_4129_; 
lean_dec_ref(v_snippet_4124_);
lean_dec_ref(v_docs_4123_);
v___x_4128_ = lean_obj_once(&l_Lean_VersoModuleDocs_add_x21___closed__2, &l_Lean_VersoModuleDocs_add_x21___closed__2_once, _init_l_Lean_VersoModuleDocs_add_x21___closed__2);
v___x_4129_ = l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(v___x_4128_);
return v___x_4129_;
}
else
{
lean_object* v___x_4130_; 
v___x_4130_ = l_Lean_PersistentArray_push___redArg(v_docs_4123_, v_snippet_4124_);
return v___x_4130_;
}
}
else
{
lean_object* v___x_4131_; 
lean_dec(v___x_4125_);
v___x_4131_ = l_Lean_PersistentArray_push___redArg(v_docs_4123_, v_snippet_4124_);
return v___x_4131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(lean_object* v_ctx_4132_){
_start:
{
lean_object* v_context_4133_; lean_object* v___x_4134_; 
v_context_4133_ = lean_ctor_get(v_ctx_4132_, 2);
v___x_4134_ = lean_array_get_size(v_context_4133_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level___boxed(lean_object* v_ctx_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_4135_);
lean_dec_ref(v_ctx_4135_);
return v_res_4136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(lean_object* v_ctx_4140_){
_start:
{
lean_object* v_content_4141_; lean_object* v_priorParts_4142_; lean_object* v_context_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4166_; 
v_content_4141_ = lean_ctor_get(v_ctx_4140_, 0);
v_priorParts_4142_ = lean_ctor_get(v_ctx_4140_, 1);
v_context_4143_ = lean_ctor_get(v_ctx_4140_, 2);
v_isSharedCheck_4166_ = !lean_is_exclusive(v_ctx_4140_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4145_ = v_ctx_4140_;
v_isShared_4146_ = v_isSharedCheck_4166_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_context_4143_);
lean_inc(v_priorParts_4142_);
lean_inc(v_content_4141_);
lean_dec(v_ctx_4140_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4166_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4147_; lean_object* v___x_4148_; uint8_t v___x_4149_; 
v___x_4147_ = lean_array_get_size(v_context_4143_);
v___x_4148_ = lean_unsigned_to_nat(0u);
v___x_4149_ = lean_nat_dec_eq(v___x_4147_, v___x_4148_);
if (v___x_4149_ == 0)
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v_last_4152_; lean_object* v_content_4153_; lean_object* v_priorParts_4154_; lean_object* v_titleString_4155_; lean_object* v_title_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4162_; 
v___x_4150_ = lean_unsigned_to_nat(1u);
v___x_4151_ = lean_nat_sub(v___x_4147_, v___x_4150_);
v_last_4152_ = lean_array_fget_borrowed(v_context_4143_, v___x_4151_);
lean_dec(v___x_4151_);
v_content_4153_ = lean_ctor_get(v_last_4152_, 0);
lean_inc_ref(v_content_4153_);
v_priorParts_4154_ = lean_ctor_get(v_last_4152_, 1);
v_titleString_4155_ = lean_ctor_get(v_last_4152_, 2);
v_title_4156_ = lean_ctor_get(v_last_4152_, 3);
v___x_4157_ = lean_box(0);
lean_inc_ref(v_titleString_4155_);
lean_inc_ref(v_title_4156_);
v___x_4158_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4158_, 0, v_title_4156_);
lean_ctor_set(v___x_4158_, 1, v_titleString_4155_);
lean_ctor_set(v___x_4158_, 2, v___x_4157_);
lean_ctor_set(v___x_4158_, 3, v_content_4141_);
lean_ctor_set(v___x_4158_, 4, v_priorParts_4142_);
lean_inc_ref(v_priorParts_4154_);
v___x_4159_ = lean_array_push(v_priorParts_4154_, v___x_4158_);
v___x_4160_ = lean_array_pop(v_context_4143_);
if (v_isShared_4146_ == 0)
{
lean_ctor_set(v___x_4145_, 2, v___x_4160_);
lean_ctor_set(v___x_4145_, 1, v___x_4159_);
lean_ctor_set(v___x_4145_, 0, v_content_4153_);
v___x_4162_ = v___x_4145_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_content_4153_);
lean_ctor_set(v_reuseFailAlloc_4164_, 1, v___x_4159_);
lean_ctor_set(v_reuseFailAlloc_4164_, 2, v___x_4160_);
v___x_4162_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
lean_object* v___x_4163_; 
v___x_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
return v___x_4163_;
}
}
else
{
lean_object* v___x_4165_; 
lean_del_object(v___x_4145_);
lean_dec_ref(v_context_4143_);
lean_dec_ref(v_priorParts_4142_);
lean_dec_ref(v_content_4141_);
v___x_4165_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__1));
return v___x_4165_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(lean_object* v_ctx_4167_){
_start:
{
lean_object* v_context_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; uint8_t v___x_4171_; 
v_context_4168_ = lean_ctor_get(v_ctx_4167_, 2);
v___x_4169_ = lean_array_get_size(v_context_4168_);
v___x_4170_ = lean_unsigned_to_nat(0u);
v___x_4171_ = lean_nat_dec_eq(v___x_4169_, v___x_4170_);
if (v___x_4171_ == 0)
{
lean_object* v___x_4172_; 
v___x_4172_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_4167_);
if (lean_obj_tag(v___x_4172_) == 0)
{
return v___x_4172_;
}
else
{
lean_object* v_a_4173_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4173_);
lean_dec_ref_known(v___x_4172_, 1);
v_ctx_4167_ = v_a_4173_;
goto _start;
}
}
else
{
lean_object* v___x_4175_; 
v___x_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4175_, 0, v_ctx_4167_);
return v___x_4175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(lean_object* v_ctx_4178_, lean_object* v_partLevel_4179_, lean_object* v_part_4180_){
_start:
{
lean_object* v___x_4181_; uint8_t v___x_4182_; 
v___x_4181_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_4178_);
v___x_4182_ = lean_nat_dec_lt(v___x_4181_, v_partLevel_4179_);
if (v___x_4182_ == 0)
{
uint8_t v___x_4183_; 
v___x_4183_ = lean_nat_dec_eq(v_partLevel_4179_, v___x_4181_);
lean_dec(v___x_4181_);
if (v___x_4183_ == 0)
{
lean_object* v___x_4184_; 
v___x_4184_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_4178_);
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_dec_ref(v_part_4180_);
lean_dec(v_partLevel_4179_);
return v___x_4184_;
}
else
{
lean_object* v_a_4185_; 
v_a_4185_ = lean_ctor_get(v___x_4184_, 0);
lean_inc(v_a_4185_);
lean_dec_ref_known(v___x_4184_, 1);
v_ctx_4178_ = v_a_4185_;
goto _start;
}
}
else
{
lean_object* v_content_4187_; lean_object* v_priorParts_4188_; lean_object* v_context_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4198_; 
lean_dec(v_partLevel_4179_);
v_content_4187_ = lean_ctor_get(v_ctx_4178_, 0);
v_priorParts_4188_ = lean_ctor_get(v_ctx_4178_, 1);
v_context_4189_ = lean_ctor_get(v_ctx_4178_, 2);
v_isSharedCheck_4198_ = !lean_is_exclusive(v_ctx_4178_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4191_ = v_ctx_4178_;
v_isShared_4192_ = v_isSharedCheck_4198_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_context_4189_);
lean_inc(v_priorParts_4188_);
lean_inc(v_content_4187_);
lean_dec(v_ctx_4178_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4198_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4193_; lean_object* v___x_4195_; 
v___x_4193_ = lean_array_push(v_priorParts_4188_, v_part_4180_);
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 1, v___x_4193_);
v___x_4195_ = v___x_4191_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_content_4187_);
lean_ctor_set(v_reuseFailAlloc_4197_, 1, v___x_4193_);
lean_ctor_set(v_reuseFailAlloc_4197_, 2, v_context_4189_);
v___x_4195_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
lean_object* v___x_4196_; 
v___x_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
return v___x_4196_;
}
}
}
}
else
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
lean_dec_ref(v_part_4180_);
lean_dec_ref(v_ctx_4178_);
v___x_4199_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__0));
v___x_4200_ = l_Nat_reprFast(v___x_4181_);
v___x_4201_ = lean_string_append(v___x_4199_, v___x_4200_);
lean_dec_ref(v___x_4200_);
v___x_4202_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__1));
v___x_4203_ = lean_string_append(v___x_4201_, v___x_4202_);
v___x_4204_ = l_Nat_reprFast(v_partLevel_4179_);
v___x_4205_ = lean_string_append(v___x_4203_, v___x_4204_);
lean_dec_ref(v___x_4204_);
v___x_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4205_);
return v___x_4206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(lean_object* v_ctx_4210_, lean_object* v_blocks_4211_){
_start:
{
lean_object* v_content_4212_; lean_object* v_priorParts_4213_; lean_object* v_context_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4227_; 
v_content_4212_ = lean_ctor_get(v_ctx_4210_, 0);
v_priorParts_4213_ = lean_ctor_get(v_ctx_4210_, 1);
v_context_4214_ = lean_ctor_get(v_ctx_4210_, 2);
v_isSharedCheck_4227_ = !lean_is_exclusive(v_ctx_4210_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4216_ = v_ctx_4210_;
v_isShared_4217_ = v_isSharedCheck_4227_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_context_4214_);
lean_inc(v_priorParts_4213_);
lean_inc(v_content_4212_);
lean_dec(v_ctx_4210_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4227_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; 
v___x_4218_ = lean_array_get_size(v_priorParts_4213_);
v___x_4219_ = lean_unsigned_to_nat(0u);
v___x_4220_ = lean_nat_dec_eq(v___x_4218_, v___x_4219_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; 
lean_del_object(v___x_4216_);
lean_dec_ref(v_context_4214_);
lean_dec_ref(v_priorParts_4213_);
lean_dec_ref(v_content_4212_);
v___x_4221_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__1));
return v___x_4221_;
}
else
{
lean_object* v___x_4222_; lean_object* v___x_4224_; 
v___x_4222_ = l_Array_append___redArg(v_content_4212_, v_blocks_4211_);
if (v_isShared_4217_ == 0)
{
lean_ctor_set(v___x_4216_, 0, v___x_4222_);
v___x_4224_ = v___x_4216_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4222_);
lean_ctor_set(v_reuseFailAlloc_4226_, 1, v_priorParts_4213_);
lean_ctor_set(v_reuseFailAlloc_4226_, 2, v_context_4214_);
v___x_4224_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
lean_object* v___x_4225_; 
v___x_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4224_);
return v___x_4225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___boxed(lean_object* v_ctx_4228_, lean_object* v_blocks_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_4228_, v_blocks_4229_);
lean_dec_ref(v_blocks_4229_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(lean_object* v_as_4231_, size_t v_sz_4232_, size_t v_i_4233_, lean_object* v_b_4234_){
_start:
{
uint8_t v___x_4235_; 
v___x_4235_ = lean_usize_dec_lt(v_i_4233_, v_sz_4232_);
if (v___x_4235_ == 0)
{
lean_object* v___x_4236_; 
v___x_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4236_, 0, v_b_4234_);
return v___x_4236_;
}
else
{
lean_object* v_a_4237_; lean_object* v_snd_4238_; lean_object* v_fst_4239_; lean_object* v_snd_4240_; lean_object* v___x_4241_; 
v_a_4237_ = lean_array_uget_borrowed(v_as_4231_, v_i_4233_);
v_snd_4238_ = lean_ctor_get(v_a_4237_, 1);
v_fst_4239_ = lean_ctor_get(v_a_4237_, 0);
v_snd_4240_ = lean_ctor_get(v_snd_4238_, 1);
lean_inc(v_snd_4240_);
lean_inc(v_fst_4239_);
v___x_4241_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(v_b_4234_, v_fst_4239_, v_snd_4240_);
if (lean_obj_tag(v___x_4241_) == 0)
{
return v___x_4241_;
}
else
{
lean_object* v_a_4242_; size_t v___x_4243_; size_t v___x_4244_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4242_);
lean_dec_ref_known(v___x_4241_, 1);
v___x_4243_ = ((size_t)1ULL);
v___x_4244_ = lean_usize_add(v_i_4233_, v___x_4243_);
v_i_4233_ = v___x_4244_;
v_b_4234_ = v_a_4242_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0___boxed(lean_object* v_as_4246_, lean_object* v_sz_4247_, lean_object* v_i_4248_, lean_object* v_b_4249_){
_start:
{
size_t v_sz_boxed_4250_; size_t v_i_boxed_4251_; lean_object* v_res_4252_; 
v_sz_boxed_4250_ = lean_unbox_usize(v_sz_4247_);
lean_dec(v_sz_4247_);
v_i_boxed_4251_ = lean_unbox_usize(v_i_4248_);
lean_dec(v_i_4248_);
v_res_4252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_as_4246_, v_sz_boxed_4250_, v_i_boxed_4251_, v_b_4249_);
lean_dec_ref(v_as_4246_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(lean_object* v_ctx_4253_, lean_object* v_snippet_4254_){
_start:
{
lean_object* v_text_4255_; lean_object* v_sections_4256_; lean_object* v___x_4257_; 
v_text_4255_ = lean_ctor_get(v_snippet_4254_, 0);
v_sections_4256_ = lean_ctor_get(v_snippet_4254_, 1);
v___x_4257_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_4253_, v_text_4255_);
if (lean_obj_tag(v___x_4257_) == 0)
{
return v___x_4257_;
}
else
{
lean_object* v_a_4258_; size_t v_sz_4259_; size_t v___x_4260_; lean_object* v___x_4261_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
lean_inc(v_a_4258_);
lean_dec_ref_known(v___x_4257_, 1);
v_sz_4259_ = lean_array_size(v_sections_4256_);
v___x_4260_ = ((size_t)0ULL);
v___x_4261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_sections_4256_, v_sz_4259_, v___x_4260_, v_a_4258_);
return v___x_4261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet___boxed(lean_object* v_ctx_4262_, lean_object* v_snippet_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_ctx_4262_, v_snippet_4263_);
lean_dec_ref(v_snippet_4263_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(lean_object* v_as_4265_, size_t v_sz_4266_, size_t v_i_4267_, lean_object* v_b_4268_){
_start:
{
uint8_t v___x_4269_; 
v___x_4269_ = lean_usize_dec_lt(v_i_4267_, v_sz_4266_);
if (v___x_4269_ == 0)
{
lean_object* v___x_4270_; 
v___x_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4270_, 0, v_b_4268_);
return v___x_4270_;
}
else
{
lean_object* v_snd_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4293_; 
v_snd_4271_ = lean_ctor_get(v_b_4268_, 1);
v_isSharedCheck_4293_ = !lean_is_exclusive(v_b_4268_);
if (v_isSharedCheck_4293_ == 0)
{
lean_object* v_unused_4294_; 
v_unused_4294_ = lean_ctor_get(v_b_4268_, 0);
lean_dec(v_unused_4294_);
v___x_4273_ = v_b_4268_;
v_isShared_4274_ = v_isSharedCheck_4293_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_snd_4271_);
lean_dec(v_b_4268_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4293_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v_a_4275_; lean_object* v___x_4276_; 
v_a_4275_ = lean_array_uget_borrowed(v_as_4265_, v_i_4267_);
v___x_4276_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4271_, v_a_4275_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
lean_del_object(v___x_4273_);
v_a_4277_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4276_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4276_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4277_);
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
lean_object* v_a_4285_; lean_object* v___x_4286_; lean_object* v___x_4288_; 
v_a_4285_ = lean_ctor_get(v___x_4276_, 0);
lean_inc(v_a_4285_);
lean_dec_ref_known(v___x_4276_, 1);
v___x_4286_ = lean_box(0);
if (v_isShared_4274_ == 0)
{
lean_ctor_set(v___x_4273_, 1, v_a_4285_);
lean_ctor_set(v___x_4273_, 0, v___x_4286_);
v___x_4288_ = v___x_4273_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v___x_4286_);
lean_ctor_set(v_reuseFailAlloc_4292_, 1, v_a_4285_);
v___x_4288_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
size_t v___x_4289_; size_t v___x_4290_; 
v___x_4289_ = ((size_t)1ULL);
v___x_4290_ = lean_usize_add(v_i_4267_, v___x_4289_);
v_i_4267_ = v___x_4290_;
v_b_4268_ = v___x_4288_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4295_, lean_object* v_sz_4296_, lean_object* v_i_4297_, lean_object* v_b_4298_){
_start:
{
size_t v_sz_boxed_4299_; size_t v_i_boxed_4300_; lean_object* v_res_4301_; 
v_sz_boxed_4299_ = lean_unbox_usize(v_sz_4296_);
lean_dec(v_sz_4296_);
v_i_boxed_4300_ = lean_unbox_usize(v_i_4297_);
lean_dec(v_i_4297_);
v_res_4301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_4295_, v_sz_boxed_4299_, v_i_boxed_4300_, v_b_4298_);
lean_dec_ref(v_as_4295_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(lean_object* v_as_4302_, size_t v_sz_4303_, size_t v_i_4304_, lean_object* v_b_4305_){
_start:
{
uint8_t v___x_4306_; 
v___x_4306_ = lean_usize_dec_lt(v_i_4304_, v_sz_4303_);
if (v___x_4306_ == 0)
{
lean_object* v___x_4307_; 
v___x_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4307_, 0, v_b_4305_);
return v___x_4307_;
}
else
{
lean_object* v_snd_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4330_; 
v_snd_4308_ = lean_ctor_get(v_b_4305_, 1);
v_isSharedCheck_4330_ = !lean_is_exclusive(v_b_4305_);
if (v_isSharedCheck_4330_ == 0)
{
lean_object* v_unused_4331_; 
v_unused_4331_ = lean_ctor_get(v_b_4305_, 0);
lean_dec(v_unused_4331_);
v___x_4310_ = v_b_4305_;
v_isShared_4311_ = v_isSharedCheck_4330_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_snd_4308_);
lean_dec(v_b_4305_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4330_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v_a_4312_; lean_object* v___x_4313_; 
v_a_4312_ = lean_array_uget_borrowed(v_as_4302_, v_i_4304_);
v___x_4313_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4308_, v_a_4312_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4321_; 
lean_del_object(v___x_4310_);
v_a_4314_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4316_ = v___x_4313_;
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v___x_4313_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_a_4314_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
else
{
lean_object* v_a_4322_; lean_object* v___x_4323_; lean_object* v___x_4325_; 
v_a_4322_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4322_);
lean_dec_ref_known(v___x_4313_, 1);
v___x_4323_ = lean_box(0);
if (v_isShared_4311_ == 0)
{
lean_ctor_set(v___x_4310_, 1, v_a_4322_);
lean_ctor_set(v___x_4310_, 0, v___x_4323_);
v___x_4325_ = v___x_4310_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v___x_4323_);
lean_ctor_set(v_reuseFailAlloc_4329_, 1, v_a_4322_);
v___x_4325_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
size_t v___x_4326_; size_t v___x_4327_; lean_object* v___x_4328_; 
v___x_4326_ = ((size_t)1ULL);
v___x_4327_ = lean_usize_add(v_i_4304_, v___x_4326_);
v___x_4328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_4302_, v_sz_4303_, v___x_4327_, v___x_4325_);
return v___x_4328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1___boxed(lean_object* v_as_4332_, lean_object* v_sz_4333_, lean_object* v_i_4334_, lean_object* v_b_4335_){
_start:
{
size_t v_sz_boxed_4336_; size_t v_i_boxed_4337_; lean_object* v_res_4338_; 
v_sz_boxed_4336_ = lean_unbox_usize(v_sz_4333_);
lean_dec(v_sz_4333_);
v_i_boxed_4337_ = lean_unbox_usize(v_i_4334_);
lean_dec(v_i_4334_);
v_res_4338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_as_4332_, v_sz_boxed_4336_, v_i_boxed_4337_, v_b_4335_);
lean_dec_ref(v_as_4332_);
return v_res_4338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_4339_, size_t v_sz_4340_, size_t v_i_4341_, lean_object* v_b_4342_){
_start:
{
uint8_t v___x_4343_; 
v___x_4343_ = lean_usize_dec_lt(v_i_4341_, v_sz_4340_);
if (v___x_4343_ == 0)
{
lean_object* v___x_4344_; 
v___x_4344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4344_, 0, v_b_4342_);
return v___x_4344_;
}
else
{
lean_object* v_snd_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4367_; 
v_snd_4345_ = lean_ctor_get(v_b_4342_, 1);
v_isSharedCheck_4367_ = !lean_is_exclusive(v_b_4342_);
if (v_isSharedCheck_4367_ == 0)
{
lean_object* v_unused_4368_; 
v_unused_4368_ = lean_ctor_get(v_b_4342_, 0);
lean_dec(v_unused_4368_);
v___x_4347_ = v_b_4342_;
v_isShared_4348_ = v_isSharedCheck_4367_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_snd_4345_);
lean_dec(v_b_4342_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4367_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v_a_4349_; lean_object* v___x_4350_; 
v_a_4349_ = lean_array_uget_borrowed(v_as_4339_, v_i_4341_);
v___x_4350_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4345_, v_a_4349_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4358_; 
lean_del_object(v___x_4347_);
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4353_ = v___x_4350_;
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4350_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4356_; 
if (v_isShared_4354_ == 0)
{
v___x_4356_ = v___x_4353_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4351_);
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
lean_object* v_a_4359_; lean_object* v___x_4360_; lean_object* v___x_4362_; 
v_a_4359_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v___x_4350_, 1);
v___x_4360_ = lean_box(0);
if (v_isShared_4348_ == 0)
{
lean_ctor_set(v___x_4347_, 1, v_a_4359_);
lean_ctor_set(v___x_4347_, 0, v___x_4360_);
v___x_4362_ = v___x_4347_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v___x_4360_);
lean_ctor_set(v_reuseFailAlloc_4366_, 1, v_a_4359_);
v___x_4362_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
size_t v___x_4363_; size_t v___x_4364_; 
v___x_4363_ = ((size_t)1ULL);
v___x_4364_ = lean_usize_add(v_i_4341_, v___x_4363_);
v_i_4341_ = v___x_4364_;
v_b_4342_ = v___x_4362_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_4369_, lean_object* v_sz_4370_, lean_object* v_i_4371_, lean_object* v_b_4372_){
_start:
{
size_t v_sz_boxed_4373_; size_t v_i_boxed_4374_; lean_object* v_res_4375_; 
v_sz_boxed_4373_ = lean_unbox_usize(v_sz_4370_);
lean_dec(v_sz_4370_);
v_i_boxed_4374_ = lean_unbox_usize(v_i_4371_);
lean_dec(v_i_4371_);
v_res_4375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_4369_, v_sz_boxed_4373_, v_i_boxed_4374_, v_b_4372_);
lean_dec_ref(v_as_4369_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(lean_object* v_as_4376_, size_t v_sz_4377_, size_t v_i_4378_, lean_object* v_b_4379_){
_start:
{
uint8_t v___x_4380_; 
v___x_4380_ = lean_usize_dec_lt(v_i_4378_, v_sz_4377_);
if (v___x_4380_ == 0)
{
lean_object* v___x_4381_; 
v___x_4381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4381_, 0, v_b_4379_);
return v___x_4381_;
}
else
{
lean_object* v_snd_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4404_; 
v_snd_4382_ = lean_ctor_get(v_b_4379_, 1);
v_isSharedCheck_4404_ = !lean_is_exclusive(v_b_4379_);
if (v_isSharedCheck_4404_ == 0)
{
lean_object* v_unused_4405_; 
v_unused_4405_ = lean_ctor_get(v_b_4379_, 0);
lean_dec(v_unused_4405_);
v___x_4384_ = v_b_4379_;
v_isShared_4385_ = v_isSharedCheck_4404_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_snd_4382_);
lean_dec(v_b_4379_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4404_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v_a_4386_; lean_object* v___x_4387_; 
v_a_4386_ = lean_array_uget_borrowed(v_as_4376_, v_i_4378_);
v___x_4387_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_4382_, v_a_4386_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4395_; 
lean_del_object(v___x_4384_);
v_a_4388_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4390_ = v___x_4387_;
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4387_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4397_; lean_object* v___x_4399_; 
v_a_4396_ = lean_ctor_get(v___x_4387_, 0);
lean_inc(v_a_4396_);
lean_dec_ref_known(v___x_4387_, 1);
v___x_4397_ = lean_box(0);
if (v_isShared_4385_ == 0)
{
lean_ctor_set(v___x_4384_, 1, v_a_4396_);
lean_ctor_set(v___x_4384_, 0, v___x_4397_);
v___x_4399_ = v___x_4384_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4397_);
lean_ctor_set(v_reuseFailAlloc_4403_, 1, v_a_4396_);
v___x_4399_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
size_t v___x_4400_; size_t v___x_4401_; lean_object* v___x_4402_; 
v___x_4400_ = ((size_t)1ULL);
v___x_4401_ = lean_usize_add(v_i_4378_, v___x_4400_);
v___x_4402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_4376_, v_sz_4377_, v___x_4401_, v___x_4399_);
return v___x_4402_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2___boxed(lean_object* v_as_4406_, lean_object* v_sz_4407_, lean_object* v_i_4408_, lean_object* v_b_4409_){
_start:
{
size_t v_sz_boxed_4410_; size_t v_i_boxed_4411_; lean_object* v_res_4412_; 
v_sz_boxed_4410_ = lean_unbox_usize(v_sz_4407_);
lean_dec(v_sz_4407_);
v_i_boxed_4411_ = lean_unbox_usize(v_i_4408_);
lean_dec(v_i_4408_);
v_res_4412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_as_4406_, v_sz_boxed_4410_, v_i_boxed_4411_, v_b_4409_);
lean_dec_ref(v_as_4406_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(lean_object* v_init_4413_, lean_object* v_n_4414_, lean_object* v_b_4415_){
_start:
{
if (lean_obj_tag(v_n_4414_) == 0)
{
lean_object* v_cs_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; size_t v_sz_4419_; size_t v___x_4420_; lean_object* v___x_4421_; 
v_cs_4416_ = lean_ctor_get(v_n_4414_, 0);
v___x_4417_ = lean_box(0);
v___x_4418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4417_);
lean_ctor_set(v___x_4418_, 1, v_b_4415_);
v_sz_4419_ = lean_array_size(v_cs_4416_);
v___x_4420_ = ((size_t)0ULL);
v___x_4421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_init_4413_, v_cs_4416_, v_sz_4419_, v___x_4420_, v___x_4418_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4429_; 
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4424_ = v___x_4421_;
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4421_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4427_; 
if (v_isShared_4425_ == 0)
{
v___x_4427_ = v___x_4424_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_a_4422_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4444_; 
v_a_4430_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4432_ = v___x_4421_;
v_isShared_4433_ = v_isSharedCheck_4444_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4421_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4444_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v_fst_4434_; 
v_fst_4434_ = lean_ctor_get(v_a_4430_, 0);
if (lean_obj_tag(v_fst_4434_) == 0)
{
lean_object* v_snd_4435_; lean_object* v___x_4436_; lean_object* v___x_4438_; 
v_snd_4435_ = lean_ctor_get(v_a_4430_, 1);
lean_inc(v_snd_4435_);
lean_dec(v_a_4430_);
v___x_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4436_, 0, v_snd_4435_);
if (v_isShared_4433_ == 0)
{
lean_ctor_set(v___x_4432_, 0, v___x_4436_);
v___x_4438_ = v___x_4432_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4436_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
else
{
lean_object* v_val_4440_; lean_object* v___x_4442_; 
lean_inc_ref(v_fst_4434_);
lean_dec(v_a_4430_);
v_val_4440_ = lean_ctor_get(v_fst_4434_, 0);
lean_inc(v_val_4440_);
lean_dec_ref_known(v_fst_4434_, 1);
if (v_isShared_4433_ == 0)
{
lean_ctor_set(v___x_4432_, 0, v_val_4440_);
v___x_4442_ = v___x_4432_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_val_4440_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
}
else
{
lean_object* v_vs_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; size_t v_sz_4448_; size_t v___x_4449_; lean_object* v___x_4450_; 
v_vs_4445_ = lean_ctor_get(v_n_4414_, 0);
v___x_4446_ = lean_box(0);
v___x_4447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4447_, 0, v___x_4446_);
lean_ctor_set(v___x_4447_, 1, v_b_4415_);
v_sz_4448_ = lean_array_size(v_vs_4445_);
v___x_4449_ = ((size_t)0ULL);
v___x_4450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_vs_4445_, v_sz_4448_, v___x_4449_, v___x_4447_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4450_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4450_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
else
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4473_; 
v_a_4459_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4461_ = v___x_4450_;
v_isShared_4462_ = v_isSharedCheck_4473_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4450_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4473_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v_fst_4463_; 
v_fst_4463_ = lean_ctor_get(v_a_4459_, 0);
if (lean_obj_tag(v_fst_4463_) == 0)
{
lean_object* v_snd_4464_; lean_object* v___x_4465_; lean_object* v___x_4467_; 
v_snd_4464_ = lean_ctor_get(v_a_4459_, 1);
lean_inc(v_snd_4464_);
lean_dec(v_a_4459_);
v___x_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4465_, 0, v_snd_4464_);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 0, v___x_4465_);
v___x_4467_ = v___x_4461_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4465_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
else
{
lean_object* v_val_4469_; lean_object* v___x_4471_; 
lean_inc_ref(v_fst_4463_);
lean_dec(v_a_4459_);
v_val_4469_ = lean_ctor_get(v_fst_4463_, 0);
lean_inc(v_val_4469_);
lean_dec_ref_known(v_fst_4463_, 1);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 0, v_val_4469_);
v___x_4471_ = v___x_4461_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_val_4469_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(lean_object* v_init_4474_, lean_object* v_as_4475_, size_t v_sz_4476_, size_t v_i_4477_, lean_object* v_b_4478_){
_start:
{
uint8_t v___x_4479_; 
v___x_4479_ = lean_usize_dec_lt(v_i_4477_, v_sz_4476_);
if (v___x_4479_ == 0)
{
lean_object* v___x_4480_; 
v___x_4480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4480_, 0, v_b_4478_);
return v___x_4480_;
}
else
{
lean_object* v_snd_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4515_; 
v_snd_4481_ = lean_ctor_get(v_b_4478_, 1);
v_isSharedCheck_4515_ = !lean_is_exclusive(v_b_4478_);
if (v_isSharedCheck_4515_ == 0)
{
lean_object* v_unused_4516_; 
v_unused_4516_ = lean_ctor_get(v_b_4478_, 0);
lean_dec(v_unused_4516_);
v___x_4483_ = v_b_4478_;
v_isShared_4484_ = v_isSharedCheck_4515_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_snd_4481_);
lean_dec(v_b_4478_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4515_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v_a_4485_; lean_object* v___x_4486_; 
v_a_4485_ = lean_array_uget_borrowed(v_as_4475_, v_i_4477_);
lean_inc(v_snd_4481_);
v___x_4486_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_4474_, v_a_4485_, v_snd_4481_);
if (lean_obj_tag(v___x_4486_) == 0)
{
lean_object* v_a_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4494_; 
lean_del_object(v___x_4483_);
lean_dec(v_snd_4481_);
v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4486_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4489_ = v___x_4486_;
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_a_4487_);
lean_dec(v___x_4486_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4492_; 
if (v_isShared_4490_ == 0)
{
v___x_4492_ = v___x_4489_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_a_4487_);
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
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4514_; 
v_a_4495_ = lean_ctor_get(v___x_4486_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4486_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4497_ = v___x_4486_;
v_isShared_4498_ = v_isSharedCheck_4514_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4486_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4514_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
if (lean_obj_tag(v_a_4495_) == 0)
{
lean_object* v___x_4499_; lean_object* v___x_4501_; 
v___x_4499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4499_, 0, v_a_4495_);
if (v_isShared_4484_ == 0)
{
lean_ctor_set(v___x_4483_, 0, v___x_4499_);
v___x_4501_ = v___x_4483_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4499_);
lean_ctor_set(v_reuseFailAlloc_4505_, 1, v_snd_4481_);
v___x_4501_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
lean_object* v___x_4503_; 
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 0, v___x_4501_);
v___x_4503_ = v___x_4497_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v___x_4501_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4507_; lean_object* v___x_4509_; 
lean_del_object(v___x_4497_);
lean_dec(v_snd_4481_);
v_a_4506_ = lean_ctor_get(v_a_4495_, 0);
lean_inc(v_a_4506_);
lean_dec_ref_known(v_a_4495_, 1);
v___x_4507_ = lean_box(0);
if (v_isShared_4484_ == 0)
{
lean_ctor_set(v___x_4483_, 1, v_a_4506_);
lean_ctor_set(v___x_4483_, 0, v___x_4507_);
v___x_4509_ = v___x_4483_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___x_4507_);
lean_ctor_set(v_reuseFailAlloc_4513_, 1, v_a_4506_);
v___x_4509_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
size_t v___x_4510_; size_t v___x_4511_; 
v___x_4510_ = ((size_t)1ULL);
v___x_4511_ = lean_usize_add(v_i_4477_, v___x_4510_);
v_i_4477_ = v___x_4511_;
v_b_4478_ = v___x_4509_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4517_, lean_object* v_as_4518_, lean_object* v_sz_4519_, lean_object* v_i_4520_, lean_object* v_b_4521_){
_start:
{
size_t v_sz_boxed_4522_; size_t v_i_boxed_4523_; lean_object* v_res_4524_; 
v_sz_boxed_4522_ = lean_unbox_usize(v_sz_4519_);
lean_dec(v_sz_4519_);
v_i_boxed_4523_ = lean_unbox_usize(v_i_4520_);
lean_dec(v_i_4520_);
v_res_4524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_init_4517_, v_as_4518_, v_sz_boxed_4522_, v_i_boxed_4523_, v_b_4521_);
lean_dec_ref(v_as_4518_);
lean_dec_ref(v_init_4517_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0___boxed(lean_object* v_init_4525_, lean_object* v_n_4526_, lean_object* v_b_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_4525_, v_n_4526_, v_b_4527_);
lean_dec_ref(v_n_4526_);
lean_dec_ref(v_init_4525_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(lean_object* v_t_4529_, lean_object* v_init_4530_){
_start:
{
lean_object* v_root_4531_; lean_object* v_tail_4532_; lean_object* v___x_4533_; 
v_root_4531_ = lean_ctor_get(v_t_4529_, 0);
v_tail_4532_ = lean_ctor_get(v_t_4529_, 1);
lean_inc_ref(v_init_4530_);
v___x_4533_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_4530_, v_root_4531_, v_init_4530_);
lean_dec_ref(v_init_4530_);
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4541_; 
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4536_ = v___x_4533_;
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4533_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4539_; 
if (v_isShared_4537_ == 0)
{
v___x_4539_ = v___x_4536_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_a_4534_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
}
}
}
else
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4578_; 
v_a_4542_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4544_ = v___x_4533_;
v_isShared_4545_ = v_isSharedCheck_4578_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v___x_4533_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4578_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
if (lean_obj_tag(v_a_4542_) == 0)
{
lean_object* v_a_4546_; lean_object* v___x_4548_; 
v_a_4546_ = lean_ctor_get(v_a_4542_, 0);
lean_inc(v_a_4546_);
lean_dec_ref_known(v_a_4542_, 1);
if (v_isShared_4545_ == 0)
{
lean_ctor_set(v___x_4544_, 0, v_a_4546_);
v___x_4548_ = v___x_4544_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4546_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
else
{
lean_object* v_a_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; size_t v_sz_4553_; size_t v___x_4554_; lean_object* v___x_4555_; 
lean_del_object(v___x_4544_);
v_a_4550_ = lean_ctor_get(v_a_4542_, 0);
lean_inc(v_a_4550_);
lean_dec_ref_known(v_a_4542_, 1);
v___x_4551_ = lean_box(0);
v___x_4552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4551_);
lean_ctor_set(v___x_4552_, 1, v_a_4550_);
v_sz_4553_ = lean_array_size(v_tail_4532_);
v___x_4554_ = ((size_t)0ULL);
v___x_4555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_tail_4532_, v_sz_4553_, v___x_4554_, v___x_4552_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4563_; 
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4558_ = v___x_4555_;
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v___x_4555_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_a_4556_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
}
else
{
lean_object* v_a_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4577_; 
v_a_4564_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4566_ = v___x_4555_;
v_isShared_4567_ = v_isSharedCheck_4577_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_a_4564_);
lean_dec(v___x_4555_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4577_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v_fst_4568_; 
v_fst_4568_ = lean_ctor_get(v_a_4564_, 0);
if (lean_obj_tag(v_fst_4568_) == 0)
{
lean_object* v_snd_4569_; lean_object* v___x_4571_; 
v_snd_4569_ = lean_ctor_get(v_a_4564_, 1);
lean_inc(v_snd_4569_);
lean_dec(v_a_4564_);
if (v_isShared_4567_ == 0)
{
lean_ctor_set(v___x_4566_, 0, v_snd_4569_);
v___x_4571_ = v___x_4566_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_snd_4569_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
else
{
lean_object* v_val_4573_; lean_object* v___x_4575_; 
lean_inc_ref(v_fst_4568_);
lean_dec(v_a_4564_);
v_val_4573_ = lean_ctor_get(v_fst_4568_, 0);
lean_inc(v_val_4573_);
lean_dec_ref_known(v_fst_4568_, 1);
if (v_isShared_4567_ == 0)
{
lean_ctor_set(v___x_4566_, 0, v_val_4573_);
v___x_4575_ = v___x_4566_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_val_4573_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
return v___x_4575_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0___boxed(lean_object* v_t_4579_, lean_object* v_init_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(v_t_4579_, v_init_4580_);
lean_dec_ref(v_t_4579_);
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble(lean_object* v_docs_4584_){
_start:
{
lean_object* v_ctx_4585_; lean_object* v___x_4586_; 
v_ctx_4585_ = ((lean_object*)(l_Lean_VersoModuleDocs_assemble___closed__0));
v___x_4586_ = l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(v_docs_4584_, v_ctx_4585_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v_a_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4594_; 
v_a_4587_ = lean_ctor_get(v___x_4586_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4589_ = v___x_4586_;
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_a_4587_);
lean_dec(v___x_4586_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v___x_4592_; 
if (v_isShared_4590_ == 0)
{
v___x_4592_ = v___x_4589_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_a_4587_);
v___x_4592_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
return v___x_4592_;
}
}
}
else
{
lean_object* v_a_4595_; lean_object* v___x_4596_; 
v_a_4595_ = lean_ctor_get(v___x_4586_, 0);
lean_inc(v_a_4595_);
lean_dec_ref_known(v___x_4586_, 1);
v___x_4596_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(v_a_4595_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v_a_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4604_; 
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4599_ = v___x_4596_;
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_a_4597_);
lean_dec(v___x_4596_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4602_; 
if (v_isShared_4600_ == 0)
{
v___x_4602_ = v___x_4599_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_a_4597_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
}
}
}
else
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4615_; 
v_a_4605_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4607_ = v___x_4596_;
v_isShared_4608_ = v_isSharedCheck_4615_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4596_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4615_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v_content_4609_; lean_object* v_priorParts_4610_; lean_object* v___x_4611_; lean_object* v___x_4613_; 
v_content_4609_ = lean_ctor_get(v_a_4605_, 0);
lean_inc_ref(v_content_4609_);
v_priorParts_4610_ = lean_ctor_get(v_a_4605_, 1);
lean_inc_ref(v_priorParts_4610_);
lean_dec(v_a_4605_);
v___x_4611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4611_, 0, v_content_4609_);
lean_ctor_set(v___x_4611_, 1, v_priorParts_4610_);
if (v_isShared_4608_ == 0)
{
lean_ctor_set(v___x_4607_, 0, v___x_4611_);
v___x_4613_ = v___x_4607_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v___x_4611_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
return v___x_4613_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble___boxed(lean_object* v_docs_4616_){
_start:
{
lean_object* v_res_4617_; 
v_res_4617_ = l_Lean_VersoModuleDocs_assemble(v_docs_4616_);
lean_dec_ref(v_docs_4616_);
return v_res_4617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v_es_4618_){
_start:
{
lean_object* v___x_4619_; 
v___x_4619_ = lean_array_mk(v_es_4618_);
return v___x_4619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v_x_4622_, lean_object* v_x_4623_, lean_object* v_es_4624_){
_start:
{
lean_object* v_ents_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; 
v_ents_4625_ = lean_array_mk(v_es_4624_);
v___x_4626_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_));
lean_inc_ref(v_ents_4625_);
v___x_4627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4627_, 0, v___x_4626_);
lean_ctor_set(v___x_4627_, 1, v_ents_4625_);
lean_ctor_set(v___x_4627_, 2, v_ents_4625_);
return v___x_4627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v_x_4628_, lean_object* v_x_4629_, lean_object* v_es_4630_){
_start:
{
lean_object* v_res_4631_; 
v_res_4631_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(v_x_4628_, v_x_4629_, v_es_4630_);
lean_dec_ref(v_x_4629_);
lean_dec_ref(v_x_4628_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v___x_4632_, lean_object* v_x_4633_){
_start:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; size_t v___x_4637_; lean_object* v___x_4638_; 
v___x_4634_ = lean_unsigned_to_nat(32u);
v___x_4635_ = lean_mk_empty_array_with_capacity(v___x_4634_);
v___x_4636_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_4637_ = ((size_t)5ULL);
lean_inc(v___x_4632_);
v___x_4638_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4638_, 0, v___x_4636_);
lean_ctor_set(v___x_4638_, 1, v___x_4635_);
lean_ctor_set(v___x_4638_, 2, v___x_4632_);
lean_ctor_set(v___x_4638_, 3, v___x_4632_);
lean_ctor_set_usize(v___x_4638_, 4, v___x_4637_);
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v___x_4639_, lean_object* v_x_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(v___x_4639_, v_x_4640_);
lean_dec_ref(v_x_4640_);
return v_res_4641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4662_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_));
v___x_4663_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_4662_);
return v___x_4663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v_a_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_();
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainVersoModuleDocs(lean_object* v_env_4666_){
_start:
{
lean_object* v___x_4667_; lean_object* v_toEnvExtension_4668_; lean_object* v_asyncMode_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
v___x_4667_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_4668_ = lean_ctor_get(v___x_4667_, 0);
v_asyncMode_4669_ = lean_ctor_get(v_toEnvExtension_4668_, 2);
v___x_4670_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_4671_ = lean_box(0);
v___x_4672_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4670_, v___x_4667_, v_env_4666_, v_asyncMode_4669_, v___x_4671_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDocs(lean_object* v_env_4673_){
_start:
{
lean_object* v___x_4674_; 
v___x_4674_ = l_Lean_getMainVersoModuleDocs(v_env_4673_);
return v___x_4674_;
}
}
static lean_object* _init_l_Lean_getVersoModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4675_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_4676_ = lean_box(0);
v___x_4677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4677_, 0, v___x_4676_);
lean_ctor_set(v___x_4677_, 1, v___x_4675_);
return v___x_4677_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f(lean_object* v_env_4678_, lean_object* v_moduleName_4679_){
_start:
{
lean_object* v___x_4680_; 
v___x_4680_ = l_Lean_Environment_getModuleIdx_x3f(v_env_4678_, v_moduleName_4679_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v___x_4681_; 
v___x_4681_ = lean_box(0);
return v___x_4681_;
}
else
{
lean_object* v_val_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4693_; 
v_val_4682_ = lean_ctor_get(v___x_4680_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4684_ = v___x_4680_;
v_isShared_4685_ = v_isSharedCheck_4693_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_val_4682_);
lean_dec(v___x_4680_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4693_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; uint8_t v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4691_; 
v___x_4686_ = lean_obj_once(&l_Lean_getVersoModuleDoc_x3f___closed__0, &l_Lean_getVersoModuleDoc_x3f___closed__0_once, _init_l_Lean_getVersoModuleDoc_x3f___closed__0);
v___x_4687_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v___x_4688_ = 1;
v___x_4689_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_4686_, v___x_4687_, v_env_4678_, v_val_4682_, v___x_4688_);
lean_dec(v_val_4682_);
if (v_isShared_4685_ == 0)
{
lean_ctor_set(v___x_4684_, 0, v___x_4689_);
v___x_4691_ = v___x_4684_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v___x_4689_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f___boxed(lean_object* v_env_4694_, lean_object* v_moduleName_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l_Lean_getVersoModuleDoc_x3f(v_env_4694_, v_moduleName_4695_);
lean_dec(v_moduleName_4695_);
lean_dec_ref(v_env_4694_);
return v_res_4696_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet(lean_object* v_env_4699_, lean_object* v_snippet_4700_){
_start:
{
lean_object* v_docs_4701_; uint8_t v___x_4702_; 
lean_inc_ref(v_env_4699_);
v_docs_4701_ = l_Lean_getMainVersoModuleDocs(v_env_4699_);
v___x_4702_ = l_Lean_VersoModuleDocs_canAdd(v_docs_4701_, v_snippet_4700_);
if (v___x_4702_ == 0)
{
lean_object* v___x_4703_; lean_object* v___y_4705_; lean_object* v___x_4710_; 
lean_dec_ref(v_snippet_4700_);
lean_dec_ref(v_env_4699_);
v___x_4703_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__0));
v___x_4710_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_4701_);
lean_dec_ref(v_docs_4701_);
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_object* v___x_4711_; 
v___x_4711_ = ((lean_object*)(l_Lean_findInternalDocString_x3f___closed__0));
v___y_4705_ = v___x_4711_;
goto v___jp_4704_;
}
else
{
lean_object* v_val_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; 
v_val_4712_ = lean_ctor_get(v___x_4710_, 0);
lean_inc(v_val_4712_);
lean_dec_ref_known(v___x_4710_, 1);
v___x_4713_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__1));
v___x_4714_ = l_Nat_reprFast(v_val_4712_);
v___x_4715_ = lean_string_append(v___x_4713_, v___x_4714_);
lean_dec_ref(v___x_4714_);
v___x_4716_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__11));
v___x_4717_ = lean_string_append(v___x_4715_, v___x_4716_);
v___y_4705_ = v___x_4717_;
goto v___jp_4704_;
}
v___jp_4704_:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; 
v___x_4706_ = lean_string_append(v___x_4703_, v___y_4705_);
lean_dec_ref(v___y_4705_);
v___x_4707_ = ((lean_object*)(l___private_Lean_DocString_Markdown_0__Lean_Doc_inlineMarkdown___at___00Lean_Doc_partMarkdown___at___00__private_Lean_DocString_Extension_0__Lean_findSimpleDocString_x3f_toMarkdown_spec__0_spec__0___closed__11));
v___x_4708_ = lean_string_append(v___x_4706_, v___x_4707_);
v___x_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
return v___x_4709_;
}
}
else
{
lean_object* v___x_4718_; lean_object* v_toEnvExtension_4719_; lean_object* v_asyncMode_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
lean_dec_ref(v_docs_4701_);
v___x_4718_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_4719_ = lean_ctor_get(v___x_4718_, 0);
v_asyncMode_4720_ = lean_ctor_get(v_toEnvExtension_4719_, 2);
v___x_4721_ = lean_box(0);
v___x_4722_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4718_, v_env_4699_, v_snippet_4700_, v_asyncMode_4720_, v___x_4721_);
v___x_4723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4723_, 0, v___x_4722_);
return v___x_4723_;
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
