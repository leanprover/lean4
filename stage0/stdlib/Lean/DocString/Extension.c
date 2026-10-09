// Lean compiler output
// Module: Lean.DocString.Extension
// Imports: public import Lean.DeclarationRange public import Lean.DocString.Types public import Lean.DocString.DeferredCheck public import Init.Data.String.Extra public import Init.Data.String.TakeDrop public import Init.Data.String.Search public import Init.Data.String.Length import Init.Omega import Lean.PrivateName
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
lean_object* l___private_Init_Dynamic_0__Dynamic_typeNameImpl(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_Environment_getModuleIdx_x3f(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default___redArg();
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedDeclarationRange_default;
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabInline_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabInline_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabInline_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabInline_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabInline_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabInline_custom_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabInline_custom_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabInline_deferred_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabInline_deferred_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprElabInline___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ElabInline.custom"};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__0 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__1 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__2 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__2_value;
static const lean_string_object l_Lean_instReprElabInline___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "(.mk "};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__3 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__3_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__4 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__2_value),((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__4_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__5 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__5_value;
static const lean_string_object l_Lean_instReprElabInline___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " _)"};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__6 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__6_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__7 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__7_value;
static const lean_string_object l_Lean_instReprElabInline___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "ElabInline.deferred"};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__8 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__8_value)}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__9 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_instReprElabInline___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprElabInline___lam__0___closed__10 = (const lean_object*)&l_Lean_instReprElabInline___lam__0___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_instReprElabInline___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprElabInline___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprElabInline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprElabInline___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprElabInline___closed__0 = (const lean_object*)&l_Lean_instReprElabInline___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprElabInline = (const lean_object*)&l_Lean_instReprElabInline___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ElabBlock_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabBlock_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabBlock_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabBlock_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabBlock_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabBlock_custom_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabBlock_custom_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabBlock_deferred_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabBlock_deferred_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprElabBlock___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ElabBlock.custom"};
static const lean_object* l_Lean_instReprElabBlock___lam__0___closed__0 = (const lean_object*)&l_Lean_instReprElabBlock___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instReprElabBlock___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprElabBlock___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instReprElabBlock___lam__0___closed__1 = (const lean_object*)&l_Lean_instReprElabBlock___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instReprElabBlock___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprElabBlock___lam__0___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprElabBlock___lam__0___closed__2 = (const lean_object*)&l_Lean_instReprElabBlock___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_instReprElabBlock___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprElabBlock___lam__0___closed__2_value),((lean_object*)&l_Lean_instReprElabInline___lam__0___closed__4_value)}};
static const lean_object* l_Lean_instReprElabBlock___lam__0___closed__3 = (const lean_object*)&l_Lean_instReprElabBlock___lam__0___closed__3_value;
static const lean_string_object l_Lean_instReprElabBlock___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ElabBlock.deferred"};
static const lean_object* l_Lean_instReprElabBlock___lam__0___closed__4 = (const lean_object*)&l_Lean_instReprElabBlock___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_instReprElabBlock___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprElabBlock___lam__0___closed__4_value)}};
static const lean_object* l_Lean_instReprElabBlock___lam__0___closed__5 = (const lean_object*)&l_Lean_instReprElabBlock___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_instReprElabBlock___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprElabBlock___lam__0___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_instReprElabBlock___lam__0___closed__6 = (const lean_object*)&l_Lean_instReprElabBlock___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprElabBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprElabBlock___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprElabBlock___closed__0 = (const lean_object*)&l_Lean_instReprElabBlock___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprElabBlock = (const lean_object*)&l_Lean_instReprElabBlock___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_custom___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_custom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_deferred(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_custom___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_custom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Block_deferred(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_throwIfHasDocString___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "invalid doc string, declaration `"};
static const lean_object* l_Lean_throwIfHasDocString___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_throwIfHasDocString___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_throwIfHasDocString___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwIfHasDocString___redArg___lam__0___closed__1;
static const lean_string_object l_Lean_throwIfHasDocString___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` already has one"};
static const lean_object* l_Lean_throwIfHasDocString___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_throwIfHasDocString___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_throwIfHasDocString___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwIfHasDocString___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwIfHasDocString___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwIfHasDocString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_throwIfHasDocString___redArg___closed__0 = (const lean_object*)&l_Lean_throwIfHasDocString___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_throwIfHasDocString___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwIfHasDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addDocStringCore___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is in an imported module"};
static const lean_object* l_Lean_addDocStringCore___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_addDocStringCore___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_addDocStringCore___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDocStringCore___redArg___lam__2___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__7(lean_object*, lean_object*);
static const lean_string_object l_Lean_addInheritedDocString___redArg___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "invalid `[inherit_doc]` attribute, cycle detected"};
static const lean_object* l_Lean_addInheritedDocString___redArg___lam__8___closed__0 = (const lean_object*)&l_Lean_addInheritedDocString___redArg___lam__8___closed__0_value;
static lean_once_cell_t l_Lean_addInheritedDocString___redArg___lam__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addInheritedDocString___redArg___lam__8___closed__1;
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addInheritedDocString___redArg___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "invalid `[inherit_doc]` attribute, declaration `"};
static const lean_object* l_Lean_addInheritedDocString___redArg___lam__10___closed__0 = (const lean_object*)&l_Lean_addInheritedDocString___redArg___lam__10___closed__0_value;
static lean_once_cell_t l_Lean_addInheritedDocString___redArg___lam__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addInheritedDocString___redArg___lam__10___closed__1;
static const lean_string_object l_Lean_addInheritedDocString___redArg___lam__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "` already has an `[inherit_doc]` attribute"};
static const lean_object* l_Lean_addInheritedDocString___redArg___lam__10___closed__2 = (const lean_object*)&l_Lean_addInheritedDocString___redArg___lam__10___closed__2_value;
static lean_once_cell_t l_Lean_addInheritedDocString___redArg___lam__10___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addInheritedDocString___redArg___lam__10___closed__3;
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_addInheritedDocString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addInheritedDocString___redArg___closed__0 = (const lean_object*)&l_Lean_addInheritedDocString___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
LEAN_EXPORT lean_object* l_Lean_addMainModuleDoc___lam__0(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_getDocStringText___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "commentBody"};
static const lean_object* l_Lean_getDocStringText___redArg___closed__4 = (const lean_object*)&l_Lean_getDocStringText___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isVersoDocComment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l_Lean_isVersoDocComment___closed__0 = (const lean_object*)&l_Lean_isVersoDocComment___closed__0_value;
static const lean_ctor_object l_Lean_isVersoDocComment___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_isVersoDocComment___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isVersoDocComment___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_isVersoDocComment___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isVersoDocComment___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_isVersoDocComment___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isVersoDocComment___closed__1_value_aux_2),((lean_object*)&l_Lean_isVersoDocComment___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 150, 193, 173, 39, 149, 4, 235)}};
static const lean_object* l_Lean_isVersoDocComment___closed__1 = (const lean_object*)&l_Lean_isVersoDocComment___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_isVersoDocComment(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isVersoDocComment___boxed(lean_object*);
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
static lean_once_cell_t l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7_value;
static const lean_string_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10 = (const lean_object*)&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10_value;
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
static const lean_string_object l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2;
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4_value;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__5 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__5_value;
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
static const lean_ctor_object l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoModuleDocSnippet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Can't add - incorrect nesting "};
static const lean_object* l_Lean_addVersoModuleDocSnippet___closed__0 = (const lean_object*)&l_Lean_addVersoModuleDocSnippet___closed__0_value;
static const lean_string_object l_Lean_addVersoModuleDocSnippet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "(expected at most "};
static const lean_object* l_Lean_addVersoModuleDocSnippet___closed__1 = (const lean_object*)&l_Lean_addVersoModuleDocSnippet___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ElabInline_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_ElabInline_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_ElabInline_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_ElabInline_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
lean_object* v_val_7_; lean_object* v___x_8_; 
v_val_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_val_7_);
lean_dec_ref(v_t_5_);
v___x_8_ = lean_apply_1(v_k_6_, v_val_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_ElabInline_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_ElabInline_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_ElabInline_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_ElabInline_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_ElabInline_custom_elim___redArg(lean_object* v_t_21_, lean_object* v_custom_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_ElabInline_ctorElim___redArg(v_t_21_, v_custom_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_ElabInline_custom_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_custom_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_ElabInline_ctorElim___redArg(v_t_25_, v_custom_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_ElabInline_deferred_elim___redArg(lean_object* v_t_29_, lean_object* v_deferred_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_ElabInline_ctorElim___redArg(v_t_29_, v_deferred_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_ElabInline_deferred_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_deferred_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_ElabInline_ctorElim___redArg(v_t_33_, v_deferred_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprElabInline___lam__0(lean_object* v_v_58_, lean_object* v_x_59_){
_start:
{
if (lean_obj_tag(v_v_58_) == 0)
{
lean_object* v_val_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; 
v_val_60_ = lean_ctor_get(v_v_58_, 0);
lean_inc(v_val_60_);
lean_dec_ref_known(v_v_58_, 1);
v___x_61_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__5));
v___x_62_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_60_);
lean_dec(v_val_60_);
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = l_Lean_Name_reprPrec(v___x_62_, v___x_63_);
v___x_65_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_61_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
v___x_66_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__7));
v___x_67_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_65_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = 0;
v___x_69_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set_uint8(v___x_69_, sizeof(void*)*1, v___x_68_);
return v___x_69_;
}
else
{
lean_object* v_index_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_82_; 
v_index_70_ = lean_ctor_get(v_v_58_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v_v_58_);
if (v_isSharedCheck_82_ == 0)
{
v___x_72_ = v_v_58_;
v_isShared_73_ = v_isSharedCheck_82_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_index_70_);
lean_dec(v_v_58_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_82_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_74_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_75_ = l_Nat_reprFast(v_index_70_);
if (v_isShared_73_ == 0)
{
lean_ctor_set_tag(v___x_72_, 3);
lean_ctor_set(v___x_72_, 0, v___x_75_);
v___x_77_ = v___x_72_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_75_);
v___x_77_ = v_reuseFailAlloc_81_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; uint8_t v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_74_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = 0;
v___x_80_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_80_, 0, v___x_78_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*1, v___x_79_);
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprElabInline___lam__0___boxed(lean_object* v_v_83_, lean_object* v_x_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_instReprElabInline___lam__0(v_v_83_, v_x_84_);
lean_dec(v_x_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_ElabBlock_ctorIdx___impl(lean_object* v_x_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_obj_tag_nat(v_x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_ElabBlock_ctorIdx___impl___boxed(lean_object* v_x_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_ElabBlock_ctorIdx___impl(v_x_90_);
lean_dec_ref(v_x_90_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_ElabBlock_ctorElim___redArg(lean_object* v_t_92_, lean_object* v_k_93_){
_start:
{
lean_object* v_val_94_; lean_object* v___x_95_; 
v_val_94_ = lean_ctor_get(v_t_92_, 0);
lean_inc(v_val_94_);
lean_dec_ref(v_t_92_);
v___x_95_ = lean_apply_1(v_k_93_, v_val_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_ElabBlock_ctorElim(lean_object* v_motive_96_, lean_object* v_ctorIdx_97_, lean_object* v_t_98_, lean_object* v_h_99_, lean_object* v_k_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_ElabBlock_ctorElim___redArg(v_t_98_, v_k_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_ElabBlock_ctorElim___boxed(lean_object* v_motive_102_, lean_object* v_ctorIdx_103_, lean_object* v_t_104_, lean_object* v_h_105_, lean_object* v_k_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_ElabBlock_ctorElim(v_motive_102_, v_ctorIdx_103_, v_t_104_, v_h_105_, v_k_106_);
lean_dec(v_ctorIdx_103_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_ElabBlock_custom_elim___redArg(lean_object* v_t_108_, lean_object* v_custom_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_ElabBlock_ctorElim___redArg(v_t_108_, v_custom_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_ElabBlock_custom_elim(lean_object* v_motive_111_, lean_object* v_t_112_, lean_object* v_h_113_, lean_object* v_custom_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_ElabBlock_ctorElim___redArg(v_t_112_, v_custom_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_ElabBlock_deferred_elim___redArg(lean_object* v_t_116_, lean_object* v_deferred_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_ElabBlock_ctorElim___redArg(v_t_116_, v_deferred_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_ElabBlock_deferred_elim(lean_object* v_motive_119_, lean_object* v_t_120_, lean_object* v_h_121_, lean_object* v_deferred_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_ElabBlock_ctorElim___redArg(v_t_120_, v_deferred_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0(lean_object* v_v_139_, lean_object* v_x_140_){
_start:
{
if (lean_obj_tag(v_v_139_) == 0)
{
lean_object* v_val_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; lean_object* v___x_150_; 
v_val_141_ = lean_ctor_get(v_v_139_, 0);
lean_inc(v_val_141_);
lean_dec_ref_known(v_v_139_, 1);
v___x_142_ = ((lean_object*)(l_Lean_instReprElabBlock___lam__0___closed__3));
v___x_143_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_141_);
lean_dec(v_val_141_);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = l_Lean_Name_reprPrec(v___x_143_, v___x_144_);
v___x_146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_142_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__7));
v___x_148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_146_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = 0;
v___x_150_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*1, v___x_149_);
return v___x_150_;
}
else
{
lean_object* v_index_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_163_; 
v_index_151_ = lean_ctor_get(v_v_139_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v_v_139_);
if (v_isSharedCheck_163_ == 0)
{
v___x_153_ = v_v_139_;
v_isShared_154_ = v_isSharedCheck_163_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_index_151_);
lean_dec(v_v_139_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_163_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_155_ = ((lean_object*)(l_Lean_instReprElabBlock___lam__0___closed__6));
v___x_156_ = l_Nat_reprFast(v_index_151_);
if (v_isShared_154_ == 0)
{
lean_ctor_set_tag(v___x_153_, 3);
lean_ctor_set(v___x_153_, 0, v___x_156_);
v___x_158_ = v___x_153_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_162_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; uint8_t v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_155_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = 0;
v___x_161_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*1, v___x_160_);
return v___x_161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprElabBlock___lam__0___boxed(lean_object* v_v_164_, lean_object* v_x_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_instReprElabBlock___lam__0(v_v_164_, v_x_165_);
lean_dec(v_x_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_custom___redArg(lean_object* v_inst_169_, lean_object* v_val_170_, lean_object* v_content_171_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_172_, 0, v_inst_169_);
lean_ctor_set(v___x_172_, 1, v_val_170_);
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
v___x_174_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v_content_171_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_custom(lean_object* v_00_u03b1_175_, lean_object* v_inst_176_, lean_object* v_val_177_, lean_object* v_content_178_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v_inst_176_);
lean_ctor_set(v___x_179_, 1, v_val_177_);
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
v___x_181_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v_content_178_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Inline_deferred(lean_object* v_index_182_, lean_object* v_content_183_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_184_, 0, v_index_182_);
v___x_185_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_content_183_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_custom___redArg(lean_object* v_inst_186_, lean_object* v_val_187_, lean_object* v_content_188_){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v_inst_186_);
lean_ctor_set(v___x_189_, 1, v_val_187_);
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
v___x_191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v_content_188_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_custom(lean_object* v_00_u03b1_192_, lean_object* v_inst_193_, lean_object* v_val_194_, lean_object* v_content_195_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v_inst_193_);
lean_ctor_set(v___x_196_, 1, v_val_194_);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
v___x_198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v_content_195_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Block_deferred(lean_object* v_index_199_, lean_object* v_content_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_201_, 0, v_index_199_);
v___x_202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v_content_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(lean_object* v_name_209_, lean_object* v_decl_210_, lean_object* v_ref_211_){
_start:
{
lean_object* v_defValue_213_; lean_object* v_descr_214_; lean_object* v_deprecation_x3f_215_; lean_object* v___x_216_; uint8_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_defValue_213_ = lean_ctor_get(v_decl_210_, 0);
v_descr_214_ = lean_ctor_get(v_decl_210_, 1);
v_deprecation_x3f_215_ = lean_ctor_get(v_decl_210_, 2);
v___x_216_ = lean_alloc_ctor(1, 0, 1);
v___x_217_ = lean_unbox(v_defValue_213_);
lean_ctor_set_uint8(v___x_216_, 0, v___x_217_);
lean_inc(v_deprecation_x3f_215_);
lean_inc_ref(v_descr_214_);
lean_inc_n(v_name_209_, 2);
v___x_218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_218_, 0, v_name_209_);
lean_ctor_set(v___x_218_, 1, v_ref_211_);
lean_ctor_set(v___x_218_, 2, v___x_216_);
lean_ctor_set(v___x_218_, 3, v_descr_214_);
lean_ctor_set(v___x_218_, 4, v_deprecation_x3f_215_);
v___x_219_ = lean_register_option(v_name_209_, v___x_218_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_227_; 
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_227_ == 0)
{
lean_object* v_unused_228_; 
v_unused_228_ = lean_ctor_get(v___x_219_, 0);
lean_dec(v_unused_228_);
v___x_221_ = v___x_219_;
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
else
{
lean_dec(v___x_219_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; lean_object* v___x_225_; 
lean_inc(v_defValue_213_);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v_name_209_);
lean_ctor_set(v___x_223_, 1, v_defValue_213_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_223_);
v___x_225_ = v___x_221_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
else
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
lean_dec(v_name_209_);
v_a_229_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_236_ == 0)
{
v___x_231_ = v___x_219_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_219_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_a_229_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_237_, lean_object* v_decl_238_, lean_object* v_ref_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v_name_237_, v_decl_238_, v_ref_239_);
lean_dec_ref(v_decl_238_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_259_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_260_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_261_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_262_ = l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v___x_259_, v___x_260_, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4____boxed(lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_();
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_282_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_283_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_284_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_285_ = l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v___x_282_, v___x_283_, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4____boxed(lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_();
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = lean_box(1);
v___x_290_ = lean_st_mk_ref(v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2____boxed(lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_();
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_294_, lean_object* v_x_295_){
_start:
{
if (lean_obj_tag(v_x_295_) == 0)
{
lean_object* v_k_296_; lean_object* v_v_297_; lean_object* v_l_298_; lean_object* v_r_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_k_296_ = lean_ctor_get(v_x_295_, 1);
v_v_297_ = lean_ctor_get(v_x_295_, 2);
v_l_298_ = lean_ctor_get(v_x_295_, 3);
v_r_299_ = lean_ctor_get(v_x_295_, 4);
v___x_300_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_294_, v_l_298_);
lean_inc(v_v_297_);
lean_inc(v_k_296_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v_k_296_);
lean_ctor_set(v___x_301_, 1, v_v_297_);
v___x_302_ = lean_array_push(v___x_300_, v___x_301_);
v_init_294_ = v___x_302_;
v_x_295_ = v_r_299_;
goto _start;
}
else
{
return v_init_294_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_304_, lean_object* v_x_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_304_, v_x_305_);
lean_dec(v_x_305_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(lean_object* v_x_311_, lean_object* v_s_312_){
_start:
{
lean_object* v___x_313_; lean_object* v_ents_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v_ents_314_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v___x_313_, v_s_312_);
v___x_315_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
lean_inc_ref(v_ents_314_);
v___x_316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v_ents_314_);
lean_ctor_set(v___x_316_, 2, v_ents_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object* v_x_317_, lean_object* v_s_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(v_x_317_, v_s_318_);
lean_dec(v_s_318_);
lean_dec_ref(v_x_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; lean_object* v___x_332_; 
v___f_328_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_329_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_330_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_331_ = 0;
v___x_332_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_329_, v___x_330_, v___x_331_, v___f_328_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_();
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0(lean_object* v_init_335_, lean_object* v_t_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_335_, v_t_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_338_, lean_object* v_t_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0(v_init_338_, v_t_339_);
lean_dec(v_t_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_341_, lean_object* v_x_342_){
_start:
{
if (lean_obj_tag(v_x_342_) == 0)
{
lean_object* v_k_343_; lean_object* v_v_344_; lean_object* v_l_345_; lean_object* v_r_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_k_343_ = lean_ctor_get(v_x_342_, 1);
v_v_344_ = lean_ctor_get(v_x_342_, 2);
v_l_345_ = lean_ctor_get(v_x_342_, 3);
v_r_346_ = lean_ctor_get(v_x_342_, 4);
v___x_347_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_341_, v_l_345_);
lean_inc(v_v_344_);
lean_inc(v_k_343_);
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v_k_343_);
lean_ctor_set(v___x_348_, 1, v_v_344_);
v___x_349_ = lean_array_push(v___x_347_, v___x_348_);
v_init_341_ = v___x_349_;
v_x_342_ = v_r_346_;
goto _start;
}
else
{
return v_init_341_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_351_, lean_object* v_x_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_351_, v_x_352_);
lean_dec(v_x_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(lean_object* v_x_358_, lean_object* v_s_359_){
_start:
{
lean_object* v___x_360_; lean_object* v_ents_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_360_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v_ents_361_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v___x_360_, v_s_359_);
v___x_362_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
lean_inc_ref(v_ents_361_);
v___x_363_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v_ents_361_);
lean_ctor_set(v___x_363_, 2, v_ents_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed(lean_object* v_x_364_, lean_object* v_s_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(v_x_364_, v_s_365_);
lean_dec(v_s_365_);
lean_dec_ref(v_x_364_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; lean_object* v___x_400_; 
v___f_396_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_397_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_398_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_399_ = 0;
v___x_400_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_397_, v___x_398_, v___x_399_, v___f_396_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed(lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_();
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0(lean_object* v_init_403_, lean_object* v_t_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_403_, v_t_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_406_, lean_object* v_t_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0(v_init_406_, v_t_407_);
lean_dec(v_t_407_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = lean_box(1);
v___x_411_ = lean_st_mk_ref(v___x_410_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2____boxed(lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_415_, lean_object* v_x_416_){
_start:
{
if (lean_obj_tag(v_x_416_) == 0)
{
lean_object* v_k_417_; lean_object* v_v_418_; lean_object* v_l_419_; lean_object* v_r_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_k_417_ = lean_ctor_get(v_x_416_, 1);
v_v_418_ = lean_ctor_get(v_x_416_, 2);
v_l_419_ = lean_ctor_get(v_x_416_, 3);
v_r_420_ = lean_ctor_get(v_x_416_, 4);
v___x_421_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_415_, v_l_419_);
lean_inc(v_v_418_);
lean_inc(v_k_417_);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v_k_417_);
lean_ctor_set(v___x_422_, 1, v_v_418_);
v___x_423_ = lean_array_push(v___x_421_, v___x_422_);
v_init_415_ = v___x_423_;
v_x_416_ = v_r_420_;
goto _start;
}
else
{
return v_init_415_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_425_, lean_object* v_x_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_425_, v_x_426_);
lean_dec(v_x_426_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(lean_object* v_x_432_, lean_object* v_s_433_){
_start:
{
lean_object* v___x_434_; lean_object* v_ents_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_434_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v_ents_435_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v___x_434_, v_s_433_);
v___x_436_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
lean_inc_ref(v_ents_435_);
v___x_437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v_ents_435_);
lean_ctor_set(v___x_437_, 2, v_ents_435_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object* v_x_438_, lean_object* v_s_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(v_x_438_, v_s_439_);
lean_dec(v_s_439_);
lean_dec_ref(v_x_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; 
v___f_447_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v___x_448_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v___x_449_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_450_ = 0;
v___x_451_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_448_, v___x_449_, v___x_450_, v___f_447_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_();
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0(lean_object* v_init_454_, lean_object* v_t_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_454_, v_t_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_457_, lean_object* v_t_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0(v_init_457_, v_t_458_);
lean_dec(v_t_458_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString(lean_object* v_declName_460_, lean_object* v_docString_461_){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_463_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_464_ = lean_st_ref_take(v___x_463_);
v___x_465_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_460_, v_docString_461_, v___x_464_);
v___x_466_ = lean_st_ref_put(v___x_463_, v___x_465_);
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString___boxed(lean_object* v_declName_468_, lean_object* v_docString_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_addBuiltinDocString(v_declName_468_, v_docString_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(lean_object* v_k_472_, lean_object* v_t_473_){
_start:
{
if (lean_obj_tag(v_t_473_) == 0)
{
lean_object* v_k_474_; lean_object* v_v_475_; lean_object* v_l_476_; lean_object* v_r_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_1131_; 
v_k_474_ = lean_ctor_get(v_t_473_, 1);
v_v_475_ = lean_ctor_get(v_t_473_, 2);
v_l_476_ = lean_ctor_get(v_t_473_, 3);
v_r_477_ = lean_ctor_get(v_t_473_, 4);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_t_473_);
if (v_isSharedCheck_1131_ == 0)
{
lean_object* v_unused_1132_; 
v_unused_1132_ = lean_ctor_get(v_t_473_, 0);
lean_dec(v_unused_1132_);
v___x_479_ = v_t_473_;
v_isShared_480_ = v_isSharedCheck_1131_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_r_477_);
lean_inc(v_l_476_);
lean_inc(v_v_475_);
lean_inc(v_k_474_);
lean_dec(v_t_473_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_1131_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
uint8_t v___x_481_; 
v___x_481_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_472_, v_k_474_);
switch(v___x_481_)
{
case 0:
{
lean_object* v_impl_482_; lean_object* v___x_483_; 
v_impl_482_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_472_, v_l_476_);
v___x_483_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_482_) == 0)
{
if (lean_obj_tag(v_r_477_) == 0)
{
lean_object* v_size_484_; lean_object* v_size_485_; lean_object* v_k_486_; lean_object* v_v_487_; lean_object* v_l_488_; lean_object* v_r_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v_size_484_ = lean_ctor_get(v_impl_482_, 0);
v_size_485_ = lean_ctor_get(v_r_477_, 0);
v_k_486_ = lean_ctor_get(v_r_477_, 1);
v_v_487_ = lean_ctor_get(v_r_477_, 2);
v_l_488_ = lean_ctor_get(v_r_477_, 3);
lean_inc(v_l_488_);
v_r_489_ = lean_ctor_get(v_r_477_, 4);
v___x_490_ = lean_unsigned_to_nat(3u);
v___x_491_ = lean_nat_mul(v___x_490_, v_size_484_);
v___x_492_ = lean_nat_dec_lt(v___x_491_, v_size_485_);
lean_dec(v___x_491_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
lean_dec(v_l_488_);
v___x_493_ = lean_nat_add(v___x_483_, v_size_484_);
v___x_494_ = lean_nat_add(v___x_493_, v_size_485_);
lean_dec(v___x_493_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 3, v_impl_482_);
lean_ctor_set(v___x_479_, 0, v___x_494_);
v___x_496_ = v___x_479_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_497_, 3, v_impl_482_);
lean_ctor_set(v_reuseFailAlloc_497_, 4, v_r_477_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
else
{
lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_561_; 
lean_inc(v_r_489_);
lean_inc(v_v_487_);
lean_inc(v_k_486_);
lean_inc(v_size_485_);
v_isSharedCheck_561_ = !lean_is_exclusive(v_r_477_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; lean_object* v_unused_563_; lean_object* v_unused_564_; lean_object* v_unused_565_; lean_object* v_unused_566_; 
v_unused_562_ = lean_ctor_get(v_r_477_, 4);
lean_dec(v_unused_562_);
v_unused_563_ = lean_ctor_get(v_r_477_, 3);
lean_dec(v_unused_563_);
v_unused_564_ = lean_ctor_get(v_r_477_, 2);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v_r_477_, 1);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_r_477_, 0);
lean_dec(v_unused_566_);
v___x_499_ = v_r_477_;
v_isShared_500_ = v_isSharedCheck_561_;
goto v_resetjp_498_;
}
else
{
lean_dec(v_r_477_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_561_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v_size_501_; lean_object* v_k_502_; lean_object* v_v_503_; lean_object* v_l_504_; lean_object* v_r_505_; lean_object* v_size_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v_size_501_ = lean_ctor_get(v_l_488_, 0);
v_k_502_ = lean_ctor_get(v_l_488_, 1);
v_v_503_ = lean_ctor_get(v_l_488_, 2);
v_l_504_ = lean_ctor_get(v_l_488_, 3);
v_r_505_ = lean_ctor_get(v_l_488_, 4);
v_size_506_ = lean_ctor_get(v_r_489_, 0);
v___x_507_ = lean_unsigned_to_nat(2u);
v___x_508_ = lean_nat_mul(v___x_507_, v_size_506_);
v___x_509_ = lean_nat_dec_lt(v_size_501_, v___x_508_);
lean_dec(v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_537_; 
lean_inc(v_r_505_);
lean_inc(v_l_504_);
lean_inc(v_v_503_);
lean_inc(v_k_502_);
v_isSharedCheck_537_ = !lean_is_exclusive(v_l_488_);
if (v_isSharedCheck_537_ == 0)
{
lean_object* v_unused_538_; lean_object* v_unused_539_; lean_object* v_unused_540_; lean_object* v_unused_541_; lean_object* v_unused_542_; 
v_unused_538_ = lean_ctor_get(v_l_488_, 4);
lean_dec(v_unused_538_);
v_unused_539_ = lean_ctor_get(v_l_488_, 3);
lean_dec(v_unused_539_);
v_unused_540_ = lean_ctor_get(v_l_488_, 2);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_l_488_, 1);
lean_dec(v_unused_541_);
v_unused_542_ = lean_ctor_get(v_l_488_, 0);
lean_dec(v_unused_542_);
v___x_511_ = v_l_488_;
v_isShared_512_ = v_isSharedCheck_537_;
goto v_resetjp_510_;
}
else
{
lean_dec(v_l_488_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_537_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_527_; 
v___x_513_ = lean_nat_add(v___x_483_, v_size_484_);
v___x_514_ = lean_nat_add(v___x_513_, v_size_485_);
lean_dec(v_size_485_);
if (lean_obj_tag(v_l_504_) == 0)
{
lean_object* v_size_535_; 
v_size_535_ = lean_ctor_get(v_l_504_, 0);
lean_inc(v_size_535_);
v___y_527_ = v_size_535_;
goto v___jp_526_;
}
else
{
lean_object* v___x_536_; 
v___x_536_ = lean_unsigned_to_nat(0u);
v___y_527_ = v___x_536_;
goto v___jp_526_;
}
v___jp_515_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = lean_nat_add(v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec(v___y_517_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 4, v_r_489_);
lean_ctor_set(v___x_511_, 3, v_r_505_);
lean_ctor_set(v___x_511_, 2, v_v_487_);
lean_ctor_set(v___x_511_, 1, v_k_486_);
lean_ctor_set(v___x_511_, 0, v___x_519_);
v___x_521_ = v___x_511_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_k_486_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v_v_487_);
lean_ctor_set(v_reuseFailAlloc_525_, 3, v_r_505_);
lean_ctor_set(v_reuseFailAlloc_525_, 4, v_r_489_);
v___x_521_ = v_reuseFailAlloc_525_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_523_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 4, v___x_521_);
lean_ctor_set(v___x_499_, 3, v___y_516_);
lean_ctor_set(v___x_499_, 2, v_v_503_);
lean_ctor_set(v___x_499_, 1, v_k_502_);
lean_ctor_set(v___x_499_, 0, v___x_514_);
v___x_523_ = v___x_499_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_k_502_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_v_503_);
lean_ctor_set(v_reuseFailAlloc_524_, 3, v___y_516_);
lean_ctor_set(v_reuseFailAlloc_524_, 4, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
v___jp_526_:
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = lean_nat_add(v___x_513_, v___y_527_);
lean_dec(v___y_527_);
lean_dec(v___x_513_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v_l_504_);
lean_ctor_set(v___x_479_, 3, v_impl_482_);
lean_ctor_set(v___x_479_, 0, v___x_528_);
v___x_530_ = v___x_479_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_534_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_534_, 3, v_impl_482_);
lean_ctor_set(v_reuseFailAlloc_534_, 4, v_l_504_);
v___x_530_ = v_reuseFailAlloc_534_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; 
v___x_531_ = lean_nat_add(v___x_483_, v_size_506_);
if (lean_obj_tag(v_r_505_) == 0)
{
lean_object* v_size_532_; 
v_size_532_ = lean_ctor_get(v_r_505_, 0);
lean_inc(v_size_532_);
v___y_516_ = v___x_530_;
v___y_517_ = v___x_531_;
v___y_518_ = v_size_532_;
goto v___jp_515_;
}
else
{
lean_object* v___x_533_; 
v___x_533_ = lean_unsigned_to_nat(0u);
v___y_516_ = v___x_530_;
v___y_517_ = v___x_531_;
v___y_518_ = v___x_533_;
goto v___jp_515_;
}
}
}
}
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_547_; 
lean_del_object(v___x_479_);
v___x_543_ = lean_nat_add(v___x_483_, v_size_484_);
v___x_544_ = lean_nat_add(v___x_543_, v_size_485_);
lean_dec(v_size_485_);
v___x_545_ = lean_nat_add(v___x_543_, v_size_501_);
lean_dec(v___x_543_);
lean_inc_ref(v_impl_482_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 4, v_l_488_);
lean_ctor_set(v___x_499_, 3, v_impl_482_);
lean_ctor_set(v___x_499_, 2, v_v_475_);
lean_ctor_set(v___x_499_, 1, v_k_474_);
lean_ctor_set(v___x_499_, 0, v___x_545_);
v___x_547_ = v___x_499_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v_impl_482_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v_l_488_);
v___x_547_ = v_reuseFailAlloc_560_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_isSharedCheck_554_ = !lean_is_exclusive(v_impl_482_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; lean_object* v_unused_556_; lean_object* v_unused_557_; lean_object* v_unused_558_; lean_object* v_unused_559_; 
v_unused_555_ = lean_ctor_get(v_impl_482_, 4);
lean_dec(v_unused_555_);
v_unused_556_ = lean_ctor_get(v_impl_482_, 3);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_impl_482_, 2);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_impl_482_, 1);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_impl_482_, 0);
lean_dec(v_unused_559_);
v___x_549_ = v_impl_482_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_dec(v_impl_482_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 4, v_r_489_);
lean_ctor_set(v___x_549_, 3, v___x_547_);
lean_ctor_set(v___x_549_, 2, v_v_487_);
lean_ctor_set(v___x_549_, 1, v_k_486_);
lean_ctor_set(v___x_549_, 0, v___x_544_);
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_k_486_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_v_487_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v_r_489_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v_size_567_ = lean_ctor_get(v_impl_482_, 0);
v___x_568_ = lean_nat_add(v___x_483_, v_size_567_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 3, v_impl_482_);
lean_ctor_set(v___x_479_, 0, v___x_568_);
v___x_570_ = v___x_479_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v_impl_482_);
lean_ctor_set(v_reuseFailAlloc_571_, 4, v_r_477_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
else
{
if (lean_obj_tag(v_r_477_) == 0)
{
lean_object* v_l_572_; 
v_l_572_ = lean_ctor_get(v_r_477_, 3);
lean_inc(v_l_572_);
if (lean_obj_tag(v_l_572_) == 0)
{
lean_object* v_r_573_; 
v_r_573_ = lean_ctor_get(v_r_477_, 4);
lean_inc(v_r_573_);
if (lean_obj_tag(v_r_573_) == 0)
{
lean_object* v_size_574_; lean_object* v_k_575_; lean_object* v_v_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_589_; 
v_size_574_ = lean_ctor_get(v_r_477_, 0);
v_k_575_ = lean_ctor_get(v_r_477_, 1);
v_v_576_ = lean_ctor_get(v_r_477_, 2);
v_isSharedCheck_589_ = !lean_is_exclusive(v_r_477_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; lean_object* v_unused_591_; 
v_unused_590_ = lean_ctor_get(v_r_477_, 4);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_r_477_, 3);
lean_dec(v_unused_591_);
v___x_578_ = v_r_477_;
v_isShared_579_ = v_isSharedCheck_589_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_v_576_);
lean_inc(v_k_575_);
lean_inc(v_size_574_);
lean_dec(v_r_477_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_589_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v_size_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_584_; 
v_size_580_ = lean_ctor_get(v_l_572_, 0);
v___x_581_ = lean_nat_add(v___x_483_, v_size_574_);
lean_dec(v_size_574_);
v___x_582_ = lean_nat_add(v___x_483_, v_size_580_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 4, v_l_572_);
lean_ctor_set(v___x_578_, 3, v_impl_482_);
lean_ctor_set(v___x_578_, 2, v_v_475_);
lean_ctor_set(v___x_578_, 1, v_k_474_);
lean_ctor_set(v___x_578_, 0, v___x_582_);
v___x_584_ = v___x_578_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_588_, 3, v_impl_482_);
lean_ctor_set(v_reuseFailAlloc_588_, 4, v_l_572_);
v___x_584_ = v_reuseFailAlloc_588_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_586_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v_r_573_);
lean_ctor_set(v___x_479_, 3, v___x_584_);
lean_ctor_set(v___x_479_, 2, v_v_576_);
lean_ctor_set(v___x_479_, 1, v_k_575_);
lean_ctor_set(v___x_479_, 0, v___x_581_);
v___x_586_ = v___x_479_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_k_575_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v_v_576_);
lean_ctor_set(v_reuseFailAlloc_587_, 3, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_587_, 4, v_r_573_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
else
{
lean_object* v_k_592_; lean_object* v_v_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_616_; 
v_k_592_ = lean_ctor_get(v_r_477_, 1);
v_v_593_ = lean_ctor_get(v_r_477_, 2);
v_isSharedCheck_616_ = !lean_is_exclusive(v_r_477_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; lean_object* v_unused_618_; lean_object* v_unused_619_; 
v_unused_617_ = lean_ctor_get(v_r_477_, 4);
lean_dec(v_unused_617_);
v_unused_618_ = lean_ctor_get(v_r_477_, 3);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_r_477_, 0);
lean_dec(v_unused_619_);
v___x_595_ = v_r_477_;
v_isShared_596_ = v_isSharedCheck_616_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_v_593_);
lean_inc(v_k_592_);
lean_dec(v_r_477_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_616_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v_k_597_; lean_object* v_v_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_612_; 
v_k_597_ = lean_ctor_get(v_l_572_, 1);
v_v_598_ = lean_ctor_get(v_l_572_, 2);
v_isSharedCheck_612_ = !lean_is_exclusive(v_l_572_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; lean_object* v_unused_614_; lean_object* v_unused_615_; 
v_unused_613_ = lean_ctor_get(v_l_572_, 4);
lean_dec(v_unused_613_);
v_unused_614_ = lean_ctor_get(v_l_572_, 3);
lean_dec(v_unused_614_);
v_unused_615_ = lean_ctor_get(v_l_572_, 0);
lean_dec(v_unused_615_);
v___x_600_ = v_l_572_;
v_isShared_601_ = v_isSharedCheck_612_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_v_598_);
lean_inc(v_k_597_);
lean_dec(v_l_572_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_612_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_602_ = lean_unsigned_to_nat(3u);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 4, v_r_573_);
lean_ctor_set(v___x_600_, 3, v_r_573_);
lean_ctor_set(v___x_600_, 2, v_v_475_);
lean_ctor_set(v___x_600_, 1, v_k_474_);
lean_ctor_set(v___x_600_, 0, v___x_483_);
v___x_604_ = v___x_600_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_r_573_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v_r_573_);
v___x_604_ = v_reuseFailAlloc_611_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_606_; 
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 3, v_r_573_);
lean_ctor_set(v___x_595_, 0, v___x_483_);
v___x_606_ = v___x_595_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_k_592_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v_v_593_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v_r_573_);
lean_ctor_set(v_reuseFailAlloc_610_, 4, v_r_573_);
v___x_606_ = v_reuseFailAlloc_610_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_608_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v___x_606_);
lean_ctor_set(v___x_479_, 3, v___x_604_);
lean_ctor_set(v___x_479_, 2, v_v_598_);
lean_ctor_set(v___x_479_, 1, v_k_597_);
lean_ctor_set(v___x_479_, 0, v___x_602_);
v___x_608_ = v___x_479_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_k_597_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_v_598_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_620_; 
v_r_620_ = lean_ctor_get(v_r_477_, 4);
lean_inc(v_r_620_);
if (lean_obj_tag(v_r_620_) == 0)
{
lean_object* v_k_621_; lean_object* v_v_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_633_; 
v_k_621_ = lean_ctor_get(v_r_477_, 1);
v_v_622_ = lean_ctor_get(v_r_477_, 2);
v_isSharedCheck_633_ = !lean_is_exclusive(v_r_477_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; lean_object* v_unused_635_; lean_object* v_unused_636_; 
v_unused_634_ = lean_ctor_get(v_r_477_, 4);
lean_dec(v_unused_634_);
v_unused_635_ = lean_ctor_get(v_r_477_, 3);
lean_dec(v_unused_635_);
v_unused_636_ = lean_ctor_get(v_r_477_, 0);
lean_dec(v_unused_636_);
v___x_624_ = v_r_477_;
v_isShared_625_ = v_isSharedCheck_633_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_v_622_);
lean_inc(v_k_621_);
lean_dec(v_r_477_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_633_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_626_ = lean_unsigned_to_nat(3u);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 4, v_l_572_);
lean_ctor_set(v___x_624_, 2, v_v_475_);
lean_ctor_set(v___x_624_, 1, v_k_474_);
lean_ctor_set(v___x_624_, 0, v___x_483_);
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_l_572_);
lean_ctor_set(v_reuseFailAlloc_632_, 4, v_l_572_);
v___x_628_ = v_reuseFailAlloc_632_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_630_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v_r_620_);
lean_ctor_set(v___x_479_, 3, v___x_628_);
lean_ctor_set(v___x_479_, 2, v_v_622_);
lean_ctor_set(v___x_479_, 1, v_k_621_);
lean_ctor_set(v___x_479_, 0, v___x_626_);
v___x_630_ = v___x_479_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_k_621_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v_v_622_);
lean_ctor_set(v_reuseFailAlloc_631_, 3, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_631_, 4, v_r_620_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
else
{
lean_object* v_size_637_; lean_object* v_k_638_; lean_object* v_v_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_650_; 
v_size_637_ = lean_ctor_get(v_r_477_, 0);
v_k_638_ = lean_ctor_get(v_r_477_, 1);
v_v_639_ = lean_ctor_get(v_r_477_, 2);
v_isSharedCheck_650_ = !lean_is_exclusive(v_r_477_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; lean_object* v_unused_652_; 
v_unused_651_ = lean_ctor_get(v_r_477_, 4);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v_r_477_, 3);
lean_dec(v_unused_652_);
v___x_641_ = v_r_477_;
v_isShared_642_ = v_isSharedCheck_650_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_v_639_);
lean_inc(v_k_638_);
lean_inc(v_size_637_);
lean_dec(v_r_477_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_650_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 3, v_r_620_);
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_size_637_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_k_638_);
lean_ctor_set(v_reuseFailAlloc_649_, 2, v_v_639_);
lean_ctor_set(v_reuseFailAlloc_649_, 3, v_r_620_);
lean_ctor_set(v_reuseFailAlloc_649_, 4, v_r_620_);
v___x_644_ = v_reuseFailAlloc_649_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = lean_unsigned_to_nat(2u);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v___x_644_);
lean_ctor_set(v___x_479_, 3, v_r_620_);
lean_ctor_set(v___x_479_, 0, v___x_645_);
v___x_647_ = v___x_479_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_648_, 3, v_r_620_);
lean_ctor_set(v_reuseFailAlloc_648_, 4, v___x_644_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
}
else
{
lean_object* v___x_654_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 3, v_r_477_);
lean_ctor_set(v___x_479_, 0, v___x_483_);
v___x_654_ = v___x_479_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_655_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_655_, 3, v_r_477_);
lean_ctor_set(v_reuseFailAlloc_655_, 4, v_r_477_);
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
case 1:
{
lean_del_object(v___x_479_);
lean_dec(v_v_475_);
lean_dec(v_k_474_);
if (lean_obj_tag(v_l_476_) == 0)
{
if (lean_obj_tag(v_r_477_) == 0)
{
lean_object* v_size_656_; lean_object* v_k_657_; lean_object* v_v_658_; lean_object* v_l_659_; lean_object* v_r_660_; lean_object* v_size_661_; lean_object* v_k_662_; lean_object* v_v_663_; lean_object* v_l_664_; lean_object* v_r_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v_size_656_ = lean_ctor_get(v_l_476_, 0);
v_k_657_ = lean_ctor_get(v_l_476_, 1);
v_v_658_ = lean_ctor_get(v_l_476_, 2);
v_l_659_ = lean_ctor_get(v_l_476_, 3);
v_r_660_ = lean_ctor_get(v_l_476_, 4);
lean_inc(v_r_660_);
v_size_661_ = lean_ctor_get(v_r_477_, 0);
v_k_662_ = lean_ctor_get(v_r_477_, 1);
v_v_663_ = lean_ctor_get(v_r_477_, 2);
v_l_664_ = lean_ctor_get(v_r_477_, 3);
lean_inc(v_l_664_);
v_r_665_ = lean_ctor_get(v_r_477_, 4);
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = lean_nat_dec_lt(v_size_656_, v_size_661_);
if (v___x_667_ == 0)
{
lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_803_; 
lean_inc(v_l_659_);
lean_inc(v_v_658_);
lean_inc(v_k_657_);
v_isSharedCheck_803_ = !lean_is_exclusive(v_l_476_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; lean_object* v_unused_805_; lean_object* v_unused_806_; lean_object* v_unused_807_; lean_object* v_unused_808_; 
v_unused_804_ = lean_ctor_get(v_l_476_, 4);
lean_dec(v_unused_804_);
v_unused_805_ = lean_ctor_get(v_l_476_, 3);
lean_dec(v_unused_805_);
v_unused_806_ = lean_ctor_get(v_l_476_, 2);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_l_476_, 1);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_l_476_, 0);
lean_dec(v_unused_808_);
v___x_669_ = v_l_476_;
v_isShared_670_ = v_isSharedCheck_803_;
goto v_resetjp_668_;
}
else
{
lean_dec(v_l_476_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_803_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v_tree_672_; 
v___x_671_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_657_, v_v_658_, v_l_659_, v_r_660_);
v_tree_672_ = lean_ctor_get(v___x_671_, 2);
if (lean_obj_tag(v_tree_672_) == 0)
{
lean_object* v_k_673_; lean_object* v_v_674_; lean_object* v_size_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
lean_inc_ref(v_tree_672_);
v_k_673_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_k_673_);
v_v_674_ = lean_ctor_get(v___x_671_, 1);
lean_inc(v_v_674_);
lean_dec_ref(v___x_671_);
v_size_675_ = lean_ctor_get(v_tree_672_, 0);
v___x_676_ = lean_unsigned_to_nat(3u);
v___x_677_ = lean_nat_mul(v___x_676_, v_size_675_);
v___x_678_ = lean_nat_dec_lt(v___x_677_, v_size_661_);
lean_dec(v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_682_; 
lean_dec(v_l_664_);
v___x_679_ = lean_nat_add(v___x_666_, v_size_675_);
v___x_680_ = lean_nat_add(v___x_679_, v_size_661_);
lean_dec(v___x_679_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 4, v_r_477_);
lean_ctor_set(v___x_669_, 3, v_tree_672_);
lean_ctor_set(v___x_669_, 2, v_v_674_);
lean_ctor_set(v___x_669_, 1, v_k_673_);
lean_ctor_set(v___x_669_, 0, v___x_680_);
v___x_682_ = v___x_669_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_k_673_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v_v_674_);
lean_ctor_set(v_reuseFailAlloc_683_, 3, v_tree_672_);
lean_ctor_set(v_reuseFailAlloc_683_, 4, v_r_477_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
else
{
lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_738_; 
lean_inc(v_r_665_);
lean_inc(v_v_663_);
lean_inc(v_k_662_);
lean_inc(v_size_661_);
v_isSharedCheck_738_ = !lean_is_exclusive(v_r_477_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; lean_object* v_unused_740_; lean_object* v_unused_741_; lean_object* v_unused_742_; lean_object* v_unused_743_; 
v_unused_739_ = lean_ctor_get(v_r_477_, 4);
lean_dec(v_unused_739_);
v_unused_740_ = lean_ctor_get(v_r_477_, 3);
lean_dec(v_unused_740_);
v_unused_741_ = lean_ctor_get(v_r_477_, 2);
lean_dec(v_unused_741_);
v_unused_742_ = lean_ctor_get(v_r_477_, 1);
lean_dec(v_unused_742_);
v_unused_743_ = lean_ctor_get(v_r_477_, 0);
lean_dec(v_unused_743_);
v___x_685_ = v_r_477_;
v_isShared_686_ = v_isSharedCheck_738_;
goto v_resetjp_684_;
}
else
{
lean_dec(v_r_477_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_738_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v_size_687_; lean_object* v_k_688_; lean_object* v_v_689_; lean_object* v_l_690_; lean_object* v_r_691_; lean_object* v_size_692_; lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v_size_687_ = lean_ctor_get(v_l_664_, 0);
v_k_688_ = lean_ctor_get(v_l_664_, 1);
v_v_689_ = lean_ctor_get(v_l_664_, 2);
v_l_690_ = lean_ctor_get(v_l_664_, 3);
v_r_691_ = lean_ctor_get(v_l_664_, 4);
v_size_692_ = lean_ctor_get(v_r_665_, 0);
v___x_693_ = lean_unsigned_to_nat(2u);
v___x_694_ = lean_nat_mul(v___x_693_, v_size_692_);
v___x_695_ = lean_nat_dec_lt(v_size_687_, v___x_694_);
lean_dec(v___x_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_723_; 
lean_inc(v_r_691_);
lean_inc(v_l_690_);
lean_inc(v_v_689_);
lean_inc(v_k_688_);
v_isSharedCheck_723_ = !lean_is_exclusive(v_l_664_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; lean_object* v_unused_725_; lean_object* v_unused_726_; lean_object* v_unused_727_; lean_object* v_unused_728_; 
v_unused_724_ = lean_ctor_get(v_l_664_, 4);
lean_dec(v_unused_724_);
v_unused_725_ = lean_ctor_get(v_l_664_, 3);
lean_dec(v_unused_725_);
v_unused_726_ = lean_ctor_get(v_l_664_, 2);
lean_dec(v_unused_726_);
v_unused_727_ = lean_ctor_get(v_l_664_, 1);
lean_dec(v_unused_727_);
v_unused_728_ = lean_ctor_get(v_l_664_, 0);
lean_dec(v_unused_728_);
v___x_697_ = v_l_664_;
v_isShared_698_ = v_isSharedCheck_723_;
goto v_resetjp_696_;
}
else
{
lean_dec(v_l_664_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_723_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_713_; 
v___x_699_ = lean_nat_add(v___x_666_, v_size_675_);
v___x_700_ = lean_nat_add(v___x_699_, v_size_661_);
lean_dec(v_size_661_);
if (lean_obj_tag(v_l_690_) == 0)
{
lean_object* v_size_721_; 
v_size_721_ = lean_ctor_get(v_l_690_, 0);
lean_inc(v_size_721_);
v___y_713_ = v_size_721_;
goto v___jp_712_;
}
else
{
lean_object* v___x_722_; 
v___x_722_ = lean_unsigned_to_nat(0u);
v___y_713_ = v___x_722_;
goto v___jp_712_;
}
v___jp_701_:
{
lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_705_ = lean_nat_add(v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec(v___y_703_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 4, v_r_665_);
lean_ctor_set(v___x_697_, 3, v_r_691_);
lean_ctor_set(v___x_697_, 2, v_v_663_);
lean_ctor_set(v___x_697_, 1, v_k_662_);
lean_ctor_set(v___x_697_, 0, v___x_705_);
v___x_707_ = v___x_697_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_k_662_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v_v_663_);
lean_ctor_set(v_reuseFailAlloc_711_, 3, v_r_691_);
lean_ctor_set(v_reuseFailAlloc_711_, 4, v_r_665_);
v___x_707_ = v_reuseFailAlloc_711_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_709_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 4, v___x_707_);
lean_ctor_set(v___x_685_, 3, v___y_702_);
lean_ctor_set(v___x_685_, 2, v_v_689_);
lean_ctor_set(v___x_685_, 1, v_k_688_);
lean_ctor_set(v___x_685_, 0, v___x_700_);
v___x_709_ = v___x_685_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_k_688_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_v_689_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v___y_702_);
lean_ctor_set(v_reuseFailAlloc_710_, 4, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
v___jp_712_:
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = lean_nat_add(v___x_699_, v___y_713_);
lean_dec(v___y_713_);
lean_dec(v___x_699_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 4, v_l_690_);
lean_ctor_set(v___x_669_, 3, v_tree_672_);
lean_ctor_set(v___x_669_, 2, v_v_674_);
lean_ctor_set(v___x_669_, 1, v_k_673_);
lean_ctor_set(v___x_669_, 0, v___x_714_);
v___x_716_ = v___x_669_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_k_673_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_v_674_);
lean_ctor_set(v_reuseFailAlloc_720_, 3, v_tree_672_);
lean_ctor_set(v_reuseFailAlloc_720_, 4, v_l_690_);
v___x_716_ = v_reuseFailAlloc_720_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_717_; 
v___x_717_ = lean_nat_add(v___x_666_, v_size_692_);
if (lean_obj_tag(v_r_691_) == 0)
{
lean_object* v_size_718_; 
v_size_718_ = lean_ctor_get(v_r_691_, 0);
lean_inc(v_size_718_);
v___y_702_ = v___x_716_;
v___y_703_ = v___x_717_;
v___y_704_ = v_size_718_;
goto v___jp_701_;
}
else
{
lean_object* v___x_719_; 
v___x_719_ = lean_unsigned_to_nat(0u);
v___y_702_ = v___x_716_;
v___y_703_ = v___x_717_;
v___y_704_ = v___x_719_;
goto v___jp_701_;
}
}
}
}
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_729_ = lean_nat_add(v___x_666_, v_size_675_);
v___x_730_ = lean_nat_add(v___x_729_, v_size_661_);
lean_dec(v_size_661_);
v___x_731_ = lean_nat_add(v___x_729_, v_size_687_);
lean_dec(v___x_729_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 4, v_l_664_);
lean_ctor_set(v___x_685_, 3, v_tree_672_);
lean_ctor_set(v___x_685_, 2, v_v_674_);
lean_ctor_set(v___x_685_, 1, v_k_673_);
lean_ctor_set(v___x_685_, 0, v___x_731_);
v___x_733_ = v___x_685_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_k_673_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_v_674_);
lean_ctor_set(v_reuseFailAlloc_737_, 3, v_tree_672_);
lean_ctor_set(v_reuseFailAlloc_737_, 4, v_l_664_);
v___x_733_ = v_reuseFailAlloc_737_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_735_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 4, v_r_665_);
lean_ctor_set(v___x_669_, 3, v___x_733_);
lean_ctor_set(v___x_669_, 2, v_v_663_);
lean_ctor_set(v___x_669_, 1, v_k_662_);
lean_ctor_set(v___x_669_, 0, v___x_730_);
v___x_735_ = v___x_669_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_k_662_);
lean_ctor_set(v_reuseFailAlloc_736_, 2, v_v_663_);
lean_ctor_set(v_reuseFailAlloc_736_, 3, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_736_, 4, v_r_665_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
}
else
{
lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_797_; 
lean_inc(v_r_665_);
lean_inc(v_v_663_);
lean_inc(v_k_662_);
lean_inc(v_size_661_);
v_isSharedCheck_797_ = !lean_is_exclusive(v_r_477_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; lean_object* v_unused_799_; lean_object* v_unused_800_; lean_object* v_unused_801_; lean_object* v_unused_802_; 
v_unused_798_ = lean_ctor_get(v_r_477_, 4);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_r_477_, 3);
lean_dec(v_unused_799_);
v_unused_800_ = lean_ctor_get(v_r_477_, 2);
lean_dec(v_unused_800_);
v_unused_801_ = lean_ctor_get(v_r_477_, 1);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_r_477_, 0);
lean_dec(v_unused_802_);
v___x_745_ = v_r_477_;
v_isShared_746_ = v_isSharedCheck_797_;
goto v_resetjp_744_;
}
else
{
lean_dec(v_r_477_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_797_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
if (lean_obj_tag(v_l_664_) == 0)
{
if (lean_obj_tag(v_r_665_) == 0)
{
lean_object* v_k_747_; lean_object* v_v_748_; lean_object* v_size_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
lean_inc(v_tree_672_);
v_k_747_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_k_747_);
v_v_748_ = lean_ctor_get(v___x_671_, 1);
lean_inc(v_v_748_);
lean_dec_ref(v___x_671_);
v_size_749_ = lean_ctor_get(v_l_664_, 0);
v___x_750_ = lean_nat_add(v___x_666_, v_size_661_);
lean_dec(v_size_661_);
v___x_751_ = lean_nat_add(v___x_666_, v_size_749_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 4, v_l_664_);
lean_ctor_set(v___x_745_, 3, v_tree_672_);
lean_ctor_set(v___x_745_, 2, v_v_748_);
lean_ctor_set(v___x_745_, 1, v_k_747_);
lean_ctor_set(v___x_745_, 0, v___x_751_);
v___x_753_ = v___x_745_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_k_747_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v_v_748_);
lean_ctor_set(v_reuseFailAlloc_757_, 3, v_tree_672_);
lean_ctor_set(v_reuseFailAlloc_757_, 4, v_l_664_);
v___x_753_ = v_reuseFailAlloc_757_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 4, v_r_665_);
lean_ctor_set(v___x_669_, 3, v___x_753_);
lean_ctor_set(v___x_669_, 2, v_v_663_);
lean_ctor_set(v___x_669_, 1, v_k_662_);
lean_ctor_set(v___x_669_, 0, v___x_750_);
v___x_755_ = v___x_669_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_k_662_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v_v_663_);
lean_ctor_set(v_reuseFailAlloc_756_, 3, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_756_, 4, v_r_665_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
lean_object* v_k_758_; lean_object* v_v_759_; lean_object* v_k_760_; lean_object* v_v_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_775_; 
lean_dec(v_size_661_);
v_k_758_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_k_758_);
v_v_759_ = lean_ctor_get(v___x_671_, 1);
lean_inc(v_v_759_);
lean_dec_ref(v___x_671_);
v_k_760_ = lean_ctor_get(v_l_664_, 1);
v_v_761_ = lean_ctor_get(v_l_664_, 2);
v_isSharedCheck_775_ = !lean_is_exclusive(v_l_664_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; lean_object* v_unused_777_; lean_object* v_unused_778_; 
v_unused_776_ = lean_ctor_get(v_l_664_, 4);
lean_dec(v_unused_776_);
v_unused_777_ = lean_ctor_get(v_l_664_, 3);
lean_dec(v_unused_777_);
v_unused_778_ = lean_ctor_get(v_l_664_, 0);
lean_dec(v_unused_778_);
v___x_763_ = v_l_664_;
v_isShared_764_ = v_isSharedCheck_775_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_v_761_);
lean_inc(v_k_760_);
lean_dec(v_l_664_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_775_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_765_ = lean_unsigned_to_nat(3u);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 4, v_r_665_);
lean_ctor_set(v___x_763_, 3, v_r_665_);
lean_ctor_set(v___x_763_, 2, v_v_759_);
lean_ctor_set(v___x_763_, 1, v_k_758_);
lean_ctor_set(v___x_763_, 0, v___x_666_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_k_758_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_v_759_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_r_665_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v_r_665_);
v___x_767_ = v_reuseFailAlloc_774_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 3, v_r_665_);
lean_ctor_set(v___x_745_, 0, v___x_666_);
v___x_769_ = v___x_745_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_k_662_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v_v_663_);
lean_ctor_set(v_reuseFailAlloc_773_, 3, v_r_665_);
lean_ctor_set(v_reuseFailAlloc_773_, 4, v_r_665_);
v___x_769_ = v_reuseFailAlloc_773_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_771_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 4, v___x_769_);
lean_ctor_set(v___x_669_, 3, v___x_767_);
lean_ctor_set(v___x_669_, 2, v_v_761_);
lean_ctor_set(v___x_669_, 1, v_k_760_);
lean_ctor_set(v___x_669_, 0, v___x_765_);
v___x_771_ = v___x_669_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_k_760_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_v_761_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_665_) == 0)
{
lean_object* v_k_779_; lean_object* v_v_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
lean_dec(v_size_661_);
v_k_779_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_k_779_);
v_v_780_ = lean_ctor_get(v___x_671_, 1);
lean_inc(v_v_780_);
lean_dec_ref(v___x_671_);
v___x_781_ = lean_unsigned_to_nat(3u);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 4, v_l_664_);
lean_ctor_set(v___x_745_, 2, v_v_780_);
lean_ctor_set(v___x_745_, 1, v_k_779_);
lean_ctor_set(v___x_745_, 0, v___x_666_);
v___x_783_ = v___x_745_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_k_779_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_v_780_);
lean_ctor_set(v_reuseFailAlloc_787_, 3, v_l_664_);
lean_ctor_set(v_reuseFailAlloc_787_, 4, v_l_664_);
v___x_783_ = v_reuseFailAlloc_787_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_785_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 4, v_r_665_);
lean_ctor_set(v___x_669_, 3, v___x_783_);
lean_ctor_set(v___x_669_, 2, v_v_663_);
lean_ctor_set(v___x_669_, 1, v_k_662_);
lean_ctor_set(v___x_669_, 0, v___x_781_);
v___x_785_ = v___x_669_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_k_662_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_v_663_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_786_, 4, v_r_665_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
else
{
lean_object* v_k_788_; lean_object* v_v_789_; lean_object* v___x_791_; 
v_k_788_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_k_788_);
v_v_789_ = lean_ctor_get(v___x_671_, 1);
lean_inc(v_v_789_);
lean_dec_ref(v___x_671_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 3, v_r_665_);
v___x_791_ = v___x_745_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_size_661_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_k_662_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v_v_663_);
lean_ctor_set(v_reuseFailAlloc_796_, 3, v_r_665_);
lean_ctor_set(v_reuseFailAlloc_796_, 4, v_r_665_);
v___x_791_ = v_reuseFailAlloc_796_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = lean_unsigned_to_nat(2u);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 4, v___x_791_);
lean_ctor_set(v___x_669_, 3, v_r_665_);
lean_ctor_set(v___x_669_, 2, v_v_789_);
lean_ctor_set(v___x_669_, 1, v_k_788_);
lean_ctor_set(v___x_669_, 0, v___x_792_);
v___x_794_ = v___x_669_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_k_788_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_v_789_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v_r_665_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v___x_791_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
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
lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_961_; 
lean_inc(v_r_665_);
lean_inc(v_v_663_);
lean_inc(v_k_662_);
v_isSharedCheck_961_ = !lean_is_exclusive(v_r_477_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; lean_object* v_unused_963_; lean_object* v_unused_964_; lean_object* v_unused_965_; lean_object* v_unused_966_; 
v_unused_962_ = lean_ctor_get(v_r_477_, 4);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_r_477_, 3);
lean_dec(v_unused_963_);
v_unused_964_ = lean_ctor_get(v_r_477_, 2);
lean_dec(v_unused_964_);
v_unused_965_ = lean_ctor_get(v_r_477_, 1);
lean_dec(v_unused_965_);
v_unused_966_ = lean_ctor_get(v_r_477_, 0);
lean_dec(v_unused_966_);
v___x_810_ = v_r_477_;
v_isShared_811_ = v_isSharedCheck_961_;
goto v_resetjp_809_;
}
else
{
lean_dec(v_r_477_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_961_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; lean_object* v_tree_813_; 
v___x_812_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_662_, v_v_663_, v_l_664_, v_r_665_);
v_tree_813_ = lean_ctor_get(v___x_812_, 2);
lean_inc(v_tree_813_);
if (lean_obj_tag(v_tree_813_) == 0)
{
lean_object* v_k_814_; lean_object* v_v_815_; lean_object* v_size_816_; lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_k_814_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_k_814_);
v_v_815_ = lean_ctor_get(v___x_812_, 1);
lean_inc(v_v_815_);
lean_dec_ref(v___x_812_);
v_size_816_ = lean_ctor_get(v_tree_813_, 0);
v___x_817_ = lean_unsigned_to_nat(3u);
v___x_818_ = lean_nat_mul(v___x_817_, v_size_816_);
v___x_819_ = lean_nat_dec_lt(v___x_818_, v_size_656_);
lean_dec(v___x_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
lean_dec(v_r_660_);
v___x_820_ = lean_nat_add(v___x_666_, v_size_656_);
v___x_821_ = lean_nat_add(v___x_820_, v_size_816_);
lean_dec(v___x_820_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 4, v_tree_813_);
lean_ctor_set(v___x_810_, 3, v_l_476_);
lean_ctor_set(v___x_810_, 2, v_v_815_);
lean_ctor_set(v___x_810_, 1, v_k_814_);
lean_ctor_set(v___x_810_, 0, v___x_821_);
v___x_823_ = v___x_810_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_k_814_);
lean_ctor_set(v_reuseFailAlloc_824_, 2, v_v_815_);
lean_ctor_set(v_reuseFailAlloc_824_, 3, v_l_476_);
lean_ctor_set(v_reuseFailAlloc_824_, 4, v_tree_813_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
else
{
lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_890_; 
lean_inc(v_l_659_);
lean_inc(v_v_658_);
lean_inc(v_k_657_);
lean_inc(v_size_656_);
v_isSharedCheck_890_ = !lean_is_exclusive(v_l_476_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; lean_object* v_unused_892_; lean_object* v_unused_893_; lean_object* v_unused_894_; lean_object* v_unused_895_; 
v_unused_891_ = lean_ctor_get(v_l_476_, 4);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_l_476_, 3);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_l_476_, 2);
lean_dec(v_unused_893_);
v_unused_894_ = lean_ctor_get(v_l_476_, 1);
lean_dec(v_unused_894_);
v_unused_895_ = lean_ctor_get(v_l_476_, 0);
lean_dec(v_unused_895_);
v___x_826_ = v_l_476_;
v_isShared_827_ = v_isSharedCheck_890_;
goto v_resetjp_825_;
}
else
{
lean_dec(v_l_476_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_890_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v_size_828_; lean_object* v_size_829_; lean_object* v_k_830_; lean_object* v_v_831_; lean_object* v_l_832_; lean_object* v_r_833_; lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v_size_828_ = lean_ctor_get(v_l_659_, 0);
v_size_829_ = lean_ctor_get(v_r_660_, 0);
v_k_830_ = lean_ctor_get(v_r_660_, 1);
v_v_831_ = lean_ctor_get(v_r_660_, 2);
v_l_832_ = lean_ctor_get(v_r_660_, 3);
v_r_833_ = lean_ctor_get(v_r_660_, 4);
v___x_834_ = lean_unsigned_to_nat(2u);
v___x_835_ = lean_nat_mul(v___x_834_, v_size_828_);
v___x_836_ = lean_nat_dec_lt(v_size_829_, v___x_835_);
lean_dec(v___x_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_874_; 
lean_inc(v_r_833_);
lean_inc(v_l_832_);
lean_inc(v_v_831_);
lean_inc(v_k_830_);
lean_del_object(v___x_826_);
v_isSharedCheck_874_ = !lean_is_exclusive(v_r_660_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; lean_object* v_unused_876_; lean_object* v_unused_877_; lean_object* v_unused_878_; lean_object* v_unused_879_; 
v_unused_875_ = lean_ctor_get(v_r_660_, 4);
lean_dec(v_unused_875_);
v_unused_876_ = lean_ctor_get(v_r_660_, 3);
lean_dec(v_unused_876_);
v_unused_877_ = lean_ctor_get(v_r_660_, 2);
lean_dec(v_unused_877_);
v_unused_878_ = lean_ctor_get(v_r_660_, 1);
lean_dec(v_unused_878_);
v_unused_879_ = lean_ctor_get(v_r_660_, 0);
lean_dec(v_unused_879_);
v___x_838_ = v_r_660_;
v_isShared_839_ = v_isSharedCheck_874_;
goto v_resetjp_837_;
}
else
{
lean_dec(v_r_660_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_874_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___x_862_; lean_object* v___y_864_; 
v___x_840_ = lean_nat_add(v___x_666_, v_size_656_);
lean_dec(v_size_656_);
v___x_841_ = lean_nat_add(v___x_840_, v_size_816_);
lean_dec(v___x_840_);
v___x_862_ = lean_nat_add(v___x_666_, v_size_828_);
if (lean_obj_tag(v_l_832_) == 0)
{
lean_object* v_size_872_; 
v_size_872_ = lean_ctor_get(v_l_832_, 0);
lean_inc(v_size_872_);
v___y_864_ = v_size_872_;
goto v___jp_863_;
}
else
{
lean_object* v___x_873_; 
v___x_873_ = lean_unsigned_to_nat(0u);
v___y_864_ = v___x_873_;
goto v___jp_863_;
}
v___jp_842_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = lean_nat_add(v___y_843_, v___y_845_);
lean_dec(v___y_845_);
lean_dec(v___y_843_);
lean_inc_ref(v_tree_813_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 4, v_tree_813_);
lean_ctor_set(v___x_838_, 3, v_r_833_);
lean_ctor_set(v___x_838_, 2, v_v_815_);
lean_ctor_set(v___x_838_, 1, v_k_814_);
lean_ctor_set(v___x_838_, 0, v___x_846_);
v___x_848_ = v___x_838_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_k_814_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_v_815_);
lean_ctor_set(v_reuseFailAlloc_861_, 3, v_r_833_);
lean_ctor_set(v_reuseFailAlloc_861_, 4, v_tree_813_);
v___x_848_ = v_reuseFailAlloc_861_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
v_isSharedCheck_855_ = !lean_is_exclusive(v_tree_813_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; lean_object* v_unused_857_; lean_object* v_unused_858_; lean_object* v_unused_859_; lean_object* v_unused_860_; 
v_unused_856_ = lean_ctor_get(v_tree_813_, 4);
lean_dec(v_unused_856_);
v_unused_857_ = lean_ctor_get(v_tree_813_, 3);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_tree_813_, 2);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v_tree_813_, 1);
lean_dec(v_unused_859_);
v_unused_860_ = lean_ctor_get(v_tree_813_, 0);
lean_dec(v_unused_860_);
v___x_850_ = v_tree_813_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_dec(v_tree_813_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 4, v___x_848_);
lean_ctor_set(v___x_850_, 3, v___y_844_);
lean_ctor_set(v___x_850_, 2, v_v_831_);
lean_ctor_set(v___x_850_, 1, v_k_830_);
lean_ctor_set(v___x_850_, 0, v___x_841_);
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_k_830_);
lean_ctor_set(v_reuseFailAlloc_854_, 2, v_v_831_);
lean_ctor_set(v_reuseFailAlloc_854_, 3, v___y_844_);
lean_ctor_set(v_reuseFailAlloc_854_, 4, v___x_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
v___jp_863_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = lean_nat_add(v___x_862_, v___y_864_);
lean_dec(v___y_864_);
lean_dec(v___x_862_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 4, v_l_832_);
lean_ctor_set(v___x_810_, 3, v_l_659_);
lean_ctor_set(v___x_810_, 2, v_v_658_);
lean_ctor_set(v___x_810_, 1, v_k_657_);
lean_ctor_set(v___x_810_, 0, v___x_865_);
v___x_867_ = v___x_810_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_k_657_);
lean_ctor_set(v_reuseFailAlloc_871_, 2, v_v_658_);
lean_ctor_set(v_reuseFailAlloc_871_, 3, v_l_659_);
lean_ctor_set(v_reuseFailAlloc_871_, 4, v_l_832_);
v___x_867_ = v_reuseFailAlloc_871_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; 
v___x_868_ = lean_nat_add(v___x_666_, v_size_816_);
if (lean_obj_tag(v_r_833_) == 0)
{
lean_object* v_size_869_; 
v_size_869_ = lean_ctor_get(v_r_833_, 0);
lean_inc(v_size_869_);
v___y_843_ = v___x_868_;
v___y_844_ = v___x_867_;
v___y_845_ = v_size_869_;
goto v___jp_842_;
}
else
{
lean_object* v___x_870_; 
v___x_870_ = lean_unsigned_to_nat(0u);
v___y_843_ = v___x_868_;
v___y_844_ = v___x_867_;
v___y_845_ = v___x_870_;
goto v___jp_842_;
}
}
}
}
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_880_ = lean_nat_add(v___x_666_, v_size_656_);
lean_dec(v_size_656_);
v___x_881_ = lean_nat_add(v___x_880_, v_size_816_);
lean_dec(v___x_880_);
v___x_882_ = lean_nat_add(v___x_666_, v_size_816_);
v___x_883_ = lean_nat_add(v___x_882_, v_size_829_);
lean_dec(v___x_882_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 4, v_tree_813_);
lean_ctor_set(v___x_810_, 3, v_r_660_);
lean_ctor_set(v___x_810_, 2, v_v_815_);
lean_ctor_set(v___x_810_, 1, v_k_814_);
lean_ctor_set(v___x_810_, 0, v___x_883_);
v___x_885_ = v___x_810_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_k_814_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_v_815_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_r_660_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v_tree_813_);
v___x_885_ = v_reuseFailAlloc_889_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_887_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 4, v___x_885_);
lean_ctor_set(v___x_826_, 0, v___x_881_);
v___x_887_ = v___x_826_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_k_657_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_v_658_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_l_659_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_659_) == 0)
{
lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_919_; 
lean_inc_ref(v_l_659_);
lean_inc(v_v_658_);
lean_inc(v_k_657_);
lean_inc(v_size_656_);
v_isSharedCheck_919_ = !lean_is_exclusive(v_l_476_);
if (v_isSharedCheck_919_ == 0)
{
lean_object* v_unused_920_; lean_object* v_unused_921_; lean_object* v_unused_922_; lean_object* v_unused_923_; lean_object* v_unused_924_; 
v_unused_920_ = lean_ctor_get(v_l_476_, 4);
lean_dec(v_unused_920_);
v_unused_921_ = lean_ctor_get(v_l_476_, 3);
lean_dec(v_unused_921_);
v_unused_922_ = lean_ctor_get(v_l_476_, 2);
lean_dec(v_unused_922_);
v_unused_923_ = lean_ctor_get(v_l_476_, 1);
lean_dec(v_unused_923_);
v_unused_924_ = lean_ctor_get(v_l_476_, 0);
lean_dec(v_unused_924_);
v___x_897_ = v_l_476_;
v_isShared_898_ = v_isSharedCheck_919_;
goto v_resetjp_896_;
}
else
{
lean_dec(v_l_476_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_919_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
if (lean_obj_tag(v_r_660_) == 0)
{
lean_object* v_k_899_; lean_object* v_v_900_; lean_object* v_size_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
v_k_899_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_k_899_);
v_v_900_ = lean_ctor_get(v___x_812_, 1);
lean_inc(v_v_900_);
lean_dec_ref(v___x_812_);
v_size_901_ = lean_ctor_get(v_r_660_, 0);
v___x_902_ = lean_nat_add(v___x_666_, v_size_656_);
lean_dec(v_size_656_);
v___x_903_ = lean_nat_add(v___x_666_, v_size_901_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 4, v_tree_813_);
lean_ctor_set(v___x_810_, 3, v_r_660_);
lean_ctor_set(v___x_810_, 2, v_v_900_);
lean_ctor_set(v___x_810_, 1, v_k_899_);
lean_ctor_set(v___x_810_, 0, v___x_903_);
v___x_905_ = v___x_810_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_k_899_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v_v_900_);
lean_ctor_set(v_reuseFailAlloc_909_, 3, v_r_660_);
lean_ctor_set(v_reuseFailAlloc_909_, 4, v_tree_813_);
v___x_905_ = v_reuseFailAlloc_909_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_907_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 4, v___x_905_);
lean_ctor_set(v___x_897_, 0, v___x_902_);
v___x_907_ = v___x_897_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_k_657_);
lean_ctor_set(v_reuseFailAlloc_908_, 2, v_v_658_);
lean_ctor_set(v_reuseFailAlloc_908_, 3, v_l_659_);
lean_ctor_set(v_reuseFailAlloc_908_, 4, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
else
{
lean_object* v_k_910_; lean_object* v_v_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
lean_dec(v_size_656_);
v_k_910_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_k_910_);
v_v_911_ = lean_ctor_get(v___x_812_, 1);
lean_inc(v_v_911_);
lean_dec_ref(v___x_812_);
v___x_912_ = lean_unsigned_to_nat(3u);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 4, v_r_660_);
lean_ctor_set(v___x_810_, 3, v_r_660_);
lean_ctor_set(v___x_810_, 2, v_v_911_);
lean_ctor_set(v___x_810_, 1, v_k_910_);
lean_ctor_set(v___x_810_, 0, v___x_666_);
v___x_914_ = v___x_810_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_k_910_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v_v_911_);
lean_ctor_set(v_reuseFailAlloc_918_, 3, v_r_660_);
lean_ctor_set(v_reuseFailAlloc_918_, 4, v_r_660_);
v___x_914_ = v_reuseFailAlloc_918_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_916_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 4, v___x_914_);
lean_ctor_set(v___x_897_, 0, v___x_912_);
v___x_916_ = v___x_897_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_k_657_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_v_658_);
lean_ctor_set(v_reuseFailAlloc_917_, 3, v_l_659_);
lean_ctor_set(v_reuseFailAlloc_917_, 4, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_660_) == 0)
{
lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_949_; 
lean_inc(v_l_659_);
lean_inc(v_v_658_);
lean_inc(v_k_657_);
v_isSharedCheck_949_ = !lean_is_exclusive(v_l_476_);
if (v_isSharedCheck_949_ == 0)
{
lean_object* v_unused_950_; lean_object* v_unused_951_; lean_object* v_unused_952_; lean_object* v_unused_953_; lean_object* v_unused_954_; 
v_unused_950_ = lean_ctor_get(v_l_476_, 4);
lean_dec(v_unused_950_);
v_unused_951_ = lean_ctor_get(v_l_476_, 3);
lean_dec(v_unused_951_);
v_unused_952_ = lean_ctor_get(v_l_476_, 2);
lean_dec(v_unused_952_);
v_unused_953_ = lean_ctor_get(v_l_476_, 1);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_l_476_, 0);
lean_dec(v_unused_954_);
v___x_926_ = v_l_476_;
v_isShared_927_ = v_isSharedCheck_949_;
goto v_resetjp_925_;
}
else
{
lean_dec(v_l_476_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_949_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_k_928_; lean_object* v_v_929_; lean_object* v_k_930_; lean_object* v_v_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_945_; 
v_k_928_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_k_928_);
v_v_929_ = lean_ctor_get(v___x_812_, 1);
lean_inc(v_v_929_);
lean_dec_ref(v___x_812_);
v_k_930_ = lean_ctor_get(v_r_660_, 1);
v_v_931_ = lean_ctor_get(v_r_660_, 2);
v_isSharedCheck_945_ = !lean_is_exclusive(v_r_660_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; lean_object* v_unused_947_; lean_object* v_unused_948_; 
v_unused_946_ = lean_ctor_get(v_r_660_, 4);
lean_dec(v_unused_946_);
v_unused_947_ = lean_ctor_get(v_r_660_, 3);
lean_dec(v_unused_947_);
v_unused_948_ = lean_ctor_get(v_r_660_, 0);
lean_dec(v_unused_948_);
v___x_933_ = v_r_660_;
v_isShared_934_ = v_isSharedCheck_945_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_v_931_);
lean_inc(v_k_930_);
lean_dec(v_r_660_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_945_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = lean_unsigned_to_nat(3u);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 4, v_l_659_);
lean_ctor_set(v___x_933_, 3, v_l_659_);
lean_ctor_set(v___x_933_, 2, v_v_658_);
lean_ctor_set(v___x_933_, 1, v_k_657_);
lean_ctor_set(v___x_933_, 0, v___x_666_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_k_657_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_v_658_);
lean_ctor_set(v_reuseFailAlloc_944_, 3, v_l_659_);
lean_ctor_set(v_reuseFailAlloc_944_, 4, v_l_659_);
v___x_937_ = v_reuseFailAlloc_944_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_939_; 
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 4, v_l_659_);
lean_ctor_set(v___x_810_, 3, v_l_659_);
lean_ctor_set(v___x_810_, 2, v_v_929_);
lean_ctor_set(v___x_810_, 1, v_k_928_);
lean_ctor_set(v___x_810_, 0, v___x_666_);
v___x_939_ = v___x_810_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_k_928_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v_v_929_);
lean_ctor_set(v_reuseFailAlloc_943_, 3, v_l_659_);
lean_ctor_set(v_reuseFailAlloc_943_, 4, v_l_659_);
v___x_939_ = v_reuseFailAlloc_943_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_941_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 4, v___x_939_);
lean_ctor_set(v___x_926_, 3, v___x_937_);
lean_ctor_set(v___x_926_, 2, v_v_931_);
lean_ctor_set(v___x_926_, 1, v_k_930_);
lean_ctor_set(v___x_926_, 0, v___x_935_);
v___x_941_ = v___x_926_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_k_930_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_v_931_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v___x_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
}
else
{
lean_object* v_k_955_; lean_object* v_v_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v_k_955_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_k_955_);
v_v_956_ = lean_ctor_get(v___x_812_, 1);
lean_inc(v_v_956_);
lean_dec_ref(v___x_812_);
v___x_957_ = lean_unsigned_to_nat(2u);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 4, v_r_660_);
lean_ctor_set(v___x_810_, 3, v_l_476_);
lean_ctor_set(v___x_810_, 2, v_v_956_);
lean_ctor_set(v___x_810_, 1, v_k_955_);
lean_ctor_set(v___x_810_, 0, v___x_957_);
v___x_959_ = v___x_810_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_k_955_);
lean_ctor_set(v_reuseFailAlloc_960_, 2, v_v_956_);
lean_ctor_set(v_reuseFailAlloc_960_, 3, v_l_476_);
lean_ctor_set(v_reuseFailAlloc_960_, 4, v_r_660_);
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
}
else
{
return v_l_476_;
}
}
else
{
return v_r_477_;
}
}
default: 
{
lean_object* v_impl_967_; lean_object* v___x_968_; 
v_impl_967_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_472_, v_r_477_);
v___x_968_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_967_) == 0)
{
if (lean_obj_tag(v_l_476_) == 0)
{
lean_object* v_size_969_; lean_object* v_size_970_; lean_object* v_k_971_; lean_object* v_v_972_; lean_object* v_l_973_; lean_object* v_r_974_; lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v_size_969_ = lean_ctor_get(v_impl_967_, 0);
v_size_970_ = lean_ctor_get(v_l_476_, 0);
v_k_971_ = lean_ctor_get(v_l_476_, 1);
v_v_972_ = lean_ctor_get(v_l_476_, 2);
v_l_973_ = lean_ctor_get(v_l_476_, 3);
v_r_974_ = lean_ctor_get(v_l_476_, 4);
lean_inc(v_r_974_);
v___x_975_ = lean_unsigned_to_nat(3u);
v___x_976_ = lean_nat_mul(v___x_975_, v_size_969_);
v___x_977_ = lean_nat_dec_lt(v___x_976_, v_size_970_);
lean_dec(v___x_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
lean_dec(v_r_974_);
v___x_978_ = lean_nat_add(v___x_968_, v_size_970_);
v___x_979_ = lean_nat_add(v___x_978_, v_size_969_);
lean_dec(v___x_978_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v_impl_967_);
lean_ctor_set(v___x_479_, 0, v___x_979_);
v___x_981_ = v___x_479_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_982_, 3, v_l_476_);
lean_ctor_set(v_reuseFailAlloc_982_, 4, v_impl_967_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
else
{
lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1048_; 
lean_inc(v_l_973_);
lean_inc(v_v_972_);
lean_inc(v_k_971_);
lean_inc(v_size_970_);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_l_476_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; lean_object* v_unused_1050_; lean_object* v_unused_1051_; lean_object* v_unused_1052_; lean_object* v_unused_1053_; 
v_unused_1049_ = lean_ctor_get(v_l_476_, 4);
lean_dec(v_unused_1049_);
v_unused_1050_ = lean_ctor_get(v_l_476_, 3);
lean_dec(v_unused_1050_);
v_unused_1051_ = lean_ctor_get(v_l_476_, 2);
lean_dec(v_unused_1051_);
v_unused_1052_ = lean_ctor_get(v_l_476_, 1);
lean_dec(v_unused_1052_);
v_unused_1053_ = lean_ctor_get(v_l_476_, 0);
lean_dec(v_unused_1053_);
v___x_984_ = v_l_476_;
v_isShared_985_ = v_isSharedCheck_1048_;
goto v_resetjp_983_;
}
else
{
lean_dec(v_l_476_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1048_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v_size_986_; lean_object* v_size_987_; lean_object* v_k_988_; lean_object* v_v_989_; lean_object* v_l_990_; lean_object* v_r_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v_size_986_ = lean_ctor_get(v_l_973_, 0);
v_size_987_ = lean_ctor_get(v_r_974_, 0);
v_k_988_ = lean_ctor_get(v_r_974_, 1);
v_v_989_ = lean_ctor_get(v_r_974_, 2);
v_l_990_ = lean_ctor_get(v_r_974_, 3);
v_r_991_ = lean_ctor_get(v_r_974_, 4);
v___x_992_ = lean_unsigned_to_nat(2u);
v___x_993_ = lean_nat_mul(v___x_992_, v_size_986_);
v___x_994_ = lean_nat_dec_lt(v_size_987_, v___x_993_);
lean_dec(v___x_993_);
if (v___x_994_ == 0)
{
lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1023_; 
lean_inc(v_r_991_);
lean_inc(v_l_990_);
lean_inc(v_v_989_);
lean_inc(v_k_988_);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_r_974_);
if (v_isSharedCheck_1023_ == 0)
{
lean_object* v_unused_1024_; lean_object* v_unused_1025_; lean_object* v_unused_1026_; lean_object* v_unused_1027_; lean_object* v_unused_1028_; 
v_unused_1024_ = lean_ctor_get(v_r_974_, 4);
lean_dec(v_unused_1024_);
v_unused_1025_ = lean_ctor_get(v_r_974_, 3);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_r_974_, 2);
lean_dec(v_unused_1026_);
v_unused_1027_ = lean_ctor_get(v_r_974_, 1);
lean_dec(v_unused_1027_);
v_unused_1028_ = lean_ctor_get(v_r_974_, 0);
lean_dec(v_unused_1028_);
v___x_996_ = v_r_974_;
v_isShared_997_ = v_isSharedCheck_1023_;
goto v_resetjp_995_;
}
else
{
lean_dec(v_r_974_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1023_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___x_1011_; lean_object* v___y_1013_; 
v___x_998_ = lean_nat_add(v___x_968_, v_size_970_);
lean_dec(v_size_970_);
v___x_999_ = lean_nat_add(v___x_998_, v_size_969_);
lean_dec(v___x_998_);
v___x_1011_ = lean_nat_add(v___x_968_, v_size_986_);
if (lean_obj_tag(v_l_990_) == 0)
{
lean_object* v_size_1021_; 
v_size_1021_ = lean_ctor_get(v_l_990_, 0);
lean_inc(v_size_1021_);
v___y_1013_ = v_size_1021_;
goto v___jp_1012_;
}
else
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_unsigned_to_nat(0u);
v___y_1013_ = v___x_1022_;
goto v___jp_1012_;
}
v___jp_1000_:
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1004_ = lean_nat_add(v___y_1001_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec(v___y_1001_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 4, v_impl_967_);
lean_ctor_set(v___x_996_, 3, v_r_991_);
lean_ctor_set(v___x_996_, 2, v_v_475_);
lean_ctor_set(v___x_996_, 1, v_k_474_);
lean_ctor_set(v___x_996_, 0, v___x_1004_);
v___x_1006_ = v___x_996_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_1010_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_1010_, 3, v_r_991_);
lean_ctor_set(v_reuseFailAlloc_1010_, 4, v_impl_967_);
v___x_1006_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1008_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 4, v___x_1006_);
lean_ctor_set(v___x_984_, 3, v___y_1002_);
lean_ctor_set(v___x_984_, 2, v_v_989_);
lean_ctor_set(v___x_984_, 1, v_k_988_);
lean_ctor_set(v___x_984_, 0, v___x_999_);
v___x_1008_ = v___x_984_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_k_988_);
lean_ctor_set(v_reuseFailAlloc_1009_, 2, v_v_989_);
lean_ctor_set(v_reuseFailAlloc_1009_, 3, v___y_1002_);
lean_ctor_set(v_reuseFailAlloc_1009_, 4, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
v___jp_1012_:
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1014_ = lean_nat_add(v___x_1011_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec(v___x_1011_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v_l_990_);
lean_ctor_set(v___x_479_, 3, v_l_973_);
lean_ctor_set(v___x_479_, 2, v_v_972_);
lean_ctor_set(v___x_479_, 1, v_k_971_);
lean_ctor_set(v___x_479_, 0, v___x_1014_);
v___x_1016_ = v___x_479_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_k_971_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v_v_972_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v_l_973_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v_l_990_);
v___x_1016_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_nat_add(v___x_968_, v_size_969_);
if (lean_obj_tag(v_r_991_) == 0)
{
lean_object* v_size_1018_; 
v_size_1018_ = lean_ctor_get(v_r_991_, 0);
lean_inc(v_size_1018_);
v___y_1001_ = v___x_1017_;
v___y_1002_ = v___x_1016_;
v___y_1003_ = v_size_1018_;
goto v___jp_1000_;
}
else
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_unsigned_to_nat(0u);
v___y_1001_ = v___x_1017_;
v___y_1002_ = v___x_1016_;
v___y_1003_ = v___x_1019_;
goto v___jp_1000_;
}
}
}
}
}
else
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
lean_del_object(v___x_479_);
v___x_1029_ = lean_nat_add(v___x_968_, v_size_970_);
lean_dec(v_size_970_);
v___x_1030_ = lean_nat_add(v___x_1029_, v_size_969_);
lean_dec(v___x_1029_);
v___x_1031_ = lean_nat_add(v___x_968_, v_size_969_);
v___x_1032_ = lean_nat_add(v___x_1031_, v_size_987_);
lean_dec(v___x_1031_);
lean_inc_ref(v_impl_967_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 4, v_impl_967_);
lean_ctor_set(v___x_984_, 3, v_r_974_);
lean_ctor_set(v___x_984_, 2, v_v_475_);
lean_ctor_set(v___x_984_, 1, v_k_474_);
lean_ctor_set(v___x_984_, 0, v___x_1032_);
v___x_1034_ = v___x_984_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_1047_, 3, v_r_974_);
lean_ctor_set(v_reuseFailAlloc_1047_, 4, v_impl_967_);
v___x_1034_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
v_isSharedCheck_1041_ = !lean_is_exclusive(v_impl_967_);
if (v_isSharedCheck_1041_ == 0)
{
lean_object* v_unused_1042_; lean_object* v_unused_1043_; lean_object* v_unused_1044_; lean_object* v_unused_1045_; lean_object* v_unused_1046_; 
v_unused_1042_ = lean_ctor_get(v_impl_967_, 4);
lean_dec(v_unused_1042_);
v_unused_1043_ = lean_ctor_get(v_impl_967_, 3);
lean_dec(v_unused_1043_);
v_unused_1044_ = lean_ctor_get(v_impl_967_, 2);
lean_dec(v_unused_1044_);
v_unused_1045_ = lean_ctor_get(v_impl_967_, 1);
lean_dec(v_unused_1045_);
v_unused_1046_ = lean_ctor_get(v_impl_967_, 0);
lean_dec(v_unused_1046_);
v___x_1036_ = v_impl_967_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_dec(v_impl_967_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1034_);
lean_ctor_set(v___x_1036_, 3, v_l_973_);
lean_ctor_set(v___x_1036_, 2, v_v_972_);
lean_ctor_set(v___x_1036_, 1, v_k_971_);
lean_ctor_set(v___x_1036_, 0, v___x_1030_);
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_k_971_);
lean_ctor_set(v_reuseFailAlloc_1040_, 2, v_v_972_);
lean_ctor_set(v_reuseFailAlloc_1040_, 3, v_l_973_);
lean_ctor_set(v_reuseFailAlloc_1040_, 4, v___x_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v_size_1054_ = lean_ctor_get(v_impl_967_, 0);
v___x_1055_ = lean_nat_add(v___x_968_, v_size_1054_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v_impl_967_);
lean_ctor_set(v___x_479_, 0, v___x_1055_);
v___x_1057_ = v___x_479_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_1058_, 3, v_l_476_);
lean_ctor_set(v_reuseFailAlloc_1058_, 4, v_impl_967_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
else
{
if (lean_obj_tag(v_l_476_) == 0)
{
lean_object* v_l_1059_; 
v_l_1059_ = lean_ctor_get(v_l_476_, 3);
if (lean_obj_tag(v_l_1059_) == 0)
{
lean_object* v_r_1060_; 
lean_inc_ref(v_l_1059_);
v_r_1060_ = lean_ctor_get(v_l_476_, 4);
lean_inc(v_r_1060_);
if (lean_obj_tag(v_r_1060_) == 0)
{
lean_object* v_size_1061_; lean_object* v_k_1062_; lean_object* v_v_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1076_; 
v_size_1061_ = lean_ctor_get(v_l_476_, 0);
v_k_1062_ = lean_ctor_get(v_l_476_, 1);
v_v_1063_ = lean_ctor_get(v_l_476_, 2);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_l_476_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; lean_object* v_unused_1078_; 
v_unused_1077_ = lean_ctor_get(v_l_476_, 4);
lean_dec(v_unused_1077_);
v_unused_1078_ = lean_ctor_get(v_l_476_, 3);
lean_dec(v_unused_1078_);
v___x_1065_ = v_l_476_;
v_isShared_1066_ = v_isSharedCheck_1076_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_v_1063_);
lean_inc(v_k_1062_);
lean_inc(v_size_1061_);
lean_dec(v_l_476_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1076_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v_size_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v_size_1067_ = lean_ctor_get(v_r_1060_, 0);
v___x_1068_ = lean_nat_add(v___x_968_, v_size_1061_);
lean_dec(v_size_1061_);
v___x_1069_ = lean_nat_add(v___x_968_, v_size_1067_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v_impl_967_);
lean_ctor_set(v___x_1065_, 3, v_r_1060_);
lean_ctor_set(v___x_1065_, 2, v_v_475_);
lean_ctor_set(v___x_1065_, 1, v_k_474_);
lean_ctor_set(v___x_1065_, 0, v___x_1069_);
v___x_1071_ = v___x_1065_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_1075_, 3, v_r_1060_);
lean_ctor_set(v_reuseFailAlloc_1075_, 4, v_impl_967_);
v___x_1071_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1073_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v___x_1071_);
lean_ctor_set(v___x_479_, 3, v_l_1059_);
lean_ctor_set(v___x_479_, 2, v_v_1063_);
lean_ctor_set(v___x_479_, 1, v_k_1062_);
lean_ctor_set(v___x_479_, 0, v___x_1068_);
v___x_1073_ = v___x_479_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_k_1062_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_v_1063_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v_l_1059_);
lean_ctor_set(v_reuseFailAlloc_1074_, 4, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
else
{
lean_object* v_k_1079_; lean_object* v_v_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1091_; 
v_k_1079_ = lean_ctor_get(v_l_476_, 1);
v_v_1080_ = lean_ctor_get(v_l_476_, 2);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_l_476_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; lean_object* v_unused_1093_; lean_object* v_unused_1094_; 
v_unused_1092_ = lean_ctor_get(v_l_476_, 4);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_l_476_, 3);
lean_dec(v_unused_1093_);
v_unused_1094_ = lean_ctor_get(v_l_476_, 0);
lean_dec(v_unused_1094_);
v___x_1082_ = v_l_476_;
v_isShared_1083_ = v_isSharedCheck_1091_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_v_1080_);
lean_inc(v_k_1079_);
lean_dec(v_l_476_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1091_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1084_ = lean_unsigned_to_nat(3u);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 3, v_r_1060_);
lean_ctor_set(v___x_1082_, 2, v_v_475_);
lean_ctor_set(v___x_1082_, 1, v_k_474_);
lean_ctor_set(v___x_1082_, 0, v___x_968_);
v___x_1086_ = v___x_1082_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_1090_, 3, v_r_1060_);
lean_ctor_set(v_reuseFailAlloc_1090_, 4, v_r_1060_);
v___x_1086_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1088_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v___x_1086_);
lean_ctor_set(v___x_479_, 3, v_l_1059_);
lean_ctor_set(v___x_479_, 2, v_v_1080_);
lean_ctor_set(v___x_479_, 1, v_k_1079_);
lean_ctor_set(v___x_479_, 0, v___x_1084_);
v___x_1088_ = v___x_479_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_k_1079_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_v_1080_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_l_1059_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
else
{
lean_object* v_r_1095_; 
v_r_1095_ = lean_ctor_get(v_l_476_, 4);
lean_inc(v_r_1095_);
if (lean_obj_tag(v_r_1095_) == 0)
{
lean_object* v_k_1096_; lean_object* v_v_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1120_; 
lean_inc(v_l_1059_);
v_k_1096_ = lean_ctor_get(v_l_476_, 1);
v_v_1097_ = lean_ctor_get(v_l_476_, 2);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_l_476_);
if (v_isSharedCheck_1120_ == 0)
{
lean_object* v_unused_1121_; lean_object* v_unused_1122_; lean_object* v_unused_1123_; 
v_unused_1121_ = lean_ctor_get(v_l_476_, 4);
lean_dec(v_unused_1121_);
v_unused_1122_ = lean_ctor_get(v_l_476_, 3);
lean_dec(v_unused_1122_);
v_unused_1123_ = lean_ctor_get(v_l_476_, 0);
lean_dec(v_unused_1123_);
v___x_1099_ = v_l_476_;
v_isShared_1100_ = v_isSharedCheck_1120_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_v_1097_);
lean_inc(v_k_1096_);
lean_dec(v_l_476_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1120_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v_k_1101_; lean_object* v_v_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1116_; 
v_k_1101_ = lean_ctor_get(v_r_1095_, 1);
v_v_1102_ = lean_ctor_get(v_r_1095_, 2);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_r_1095_);
if (v_isSharedCheck_1116_ == 0)
{
lean_object* v_unused_1117_; lean_object* v_unused_1118_; lean_object* v_unused_1119_; 
v_unused_1117_ = lean_ctor_get(v_r_1095_, 4);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v_r_1095_, 3);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v_r_1095_, 0);
lean_dec(v_unused_1119_);
v___x_1104_ = v_r_1095_;
v_isShared_1105_ = v_isSharedCheck_1116_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_v_1102_);
lean_inc(v_k_1101_);
lean_dec(v_r_1095_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1116_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1106_ = lean_unsigned_to_nat(3u);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 4, v_l_1059_);
lean_ctor_set(v___x_1104_, 3, v_l_1059_);
lean_ctor_set(v___x_1104_, 2, v_v_1097_);
lean_ctor_set(v___x_1104_, 1, v_k_1096_);
lean_ctor_set(v___x_1104_, 0, v___x_968_);
v___x_1108_ = v___x_1104_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_k_1096_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_v_1097_);
lean_ctor_set(v_reuseFailAlloc_1115_, 3, v_l_1059_);
lean_ctor_set(v_reuseFailAlloc_1115_, 4, v_l_1059_);
v___x_1108_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1110_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 4, v_l_1059_);
lean_ctor_set(v___x_1099_, 2, v_v_475_);
lean_ctor_set(v___x_1099_, 1, v_k_474_);
lean_ctor_set(v___x_1099_, 0, v___x_968_);
v___x_1110_ = v___x_1099_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_l_1059_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v_l_1059_);
v___x_1110_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1112_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v___x_1110_);
lean_ctor_set(v___x_479_, 3, v___x_1108_);
lean_ctor_set(v___x_479_, 2, v_v_1102_);
lean_ctor_set(v___x_479_, 1, v_k_1101_);
lean_ctor_set(v___x_479_, 0, v___x_1106_);
v___x_1112_ = v___x_479_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v___x_1108_);
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
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1124_ = lean_unsigned_to_nat(2u);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v_r_1095_);
lean_ctor_set(v___x_479_, 0, v___x_1124_);
v___x_1126_ = v___x_479_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_1127_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_1127_, 3, v_l_476_);
lean_ctor_set(v_reuseFailAlloc_1127_, 4, v_r_1095_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v___x_1129_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v_l_476_);
lean_ctor_set(v___x_479_, 0, v___x_968_);
v___x_1129_ = v___x_479_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_k_474_);
lean_ctor_set(v_reuseFailAlloc_1130_, 2, v_v_475_);
lean_ctor_set(v_reuseFailAlloc_1130_, 3, v_l_476_);
lean_ctor_set(v_reuseFailAlloc_1130_, 4, v_l_476_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
}
}
else
{
return v_t_473_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg___boxed(lean_object* v_k_1133_, lean_object* v_t_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_1133_, v_t_1134_);
lean_dec(v_k_1133_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString(lean_object* v_declName_1136_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1138_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1139_ = lean_st_ref_take(v___x_1138_);
v___x_1140_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_declName_1136_, v___x_1139_);
v___x_1141_ = lean_st_ref_put(v___x_1138_, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString___boxed(lean_object* v_declName_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_removeBuiltinDocString(v_declName_1143_);
lean_dec(v_declName_1143_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(lean_object* v_00_u03b2_1146_, lean_object* v_k_1147_, lean_object* v_t_1148_, lean_object* v_h_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_1147_, v_t_1148_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___boxed(lean_object* v_00_u03b2_1151_, lean_object* v_k_1152_, lean_object* v_t_1153_, lean_object* v_h_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(v_00_u03b2_1151_, v_k_1152_, v_t_1153_, v_h_1154_);
lean_dec(v_k_1152_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings(){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1157_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1158_ = lean_st_ref_get(v___x_1157_);
v___x_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings___boxed(lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_getBuiltinVersoDocStrings();
return v_res_1161_;
}
}
static lean_object* _init_l_Lean_throwIfHasDocString___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l_Lean_throwIfHasDocString___redArg___lam__0___closed__0));
v___x_1164_ = l_Lean_stringToMessageData(v___x_1163_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_throwIfHasDocString___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_Lean_throwIfHasDocString___redArg___lam__0___closed__2));
v___x_1167_ = l_Lean_stringToMessageData(v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwIfHasDocString___redArg___lam__0(lean_object* v_toPure_1168_, lean_object* v_declName_1169_, lean_object* v_inst_1170_, lean_object* v_inst_1171_, lean_object* v___x_1172_, lean_object* v___x_1173_, lean_object* v_env_1174_){
_start:
{
uint8_t v___y_1176_; lean_object* v___x_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1186_ = l_Lean_docStringExt;
v___x_1187_ = lean_box(1);
lean_inc(v_declName_1169_);
lean_inc_ref(v_env_1174_);
v___x_1188_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_1172_, v___x_1186_, v_env_1174_, v_declName_1169_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_1169_);
v___x_1190_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_1173_, v___x_1189_, v_env_1174_, v_declName_1169_, v___x_1187_);
v___y_1176_ = v___x_1190_;
goto v___jp_1175_;
}
else
{
lean_dec_ref(v_env_1174_);
lean_dec_ref(v___x_1173_);
v___y_1176_ = v___x_1188_;
goto v___jp_1175_;
}
v___jp_1175_:
{
if (v___y_1176_ == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec_ref(v_inst_1171_);
lean_dec_ref(v_inst_1170_);
lean_dec(v_declName_1169_);
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_apply_2(v_toPure_1168_, lean_box(0), v___x_1177_);
return v___x_1178_;
}
else
{
lean_object* v___x_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec(v_toPure_1168_);
v___x_1179_ = lean_obj_once(&l_Lean_throwIfHasDocString___redArg___lam__0___closed__1, &l_Lean_throwIfHasDocString___redArg___lam__0___closed__1_once, _init_l_Lean_throwIfHasDocString___redArg___lam__0___closed__1);
v___x_1180_ = 0;
v___x_1181_ = l_Lean_MessageData_ofConstName(v_declName_1169_, v___x_1180_);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1179_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = lean_obj_once(&l_Lean_throwIfHasDocString___redArg___lam__0___closed__3, &l_Lean_throwIfHasDocString___redArg___lam__0___closed__3_once, _init_l_Lean_throwIfHasDocString___redArg___lam__0___closed__3);
v___x_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = l_Lean_throwError___redArg(v_inst_1170_, v_inst_1171_, v___x_1184_);
return v___x_1185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwIfHasDocString___redArg(lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_declName_1195_){
_start:
{
lean_object* v_toApplicative_1196_; lean_object* v_toBind_1197_; lean_object* v_getEnv_1198_; lean_object* v_toPure_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; 
v_toApplicative_1196_ = lean_ctor_get(v_inst_1192_, 0);
v_toBind_1197_ = lean_ctor_get(v_inst_1192_, 1);
lean_inc(v_toBind_1197_);
v_getEnv_1198_ = lean_ctor_get(v_inst_1194_, 0);
lean_inc(v_getEnv_1198_);
lean_dec_ref(v_inst_1194_);
v_toPure_1199_ = lean_ctor_get(v_toApplicative_1196_, 1);
lean_inc(v_toPure_1199_);
v___x_1200_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default));
v___x_1201_ = ((lean_object*)(l_Lean_throwIfHasDocString___redArg___closed__0));
v___f_1202_ = lean_alloc_closure((void*)(l_Lean_throwIfHasDocString___redArg___lam__0), 7, 6);
lean_closure_set(v___f_1202_, 0, v_toPure_1199_);
lean_closure_set(v___f_1202_, 1, v_declName_1195_);
lean_closure_set(v___f_1202_, 2, v_inst_1192_);
lean_closure_set(v___f_1202_, 3, v_inst_1193_);
lean_closure_set(v___f_1202_, 4, v___x_1201_);
lean_closure_set(v___f_1202_, 5, v___x_1200_);
v___x_1203_ = lean_apply_4(v_toBind_1197_, lean_box(0), lean_box(0), v_getEnv_1198_, v___f_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwIfHasDocString(lean_object* v_m_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_, lean_object* v_declName_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_throwIfHasDocString___redArg(v_inst_1205_, v_inst_1206_, v_inst_1207_, v_declName_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__0(lean_object* v_docString_1210_, lean_object* v_declName_1211_, lean_object* v_env_1212_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; lean_object* v___x_1216_; 
v___x_1213_ = l_Lean_docStringExt;
v___x_1214_ = l_String_removeLeadingSpaces(v_docString_1210_);
v___x_1215_ = 1;
v___x_1216_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1213_, v_env_1212_, v_declName_1211_, v___x_1214_, v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__1(lean_object* v_modifyEnv_1217_, lean_object* v___f_1218_, lean_object* v_____r_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_apply_1(v_modifyEnv_1217_, v___f_1218_);
return v___x_1220_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = ((lean_object*)(l_Lean_addDocStringCore___redArg___lam__2___closed__0));
v___x_1223_ = l_Lean_stringToMessageData(v___x_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2(lean_object* v_declName_1224_, lean_object* v_modifyEnv_1225_, lean_object* v___f_1226_, lean_object* v_inst_1227_, lean_object* v_inst_1228_, lean_object* v_toBind_1229_, lean_object* v___f_1230_, lean_object* v_____do__lift_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1231_, v_declName_1224_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v___x_1233_; 
lean_dec(v___f_1230_);
lean_dec(v_toBind_1229_);
lean_dec_ref(v_inst_1228_);
lean_dec_ref(v_inst_1227_);
lean_dec(v_declName_1224_);
v___x_1233_ = lean_apply_1(v_modifyEnv_1225_, v___f_1226_);
return v___x_1233_;
}
else
{
uint8_t v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_dec_ref_known(v___x_1232_, 1);
lean_dec_ref(v___f_1226_);
lean_dec(v_modifyEnv_1225_);
v___x_1234_ = 0;
v___x_1235_ = lean_obj_once(&l_Lean_throwIfHasDocString___redArg___lam__0___closed__1, &l_Lean_throwIfHasDocString___redArg___lam__0___closed__1_once, _init_l_Lean_throwIfHasDocString___redArg___lam__0___closed__1);
v___x_1236_ = l_Lean_MessageData_ofConstName(v_declName_1224_, v___x_1234_);
v___x_1237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__1, &l_Lean_addDocStringCore___redArg___lam__2___closed__1_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1);
v___x_1239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = l_Lean_throwError___redArg(v_inst_1227_, v_inst_1228_, v___x_1239_);
v___x_1241_ = lean_apply_4(v_toBind_1229_, lean_box(0), lean_box(0), v___x_1240_, v___f_1230_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_1242_, lean_object* v_modifyEnv_1243_, lean_object* v___f_1244_, lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v_toBind_1247_, lean_object* v___f_1248_, lean_object* v_____do__lift_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_addDocStringCore___redArg___lam__2(v_declName_1242_, v_modifyEnv_1243_, v___f_1244_, v_inst_1245_, v_inst_1246_, v_toBind_1247_, v___f_1248_, v_____do__lift_1249_);
lean_dec_ref(v_____do__lift_1249_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg(lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_declName_1254_, lean_object* v_docString_1255_){
_start:
{
lean_object* v_toBind_1256_; lean_object* v_getEnv_1257_; lean_object* v_modifyEnv_1258_; lean_object* v___f_1259_; lean_object* v___f_1260_; lean_object* v___f_1261_; lean_object* v___x_1262_; 
v_toBind_1256_ = lean_ctor_get(v_inst_1251_, 1);
lean_inc_n(v_toBind_1256_, 2);
v_getEnv_1257_ = lean_ctor_get(v_inst_1253_, 0);
lean_inc(v_getEnv_1257_);
v_modifyEnv_1258_ = lean_ctor_get(v_inst_1253_, 1);
lean_inc_n(v_modifyEnv_1258_, 2);
lean_dec_ref(v_inst_1253_);
lean_inc(v_declName_1254_);
v___f_1259_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1259_, 0, v_docString_1255_);
lean_closure_set(v___f_1259_, 1, v_declName_1254_);
lean_inc_ref(v___f_1259_);
v___f_1260_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1260_, 0, v_modifyEnv_1258_);
lean_closure_set(v___f_1260_, 1, v___f_1259_);
v___f_1261_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1261_, 0, v_declName_1254_);
lean_closure_set(v___f_1261_, 1, v_modifyEnv_1258_);
lean_closure_set(v___f_1261_, 2, v___f_1259_);
lean_closure_set(v___f_1261_, 3, v_inst_1251_);
lean_closure_set(v___f_1261_, 4, v_inst_1252_);
lean_closure_set(v___f_1261_, 5, v_toBind_1256_);
lean_closure_set(v___f_1261_, 6, v___f_1260_);
v___x_1262_ = lean_apply_4(v_toBind_1256_, lean_box(0), lean_box(0), v_getEnv_1257_, v___f_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore(lean_object* v_m_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v_declName_1268_, lean_object* v_docString_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_addDocStringCore___redArg(v_inst_1264_, v_inst_1265_, v_inst_1266_, v_declName_1268_, v_docString_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___boxed(lean_object* v_m_1271_, lean_object* v_inst_1272_, lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_inst_1275_, lean_object* v_declName_1276_, lean_object* v_docString_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_addDocStringCore(v_m_1271_, v_inst_1272_, v_inst_1273_, v_inst_1274_, v_inst_1275_, v_declName_1276_, v_docString_1277_);
lean_dec(v_inst_1275_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__0(lean_object* v_declName_1280_, lean_object* v_ps_1281_){
_start:
{
lean_object* v_importedEntries_1282_; lean_object* v_state_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1292_; 
v_importedEntries_1282_ = lean_ctor_get(v_ps_1281_, 0);
v_state_1283_ = lean_ctor_get(v_ps_1281_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_ps_1281_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1285_ = v_ps_1281_;
v_isShared_1286_ = v_isSharedCheck_1292_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_state_1283_);
lean_inc(v_importedEntries_1282_);
lean_dec(v_ps_1281_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1292_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1287_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__0___closed__0));
v___x_1288_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_1287_, v_declName_1280_, v_state_1283_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1288_);
v___x_1290_ = v___x_1285_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_importedEntries_1282_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__1(lean_object* v___f_1293_, lean_object* v_env_1294_){
_start:
{
lean_object* v___x_1295_; lean_object* v_toEnvExtension_1296_; uint8_t v_logWrites_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1295_ = l_Lean_docStringExt;
v_toEnvExtension_1296_ = lean_ctor_get(v___x_1295_, 0);
v_logWrites_1297_ = lean_ctor_get_uint8(v_toEnvExtension_1296_, sizeof(void*)*6);
v___x_1298_ = lean_box(2);
v___x_1299_ = lean_box(0);
v___x_1300_ = 1;
if (v_logWrites_1297_ == 0)
{
lean_object* v___x_1301_; 
lean_inc_ref(v_toEnvExtension_1296_);
v___x_1301_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1296_, v_env_1294_, v___f_1293_, v___x_1298_, v___x_1299_, v___x_1300_);
return v___x_1301_;
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_inc_ref_n(v_toEnvExtension_1296_, 2);
v___x_1302_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1296_, v_env_1294_);
lean_dec_ref(v_env_1294_);
v___x_1303_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1296_, v___x_1302_, v___f_1293_, v___x_1298_, v___x_1299_, v___x_1300_);
return v___x_1303_;
}
}
}
static lean_object* _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__3___closed__0));
v___x_1306_ = l_Lean_stringToMessageData(v___x_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3(lean_object* v_declName_1307_, lean_object* v_modifyEnv_1308_, lean_object* v___f_1309_, lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_toBind_1312_, lean_object* v___f_1313_, lean_object* v_____do__lift_1314_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1314_, v_declName_1307_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v___x_1316_; 
lean_dec(v___f_1313_);
lean_dec(v_toBind_1312_);
lean_dec_ref(v_inst_1311_);
lean_dec_ref(v_inst_1310_);
lean_dec(v_declName_1307_);
v___x_1316_ = lean_apply_1(v_modifyEnv_1308_, v___f_1309_);
return v___x_1316_;
}
else
{
uint8_t v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec_ref_known(v___x_1315_, 1);
lean_dec_ref(v___f_1309_);
lean_dec(v_modifyEnv_1308_);
v___x_1317_ = 0;
v___x_1318_ = lean_obj_once(&l_Lean_removeDocStringCore___redArg___lam__3___closed__1, &l_Lean_removeDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1);
v___x_1319_ = l_Lean_MessageData_ofConstName(v_declName_1307_, v___x_1317_);
v___x_1320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1318_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
v___x_1321_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__1, &l_Lean_addDocStringCore___redArg___lam__2___closed__1_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1);
v___x_1322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1320_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = l_Lean_throwError___redArg(v_inst_1310_, v_inst_1311_, v___x_1322_);
v___x_1324_ = lean_apply_4(v_toBind_1312_, lean_box(0), lean_box(0), v___x_1323_, v___f_1313_);
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_1325_, lean_object* v_modifyEnv_1326_, lean_object* v___f_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_toBind_1330_, lean_object* v___f_1331_, lean_object* v_____do__lift_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_removeDocStringCore___redArg___lam__3(v_declName_1325_, v_modifyEnv_1326_, v___f_1327_, v_inst_1328_, v_inst_1329_, v_toBind_1330_, v___f_1331_, v_____do__lift_1332_);
lean_dec_ref(v_____do__lift_1332_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg(lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_declName_1337_){
_start:
{
lean_object* v_toBind_1338_; lean_object* v_getEnv_1339_; lean_object* v_modifyEnv_1340_; lean_object* v___f_1341_; lean_object* v___f_1342_; lean_object* v___f_1343_; lean_object* v___f_1344_; lean_object* v___x_1345_; 
v_toBind_1338_ = lean_ctor_get(v_inst_1334_, 1);
lean_inc_n(v_toBind_1338_, 2);
v_getEnv_1339_ = lean_ctor_get(v_inst_1336_, 0);
lean_inc(v_getEnv_1339_);
v_modifyEnv_1340_ = lean_ctor_get(v_inst_1336_, 1);
lean_inc_n(v_modifyEnv_1340_, 2);
lean_dec_ref(v_inst_1336_);
lean_inc(v_declName_1337_);
v___f_1341_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1341_, 0, v_declName_1337_);
v___f_1342_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1342_, 0, v___f_1341_);
lean_inc_ref(v___f_1342_);
v___f_1343_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1343_, 0, v_modifyEnv_1340_);
lean_closure_set(v___f_1343_, 1, v___f_1342_);
v___f_1344_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1344_, 0, v_declName_1337_);
lean_closure_set(v___f_1344_, 1, v_modifyEnv_1340_);
lean_closure_set(v___f_1344_, 2, v___f_1342_);
lean_closure_set(v___f_1344_, 3, v_inst_1334_);
lean_closure_set(v___f_1344_, 4, v_inst_1335_);
lean_closure_set(v___f_1344_, 5, v_toBind_1338_);
lean_closure_set(v___f_1344_, 6, v___f_1343_);
v___x_1345_ = lean_apply_4(v_toBind_1338_, lean_box(0), lean_box(0), v_getEnv_1339_, v___f_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore(lean_object* v_m_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_inst_1350_, lean_object* v_declName_1351_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_removeDocStringCore___redArg(v_inst_1347_, v_inst_1348_, v_inst_1349_, v_declName_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___boxed(lean_object* v_m_1353_, lean_object* v_inst_1354_, lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_inst_1357_, lean_object* v_declName_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_removeDocStringCore(v_m_1353_, v_inst_1354_, v_inst_1355_, v_inst_1356_, v_inst_1357_, v_declName_1358_);
lean_dec(v_inst_1357_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___redArg(lean_object* v_inst_1360_, lean_object* v_inst_1361_, lean_object* v_inst_1362_, lean_object* v_declName_1363_, lean_object* v_docString_x3f_1364_){
_start:
{
if (lean_obj_tag(v_docString_x3f_1364_) == 0)
{
lean_object* v_toApplicative_1365_; lean_object* v_toPure_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v_toApplicative_1365_ = lean_ctor_get(v_inst_1360_, 0);
lean_inc_ref(v_toApplicative_1365_);
lean_dec(v_declName_1363_);
lean_dec_ref(v_inst_1362_);
lean_dec_ref(v_inst_1361_);
lean_dec_ref(v_inst_1360_);
v_toPure_1366_ = lean_ctor_get(v_toApplicative_1365_, 1);
lean_inc(v_toPure_1366_);
lean_dec_ref(v_toApplicative_1365_);
v___x_1367_ = lean_box(0);
v___x_1368_ = lean_apply_2(v_toPure_1366_, lean_box(0), v___x_1367_);
return v___x_1368_;
}
else
{
lean_object* v_val_1369_; lean_object* v___x_1370_; 
v_val_1369_ = lean_ctor_get(v_docString_x3f_1364_, 0);
lean_inc(v_val_1369_);
lean_dec_ref_known(v_docString_x3f_1364_, 1);
v___x_1370_ = l_Lean_addDocStringCore___redArg(v_inst_1360_, v_inst_1361_, v_inst_1362_, v_declName_1363_, v_val_1369_);
return v___x_1370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27(lean_object* v_m_1371_, lean_object* v_inst_1372_, lean_object* v_inst_1373_, lean_object* v_inst_1374_, lean_object* v_inst_1375_, lean_object* v_declName_1376_, lean_object* v_docString_x3f_1377_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_addDocStringCore_x27___redArg(v_inst_1372_, v_inst_1373_, v_inst_1374_, v_declName_1376_, v_docString_x3f_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___boxed(lean_object* v_m_1379_, lean_object* v_inst_1380_, lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v_inst_1383_, lean_object* v_declName_1384_, lean_object* v_docString_x3f_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_addDocStringCore_x27(v_m_1379_, v_inst_1380_, v_inst_1381_, v_inst_1382_, v_inst_1383_, v_declName_1384_, v_docString_x3f_1385_);
lean_dec(v_inst_1383_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f(lean_object* v_env_1387_, lean_object* v_declName_1388_, uint8_t v_includeBuiltin_1389_){
_start:
{
lean_object* v_md_1392_; lean_object* v_v_1397_; lean_object* v___x_1404_; lean_object* v_toEnvExtension_1405_; lean_object* v_asyncMode_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; lean_object* v___x_1409_; 
v___x_1404_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1405_ = lean_ctor_get(v___x_1404_, 0);
v_asyncMode_1406_ = lean_ctor_get(v_toEnvExtension_1405_, 2);
v___x_1407_ = lean_box(0);
v___x_1408_ = 1;
lean_inc(v_declName_1388_);
lean_inc_ref(v_env_1387_);
v___x_1409_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1407_, v___x_1404_, v_env_1387_, v_declName_1388_, v_asyncMode_1406_, v___x_1408_);
if (lean_obj_tag(v___x_1409_) == 1)
{
lean_object* v_val_1410_; 
lean_dec(v_declName_1388_);
v_val_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_val_1410_);
lean_dec_ref_known(v___x_1409_, 1);
v_declName_1388_ = v_val_1410_;
goto _start;
}
else
{
lean_object* v___x_1412_; lean_object* v_toEnvExtension_1413_; lean_object* v_asyncMode_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_dec(v___x_1409_);
v___x_1412_ = l_Lean_docStringExt;
v_toEnvExtension_1413_ = lean_ctor_get(v___x_1412_, 0);
v_asyncMode_1414_ = lean_ctor_get(v_toEnvExtension_1413_, 2);
v___x_1415_ = ((lean_object*)(l_Lean_throwIfHasDocString___redArg___closed__0));
lean_inc(v_declName_1388_);
lean_inc_ref(v_env_1387_);
v___x_1416_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1415_, v___x_1412_, v_env_1387_, v_declName_1388_, v_asyncMode_1414_, v___x_1408_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v___x_1417_; lean_object* v_toEnvExtension_1418_; lean_object* v_asyncMode_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1417_ = l_Lean_versoDocStringExt;
v_toEnvExtension_1418_ = lean_ctor_get(v___x_1417_, 0);
v_asyncMode_1419_ = lean_ctor_get(v_toEnvExtension_1418_, 2);
v___x_1420_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default));
lean_inc(v_declName_1388_);
v___x_1421_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1420_, v___x_1417_, v_env_1387_, v_declName_1388_, v_asyncMode_1419_, v___x_1408_);
if (lean_obj_tag(v___x_1421_) == 0)
{
if (v_includeBuiltin_1389_ == 0)
{
lean_dec(v_declName_1388_);
goto v___jp_1401_;
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1423_ = lean_st_ref_get(v___x_1422_);
v___x_1424_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1423_, v_declName_1388_);
lean_dec(v___x_1423_);
if (lean_obj_tag(v___x_1424_) == 1)
{
lean_object* v_val_1425_; 
lean_dec(v_declName_1388_);
v_val_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_val_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v_md_1392_ = v_val_1425_;
goto v___jp_1391_;
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
lean_dec(v___x_1424_);
v___x_1426_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1427_ = lean_st_ref_get(v___x_1426_);
v___x_1428_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1427_, v_declName_1388_);
lean_dec(v_declName_1388_);
lean_dec(v___x_1427_);
if (lean_obj_tag(v___x_1428_) == 1)
{
lean_object* v_val_1429_; 
v_val_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_val_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v_v_1397_ = v_val_1429_;
goto v___jp_1396_;
}
else
{
lean_dec(v___x_1428_);
goto v___jp_1401_;
}
}
}
}
else
{
lean_object* v_val_1430_; 
lean_dec(v_declName_1388_);
v_val_1430_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_val_1430_);
lean_dec_ref_known(v___x_1421_, 1);
v_v_1397_ = v_val_1430_;
goto v___jp_1396_;
}
}
else
{
lean_object* v_val_1431_; 
lean_dec(v_declName_1388_);
lean_dec_ref(v_env_1387_);
v_val_1431_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_val_1431_);
lean_dec_ref_known(v___x_1416_, 1);
v_md_1392_ = v_val_1431_;
goto v___jp_1391_;
}
}
v___jp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v_md_1392_);
v___x_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
return v___x_1395_;
}
v___jp_1396_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1398_, 0, v_v_1397_);
v___x_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
v___jp_1401_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_box(0);
v___x_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
return v___x_1403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f___boxed(lean_object* v_env_1432_, lean_object* v_declName_1433_, lean_object* v_includeBuiltin_1434_, lean_object* v_a_1435_){
_start:
{
uint8_t v_includeBuiltin_boxed_1436_; lean_object* v_res_1437_; 
v_includeBuiltin_boxed_1436_ = lean_unbox(v_includeBuiltin_1434_);
v_res_1437_ = l_Lean_findInternalDocString_x3f(v_env_1432_, v_declName_1433_, v_includeBuiltin_boxed_1436_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__0(lean_object* v_declName_1438_, lean_object* v_target_1439_, lean_object* v_x_1440_){
_start:
{
lean_object* v___x_1441_; uint8_t v___x_1442_; lean_object* v___x_1443_; 
v___x_1441_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v___x_1442_ = 0;
v___x_1443_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1441_, v_x_1440_, v_declName_1438_, v_target_1439_, v___x_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__1(lean_object* v_declName_1444_, lean_object* v_val_1445_, lean_object* v_x_1446_){
_start:
{
lean_object* v___x_1447_; uint8_t v___x_1448_; lean_object* v___x_1449_; 
v___x_1447_ = l_Lean_docStringExt;
v___x_1448_ = 0;
v___x_1449_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1447_, v_x_1446_, v_declName_1444_, v_val_1445_, v___x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__2(lean_object* v_declName_1450_, lean_object* v_val_1451_, lean_object* v_x_1452_){
_start:
{
lean_object* v___x_1453_; uint8_t v___x_1454_; lean_object* v___x_1455_; 
v___x_1453_ = l_Lean_versoDocStringExt;
v___x_1454_ = 0;
v___x_1455_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1453_, v_x_1452_, v_declName_1450_, v_val_1451_, v___x_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__3(lean_object* v_modifyEnv_1456_, lean_object* v___f_1457_, lean_object* v_declName_1458_, lean_object* v_____do__lift_1459_){
_start:
{
if (lean_obj_tag(v_____do__lift_1459_) == 0)
{
lean_object* v___x_1460_; 
lean_dec(v_declName_1458_);
v___x_1460_ = lean_apply_1(v_modifyEnv_1456_, v___f_1457_);
return v___x_1460_;
}
else
{
lean_object* v_val_1461_; 
lean_dec_ref(v___f_1457_);
v_val_1461_ = lean_ctor_get(v_____do__lift_1459_, 0);
lean_inc(v_val_1461_);
lean_dec_ref_known(v_____do__lift_1459_, 1);
if (lean_obj_tag(v_val_1461_) == 0)
{
lean_object* v_val_1462_; lean_object* v___f_1463_; lean_object* v___x_1464_; 
v_val_1462_ = lean_ctor_get(v_val_1461_, 0);
lean_inc(v_val_1462_);
lean_dec_ref_known(v_val_1461_, 1);
v___f_1463_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1463_, 0, v_declName_1458_);
lean_closure_set(v___f_1463_, 1, v_val_1462_);
v___x_1464_ = lean_apply_1(v_modifyEnv_1456_, v___f_1463_);
return v___x_1464_;
}
else
{
lean_object* v_val_1465_; lean_object* v___f_1466_; lean_object* v___x_1467_; 
v_val_1465_ = lean_ctor_get(v_val_1461_, 0);
lean_inc(v_val_1465_);
lean_dec_ref_known(v_val_1461_, 1);
v___f_1466_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1466_, 0, v_declName_1458_);
lean_closure_set(v___f_1466_, 1, v_val_1465_);
v___x_1467_ = lean_apply_1(v_modifyEnv_1456_, v___f_1466_);
return v___x_1467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__4(lean_object* v_declName_1468_, lean_object* v_target_1469_, uint8_t v___y_1470_, lean_object* v_x_1471_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v___x_1473_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1472_, v_x_1471_, v_declName_1468_, v_target_1469_, v___y_1470_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__4___boxed(lean_object* v_declName_1474_, lean_object* v_target_1475_, lean_object* v___y_1476_, lean_object* v_x_1477_){
_start:
{
uint8_t v___y_622__boxed_1478_; lean_object* v_res_1479_; 
v___y_622__boxed_1478_ = lean_unbox(v___y_1476_);
v_res_1479_ = l_Lean_addInheritedDocString___redArg___lam__4(v_declName_1474_, v_target_1475_, v___y_622__boxed_1478_, v_x_1477_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5(lean_object* v_target_1480_, uint8_t v___x_1481_, lean_object* v_inst_1482_, lean_object* v_toBind_1483_, lean_object* v___f_1484_, lean_object* v_____do__lift_1485_){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1486_ = lean_box(v___x_1481_);
v___x_1487_ = lean_alloc_closure((void*)(l_Lean_findInternalDocString_x3f___boxed), 4, 3);
lean_closure_set(v___x_1487_, 0, v_____do__lift_1485_);
lean_closure_set(v___x_1487_, 1, v_target_1480_);
lean_closure_set(v___x_1487_, 2, v___x_1486_);
v___x_1488_ = lean_apply_2(v_inst_1482_, lean_box(0), v___x_1487_);
v___x_1489_ = lean_apply_4(v_toBind_1483_, lean_box(0), lean_box(0), v___x_1488_, v___f_1484_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5___boxed(lean_object* v_target_1490_, lean_object* v___x_1491_, lean_object* v_inst_1492_, lean_object* v_toBind_1493_, lean_object* v___f_1494_, lean_object* v_____do__lift_1495_){
_start:
{
uint8_t v___x_632__boxed_1496_; lean_object* v_res_1497_; 
v___x_632__boxed_1496_ = lean_unbox(v___x_1491_);
v_res_1497_ = l_Lean_addInheritedDocString___redArg___lam__5(v_target_1490_, v___x_632__boxed_1496_, v_inst_1492_, v_toBind_1493_, v___f_1494_, v_____do__lift_1495_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__6(lean_object* v_declName_1498_, lean_object* v_target_1499_, lean_object* v_modifyEnv_1500_, lean_object* v_inst_1501_, lean_object* v_toBind_1502_, lean_object* v___f_1503_, lean_object* v_getEnv_1504_, lean_object* v_____r_1505_){
_start:
{
uint8_t v___y_1507_; uint8_t v___x_1511_; 
v___x_1511_ = l_Lean_isPrivateName(v_declName_1498_);
if (v___x_1511_ == 0)
{
uint8_t v___x_1512_; 
v___x_1512_ = l_Lean_isPrivateName(v_target_1499_);
if (v___x_1512_ == 0)
{
lean_dec(v_getEnv_1504_);
lean_dec(v___f_1503_);
lean_dec(v_toBind_1502_);
lean_dec(v_inst_1501_);
v___y_1507_ = v___x_1512_;
goto v___jp_1506_;
}
else
{
lean_object* v___x_1513_; lean_object* v___f_1514_; lean_object* v___x_1515_; 
lean_dec(v_modifyEnv_1500_);
lean_dec(v_declName_1498_);
v___x_1513_ = lean_box(v___x_1512_);
lean_inc(v_toBind_1502_);
v___f_1514_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_1514_, 0, v_target_1499_);
lean_closure_set(v___f_1514_, 1, v___x_1513_);
lean_closure_set(v___f_1514_, 2, v_inst_1501_);
lean_closure_set(v___f_1514_, 3, v_toBind_1502_);
lean_closure_set(v___f_1514_, 4, v___f_1503_);
v___x_1515_ = lean_apply_4(v_toBind_1502_, lean_box(0), lean_box(0), v_getEnv_1504_, v___f_1514_);
return v___x_1515_;
}
}
else
{
uint8_t v___x_1516_; 
lean_dec(v_getEnv_1504_);
lean_dec(v___f_1503_);
lean_dec(v_toBind_1502_);
lean_dec(v_inst_1501_);
v___x_1516_ = 0;
v___y_1507_ = v___x_1516_;
goto v___jp_1506_;
}
v___jp_1506_:
{
lean_object* v___x_1508_; lean_object* v___f_1509_; lean_object* v___x_1510_; 
v___x_1508_ = lean_box(v___y_1507_);
v___f_1509_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_1509_, 0, v_declName_1498_);
lean_closure_set(v___f_1509_, 1, v_target_1499_);
lean_closure_set(v___f_1509_, 2, v___x_1508_);
v___x_1510_ = lean_apply_1(v_modifyEnv_1500_, v___f_1509_);
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__7(lean_object* v___f_1517_, lean_object* v_____r_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_apply_1(v___f_1517_, v_____r_1518_);
return v___x_1519_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__8___closed__1(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__8___closed__0));
v___x_1522_ = l_Lean_stringToMessageData(v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__8(lean_object* v___x_1523_, lean_object* v_target_1524_, lean_object* v_declName_1525_, lean_object* v___x_1526_, lean_object* v___f_1527_, lean_object* v_inst_1528_, lean_object* v_inst_1529_, lean_object* v_toBind_1530_, lean_object* v___f_1531_, lean_object* v_____do__lift_1532_){
_start:
{
lean_object* v___x_1533_; lean_object* v_toEnvExtension_1534_; lean_object* v_asyncMode_1535_; uint8_t v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1533_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1534_ = lean_ctor_get(v___x_1533_, 0);
v_asyncMode_1535_ = lean_ctor_get(v_toEnvExtension_1534_, 2);
v___x_1536_ = 1;
v___x_1537_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1523_, v___x_1533_, v_____do__lift_1532_, v_target_1524_, v_asyncMode_1535_, v___x_1536_);
v___x_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1538_, 0, v_declName_1525_);
v___x_1539_ = l_instBEqOption_beq___redArg(v___x_1526_, v___x_1537_, v___x_1538_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_dec(v___f_1531_);
lean_dec(v_toBind_1530_);
lean_dec_ref(v_inst_1529_);
lean_dec_ref(v_inst_1528_);
v___x_1540_ = lean_box(0);
v___x_1541_ = lean_apply_1(v___f_1527_, v___x_1540_);
return v___x_1541_;
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec(v___f_1527_);
v___x_1542_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__8___closed__1, &l_Lean_addInheritedDocString___redArg___lam__8___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__8___closed__1);
v___x_1543_ = l_Lean_throwError___redArg(v_inst_1528_, v_inst_1529_, v___x_1542_);
v___x_1544_ = lean_apply_4(v_toBind_1530_, lean_box(0), lean_box(0), v___x_1543_, v___f_1531_);
return v___x_1544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__9(lean_object* v_toBind_1545_, lean_object* v_getEnv_1546_, lean_object* v___f_1547_, lean_object* v_____r_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_apply_4(v_toBind_1545_, lean_box(0), lean_box(0), v_getEnv_1546_, v___f_1547_);
return v___x_1549_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__10___closed__0));
v___x_1552_ = l_Lean_stringToMessageData(v___x_1551_);
return v___x_1552_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__10___closed__3(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__10___closed__2));
v___x_1555_ = l_Lean_stringToMessageData(v___x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__10(lean_object* v___x_1556_, lean_object* v_declName_1557_, lean_object* v_toBind_1558_, lean_object* v_getEnv_1559_, lean_object* v___f_1560_, lean_object* v_inst_1561_, lean_object* v_inst_1562_, lean_object* v___f_1563_, lean_object* v_____do__lift_1564_){
_start:
{
lean_object* v___x_1565_; lean_object* v_toEnvExtension_1566_; lean_object* v_asyncMode_1567_; uint8_t v___x_1568_; lean_object* v___x_1569_; 
v___x_1565_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1566_ = lean_ctor_get(v___x_1565_, 0);
v_asyncMode_1567_ = lean_ctor_get(v_toEnvExtension_1566_, 2);
v___x_1568_ = 1;
lean_inc(v_declName_1557_);
v___x_1569_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1556_, v___x_1565_, v_____do__lift_1564_, v_declName_1557_, v_asyncMode_1567_, v___x_1568_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v___x_1570_; 
lean_dec(v___f_1563_);
lean_dec_ref(v_inst_1562_);
lean_dec_ref(v_inst_1561_);
lean_dec(v_declName_1557_);
v___x_1570_ = lean_apply_4(v_toBind_1558_, lean_box(0), lean_box(0), v_getEnv_1559_, v___f_1560_);
return v___x_1570_;
}
else
{
lean_object* v___x_1571_; uint8_t v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_dec_ref_known(v___x_1569_, 1);
lean_dec(v___f_1560_);
lean_dec(v_getEnv_1559_);
v___x_1571_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__10___closed__1, &l_Lean_addInheritedDocString___redArg___lam__10___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__10___closed__1);
v___x_1572_ = 0;
v___x_1573_ = l_Lean_MessageData_ofConstName(v_declName_1557_, v___x_1572_);
v___x_1574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1571_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__10___closed__3, &l_Lean_addInheritedDocString___redArg___lam__10___closed__3_once, _init_l_Lean_addInheritedDocString___redArg___lam__10___closed__3);
v___x_1576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = l_Lean_throwError___redArg(v_inst_1561_, v_inst_1562_, v___x_1576_);
v___x_1578_ = lean_apply_4(v_toBind_1558_, lean_box(0), lean_box(0), v___x_1577_, v___f_1563_);
return v___x_1578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__12(lean_object* v_declName_1579_, lean_object* v_toBind_1580_, lean_object* v_getEnv_1581_, lean_object* v___f_1582_, lean_object* v_inst_1583_, lean_object* v_inst_1584_, lean_object* v___f_1585_, lean_object* v_____do__lift_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1586_, v_declName_1579_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v___x_1588_; 
lean_dec(v___f_1585_);
lean_dec_ref(v_inst_1584_);
lean_dec_ref(v_inst_1583_);
lean_dec(v_declName_1579_);
v___x_1588_ = lean_apply_4(v_toBind_1580_, lean_box(0), lean_box(0), v_getEnv_1581_, v___f_1582_);
return v___x_1588_;
}
else
{
uint8_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec_ref_known(v___x_1587_, 1);
lean_dec(v___f_1582_);
lean_dec(v_getEnv_1581_);
v___x_1589_ = 0;
v___x_1590_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__10___closed__1, &l_Lean_addInheritedDocString___redArg___lam__10___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__10___closed__1);
v___x_1591_ = l_Lean_MessageData_ofConstName(v_declName_1579_, v___x_1589_);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__1, &l_Lean_addDocStringCore___redArg___lam__2___closed__1_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = l_Lean_throwError___redArg(v_inst_1583_, v_inst_1584_, v___x_1594_);
v___x_1596_ = lean_apply_4(v_toBind_1580_, lean_box(0), lean_box(0), v___x_1595_, v___f_1585_);
return v___x_1596_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__12___boxed(lean_object* v_declName_1597_, lean_object* v_toBind_1598_, lean_object* v_getEnv_1599_, lean_object* v___f_1600_, lean_object* v_inst_1601_, lean_object* v_inst_1602_, lean_object* v___f_1603_, lean_object* v_____do__lift_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_addInheritedDocString___redArg___lam__12(v_declName_1597_, v_toBind_1598_, v_getEnv_1599_, v___f_1600_, v_inst_1601_, v_inst_1602_, v___f_1603_, v_____do__lift_1604_);
lean_dec_ref(v_____do__lift_1604_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg(lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_inst_1610_, lean_object* v_declName_1611_, lean_object* v_target_1612_){
_start:
{
lean_object* v_toBind_1613_; lean_object* v_getEnv_1614_; lean_object* v_modifyEnv_1615_; lean_object* v___f_1616_; lean_object* v___f_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___f_1620_; lean_object* v___f_1621_; lean_object* v___f_1622_; lean_object* v___f_1623_; lean_object* v___f_1624_; lean_object* v___f_1625_; lean_object* v___f_1626_; lean_object* v___x_1627_; 
v_toBind_1613_ = lean_ctor_get(v_inst_1607_, 1);
lean_inc_n(v_toBind_1613_, 7);
v_getEnv_1614_ = lean_ctor_get(v_inst_1609_, 0);
lean_inc_n(v_getEnv_1614_, 6);
v_modifyEnv_1615_ = lean_ctor_get(v_inst_1609_, 1);
lean_inc_n(v_modifyEnv_1615_, 2);
lean_dec_ref(v_inst_1609_);
lean_inc_n(v_target_1612_, 2);
lean_inc_n(v_declName_1611_, 5);
v___f_1616_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1616_, 0, v_declName_1611_);
lean_closure_set(v___f_1616_, 1, v_target_1612_);
v___f_1617_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1617_, 0, v_modifyEnv_1615_);
lean_closure_set(v___f_1617_, 1, v___f_1616_);
lean_closure_set(v___f_1617_, 2, v_declName_1611_);
v___x_1618_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___closed__0));
v___x_1619_ = lean_box(0);
v___f_1620_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__6), 8, 7);
lean_closure_set(v___f_1620_, 0, v_declName_1611_);
lean_closure_set(v___f_1620_, 1, v_target_1612_);
lean_closure_set(v___f_1620_, 2, v_modifyEnv_1615_);
lean_closure_set(v___f_1620_, 3, v_inst_1610_);
lean_closure_set(v___f_1620_, 4, v_toBind_1613_);
lean_closure_set(v___f_1620_, 5, v___f_1617_);
lean_closure_set(v___f_1620_, 6, v_getEnv_1614_);
lean_inc_ref(v___f_1620_);
v___f_1621_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__7), 2, 1);
lean_closure_set(v___f_1621_, 0, v___f_1620_);
lean_inc_ref_n(v_inst_1608_, 2);
lean_inc_ref_n(v_inst_1607_, 2);
v___f_1622_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__8), 10, 9);
lean_closure_set(v___f_1622_, 0, v___x_1619_);
lean_closure_set(v___f_1622_, 1, v_target_1612_);
lean_closure_set(v___f_1622_, 2, v_declName_1611_);
lean_closure_set(v___f_1622_, 3, v___x_1618_);
lean_closure_set(v___f_1622_, 4, v___f_1620_);
lean_closure_set(v___f_1622_, 5, v_inst_1607_);
lean_closure_set(v___f_1622_, 6, v_inst_1608_);
lean_closure_set(v___f_1622_, 7, v_toBind_1613_);
lean_closure_set(v___f_1622_, 8, v___f_1621_);
lean_inc_ref(v___f_1622_);
v___f_1623_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__9), 4, 3);
lean_closure_set(v___f_1623_, 0, v_toBind_1613_);
lean_closure_set(v___f_1623_, 1, v_getEnv_1614_);
lean_closure_set(v___f_1623_, 2, v___f_1622_);
v___f_1624_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__10), 9, 8);
lean_closure_set(v___f_1624_, 0, v___x_1619_);
lean_closure_set(v___f_1624_, 1, v_declName_1611_);
lean_closure_set(v___f_1624_, 2, v_toBind_1613_);
lean_closure_set(v___f_1624_, 3, v_getEnv_1614_);
lean_closure_set(v___f_1624_, 4, v___f_1622_);
lean_closure_set(v___f_1624_, 5, v_inst_1607_);
lean_closure_set(v___f_1624_, 6, v_inst_1608_);
lean_closure_set(v___f_1624_, 7, v___f_1623_);
lean_inc_ref(v___f_1624_);
v___f_1625_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__9), 4, 3);
lean_closure_set(v___f_1625_, 0, v_toBind_1613_);
lean_closure_set(v___f_1625_, 1, v_getEnv_1614_);
lean_closure_set(v___f_1625_, 2, v___f_1624_);
v___f_1626_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__12___boxed), 8, 7);
lean_closure_set(v___f_1626_, 0, v_declName_1611_);
lean_closure_set(v___f_1626_, 1, v_toBind_1613_);
lean_closure_set(v___f_1626_, 2, v_getEnv_1614_);
lean_closure_set(v___f_1626_, 3, v___f_1624_);
lean_closure_set(v___f_1626_, 4, v_inst_1607_);
lean_closure_set(v___f_1626_, 5, v_inst_1608_);
lean_closure_set(v___f_1626_, 6, v___f_1625_);
v___x_1627_ = lean_apply_4(v_toBind_1613_, lean_box(0), lean_box(0), v_getEnv_1614_, v___f_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString(lean_object* v_m_1628_, lean_object* v_inst_1629_, lean_object* v_inst_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_declName_1633_, lean_object* v_target_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_addInheritedDocString___redArg(v_inst_1629_, v_inst_1630_, v_inst_1631_, v_inst_1632_, v_declName_1633_, v_target_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v_es_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_array_mk(v_es_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v_x_1640_, lean_object* v_x_1641_, lean_object* v_es_1642_){
_start:
{
lean_object* v_ents_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v_ents_1643_ = lean_array_mk(v_es_1642_);
v___x_1644_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_));
lean_inc_ref(v_ents_1643_);
v___x_1645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_ctor_set(v___x_1645_, 1, v_ents_1643_);
lean_ctor_set(v___x_1645_, 2, v_ents_1643_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v_x_1646_, lean_object* v_x_1647_, lean_object* v_es_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(v_x_1646_, v_x_1647_, v_es_1648_);
lean_dec_ref(v_x_1647_);
lean_dec_ref(v_x_1646_);
return v_res_1649_;
}
}
static lean_object* _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1650_ = lean_unsigned_to_nat(32u);
v___x_1651_ = lean_mk_empty_array_with_capacity(v___x_1650_);
v___x_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v___x_1653_, lean_object* v_x_1654_){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; size_t v___x_1658_; lean_object* v___x_1659_; 
v___x_1655_ = lean_unsigned_to_nat(32u);
v___x_1656_ = lean_mk_empty_array_with_capacity(v___x_1655_);
v___x_1657_ = lean_obj_once(&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_, &l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_);
v___x_1658_ = ((size_t)5ULL);
lean_inc(v___x_1653_);
v___x_1659_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1659_, 0, v___x_1657_);
lean_ctor_set(v___x_1659_, 1, v___x_1656_);
lean_ctor_set(v___x_1659_, 2, v___x_1653_);
lean_ctor_set(v___x_1659_, 3, v___x_1653_);
lean_ctor_set_usize(v___x_1659_, 4, v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v___x_1660_, lean_object* v_x_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(v___x_1660_, v_x_1661_);
lean_dec_ref(v_x_1661_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_));
v___x_1685_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_();
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMainModuleDoc___lam__0(lean_object* v___x_1688_, lean_object* v_doc_1689_, lean_object* v_s_1690_){
_start:
{
lean_object* v_addEntryFn_1691_; lean_object* v_importedEntries_1692_; lean_object* v_state_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1701_; 
v_addEntryFn_1691_ = lean_ctor_get(v___x_1688_, 3);
lean_inc(v_addEntryFn_1691_);
lean_dec_ref(v___x_1688_);
v_importedEntries_1692_ = lean_ctor_get(v_s_1690_, 0);
v_state_1693_ = lean_ctor_get(v_s_1690_, 1);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_s_1690_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1695_ = v_s_1690_;
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_state_1693_);
lean_inc(v_importedEntries_1692_);
lean_dec(v_s_1690_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v_state_1697_; lean_object* v___x_1699_; 
v_state_1697_ = lean_apply_2(v_addEntryFn_1691_, v_state_1693_, v_doc_1689_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 1, v_state_1697_);
v___x_1699_ = v___x_1695_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_importedEntries_1692_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_state_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMainModuleDoc(lean_object* v_env_1702_, lean_object* v_doc_1703_){
_start:
{
lean_object* v___x_1704_; lean_object* v_toEnvExtension_1705_; lean_object* v_asyncMode_1706_; uint8_t v_logWrites_1707_; lean_object* v___f_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1704_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_1705_ = lean_ctor_get(v___x_1704_, 0);
v_asyncMode_1706_ = lean_ctor_get(v_toEnvExtension_1705_, 2);
v_logWrites_1707_ = lean_ctor_get_uint8(v_toEnvExtension_1705_, sizeof(void*)*6);
v___f_1708_ = lean_alloc_closure((void*)(l_Lean_addMainModuleDoc___lam__0), 3, 2);
lean_closure_set(v___f_1708_, 0, v___x_1704_);
lean_closure_set(v___f_1708_, 1, v_doc_1703_);
v___x_1709_ = lean_box(0);
v___x_1710_ = 1;
if (v_logWrites_1707_ == 0)
{
lean_object* v___x_1711_; 
lean_inc_ref(v_toEnvExtension_1705_);
v___x_1711_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1705_, v_env_1702_, v___f_1708_, v_asyncMode_1706_, v___x_1709_, v___x_1710_);
return v___x_1711_;
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_inc_ref_n(v_toEnvExtension_1705_, 2);
v___x_1712_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1705_, v_env_1702_);
lean_dec_ref(v_env_1702_);
v___x_1713_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1705_, v___x_1712_, v___f_1708_, v_asyncMode_1706_, v___x_1709_, v___x_1710_);
return v___x_1713_;
}
}
}
static lean_object* _init_l_Lean_getMainModuleDoc___closed__0(void){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModuleDoc(lean_object* v_env_1715_){
_start:
{
lean_object* v___x_1716_; lean_object* v_toEnvExtension_1717_; lean_object* v_asyncMode_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1716_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_1717_ = lean_ctor_get(v___x_1716_, 0);
v_asyncMode_1718_ = lean_ctor_get(v_toEnvExtension_1717_, 2);
v___x_1719_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_1720_ = lean_box(0);
v___x_1721_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1719_, v___x_1716_, v_env_1715_, v_asyncMode_1718_, v___x_1720_);
return v___x_1721_;
}
}
static lean_object* _init_l_Lean_getModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1722_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_1723_ = lean_box(0);
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
lean_ctor_set(v___x_1724_, 1, v___x_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f(lean_object* v_env_1725_, lean_object* v_moduleName_1726_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_Environment_getModuleIdx_x3f(v_env_1725_, v_moduleName_1726_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_box(0);
return v___x_1728_;
}
else
{
lean_object* v_val_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1740_; 
v_val_1729_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1731_ = v___x_1727_;
v_isShared_1732_ = v_isSharedCheck_1740_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_val_1729_);
lean_dec(v___x_1727_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1740_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; uint8_t v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1733_ = lean_obj_once(&l_Lean_getModuleDoc_x3f___closed__0, &l_Lean_getModuleDoc_x3f___closed__0_once, _init_l_Lean_getModuleDoc_x3f___closed__0);
v___x_1734_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v___x_1735_ = 1;
v___x_1736_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1733_, v___x_1734_, v_env_1725_, v_val_1729_, v___x_1735_);
lean_dec(v_val_1729_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1736_);
v___x_1738_ = v___x_1731_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f___boxed(lean_object* v_env_1741_, lean_object* v_moduleName_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_getModuleDoc_x3f(v_env_1741_, v_moduleName_1742_);
lean_dec(v_moduleName_1742_);
lean_dec_ref(v_env_1741_);
return v_res_1743_;
}
}
static lean_object* _init_l_Lean_getDocStringText___redArg___closed__1(void){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__0));
v___x_1746_ = l_Lean_stringToMessageData(v___x_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___redArg(lean_object* v_inst_1750_, lean_object* v_inst_1751_, lean_object* v_stx_1752_){
_start:
{
lean_object* v_toApplicative_1759_; lean_object* v_toPure_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v_toApplicative_1759_ = lean_ctor_get(v_inst_1750_, 0);
v_toPure_1760_ = lean_ctor_get(v_toApplicative_1759_, 1);
v___x_1761_ = lean_unsigned_to_nat(1u);
v___x_1762_ = l_Lean_Syntax_getArg(v_stx_1752_, v___x_1761_);
if (lean_obj_tag(v___x_1762_) == 1)
{
lean_object* v_kind_1763_; 
v_kind_1763_ = lean_ctor_get(v___x_1762_, 1);
lean_inc(v_kind_1763_);
if (lean_obj_tag(v_kind_1763_) == 1)
{
lean_object* v_pre_1764_; 
v_pre_1764_ = lean_ctor_get(v_kind_1763_, 0);
lean_inc(v_pre_1764_);
if (lean_obj_tag(v_pre_1764_) == 1)
{
lean_object* v_pre_1765_; 
v_pre_1765_ = lean_ctor_get(v_pre_1764_, 0);
lean_inc(v_pre_1765_);
if (lean_obj_tag(v_pre_1765_) == 1)
{
lean_object* v_pre_1766_; 
v_pre_1766_ = lean_ctor_get(v_pre_1765_, 0);
lean_inc(v_pre_1766_);
if (lean_obj_tag(v_pre_1766_) == 1)
{
lean_object* v_pre_1767_; 
v_pre_1767_ = lean_ctor_get(v_pre_1766_, 0);
if (lean_obj_tag(v_pre_1767_) == 0)
{
lean_object* v_args_1768_; lean_object* v_str_1769_; lean_object* v_str_1770_; lean_object* v_str_1771_; lean_object* v_str_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v_args_1768_ = lean_ctor_get(v___x_1762_, 2);
lean_inc_ref(v_args_1768_);
lean_dec_ref_known(v___x_1762_, 3);
v_str_1769_ = lean_ctor_get(v_kind_1763_, 1);
lean_inc_ref(v_str_1769_);
lean_dec_ref_known(v_kind_1763_, 2);
v_str_1770_ = lean_ctor_get(v_pre_1764_, 1);
lean_inc_ref(v_str_1770_);
lean_dec_ref_known(v_pre_1764_, 2);
v_str_1771_ = lean_ctor_get(v_pre_1765_, 1);
lean_inc_ref(v_str_1771_);
lean_dec_ref_known(v_pre_1765_, 2);
v_str_1772_ = lean_ctor_get(v_pre_1766_, 1);
lean_inc_ref(v_str_1772_);
lean_dec_ref_known(v_pre_1766_, 2);
v___x_1773_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_1774_ = lean_string_dec_eq(v_str_1772_, v___x_1773_);
lean_dec_ref(v_str_1772_);
if (v___x_1774_ == 0)
{
lean_dec_ref(v_str_1771_);
lean_dec_ref(v_str_1770_);
lean_dec_ref(v_str_1769_);
lean_dec_ref(v_args_1768_);
goto v___jp_1753_;
}
else
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__2));
v___x_1776_ = lean_string_dec_eq(v_str_1771_, v___x_1775_);
lean_dec_ref(v_str_1771_);
if (v___x_1776_ == 0)
{
lean_dec_ref(v_str_1770_);
lean_dec_ref(v_str_1769_);
lean_dec_ref(v_args_1768_);
goto v___jp_1753_;
}
else
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__3));
v___x_1778_ = lean_string_dec_eq(v_str_1770_, v___x_1777_);
lean_dec_ref(v_str_1770_);
if (v___x_1778_ == 0)
{
lean_dec_ref(v_str_1769_);
lean_dec_ref(v_args_1768_);
goto v___jp_1753_;
}
else
{
lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1779_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__4));
v___x_1780_ = lean_string_dec_eq(v_str_1769_, v___x_1779_);
lean_dec_ref(v_str_1769_);
if (v___x_1780_ == 0)
{
lean_dec_ref(v_args_1768_);
goto v___jp_1753_;
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; 
v___x_1781_ = lean_array_get_size(v_args_1768_);
v___x_1782_ = lean_unsigned_to_nat(2u);
v___x_1783_ = lean_nat_dec_eq(v___x_1781_, v___x_1782_);
if (v___x_1783_ == 0)
{
lean_dec_ref(v_args_1768_);
goto v___jp_1753_;
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = lean_unsigned_to_nat(0u);
v___x_1785_ = lean_array_fget(v_args_1768_, v___x_1784_);
lean_dec_ref(v_args_1768_);
if (lean_obj_tag(v___x_1785_) == 2)
{
lean_object* v_val_1786_; lean_object* v___x_1787_; 
lean_inc(v_toPure_1760_);
lean_dec(v_stx_1752_);
lean_dec_ref(v_inst_1751_);
lean_dec_ref(v_inst_1750_);
v_val_1786_ = lean_ctor_get(v___x_1785_, 1);
lean_inc_ref(v_val_1786_);
lean_dec_ref_known(v___x_1785_, 2);
v___x_1787_ = lean_apply_2(v_toPure_1760_, lean_box(0), v_val_1786_);
return v___x_1787_;
}
else
{
lean_dec(v___x_1785_);
goto v___jp_1753_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1766_, 2);
lean_dec_ref_known(v_pre_1765_, 2);
lean_dec_ref_known(v_pre_1764_, 2);
lean_dec_ref_known(v_kind_1763_, 2);
lean_dec_ref_known(v___x_1762_, 3);
goto v___jp_1753_;
}
}
else
{
lean_dec(v_pre_1766_);
lean_dec_ref_known(v_pre_1765_, 2);
lean_dec_ref_known(v_pre_1764_, 2);
lean_dec_ref_known(v_kind_1763_, 2);
lean_dec_ref_known(v___x_1762_, 3);
goto v___jp_1753_;
}
}
else
{
lean_dec(v_pre_1765_);
lean_dec_ref_known(v_pre_1764_, 2);
lean_dec_ref_known(v_kind_1763_, 2);
lean_dec_ref_known(v___x_1762_, 3);
goto v___jp_1753_;
}
}
else
{
lean_dec(v_pre_1764_);
lean_dec_ref_known(v_kind_1763_, 2);
lean_dec_ref_known(v___x_1762_, 3);
goto v___jp_1753_;
}
}
else
{
lean_dec_ref_known(v___x_1762_, 3);
lean_dec(v_kind_1763_);
goto v___jp_1753_;
}
}
else
{
lean_dec(v___x_1762_);
goto v___jp_1753_;
}
v___jp_1753_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1754_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_1752_);
v___x_1755_ = l_Lean_MessageData_ofSyntax(v_stx_1752_);
v___x_1756_ = l_Lean_indentD(v___x_1755_);
v___x_1757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1754_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = l_Lean_throwErrorAt___redArg(v_inst_1750_, v_inst_1751_, v_stx_1752_, v___x_1757_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText(lean_object* v_m_1788_, lean_object* v_inst_1789_, lean_object* v_inst_1790_, lean_object* v_stx_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_getDocStringText___redArg(v_inst_1789_, v_inst_1790_, v_stx_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT uint8_t l_Lean_isVersoDocComment(lean_object* v_stx_1799_){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1800_ = lean_unsigned_to_nat(1u);
v___x_1801_ = l_Lean_Syntax_getArg(v_stx_1799_, v___x_1800_);
v___x_1802_ = ((lean_object*)(l_Lean_isVersoDocComment___closed__1));
v___x_1803_ = l_Lean_Syntax_isOfKind(v___x_1801_, v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_isVersoDocComment___boxed(lean_object* v_stx_1804_){
_start:
{
uint8_t v_res_1805_; lean_object* v_r_1806_; 
v_res_1805_ = l_Lean_isVersoDocComment(v_stx_1804_);
lean_dec(v_stx_1804_);
v_r_1806_ = lean_box(v_res_1805_);
return v_r_1806_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = l_Lean_instInhabitedDeclarationRange_default;
v___x_1810_ = ((lean_object*)(l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0));
v___x_1811_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
lean_ctor_set(v___x_1811_, 2, v___x_1809_);
return v___x_1811_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default(void){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = lean_obj_once(&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1, &l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1_once, _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1);
return v___x_1812_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet(void){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Lean_VersoModuleDocs_instInhabitedSnippet_default;
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__2(lean_object* v_a_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = lean_nat_to_int(v_a_1814_);
return v___x_1815_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = lean_unsigned_to_nat(2u);
v___x_1823_ = lean_nat_to_int(v___x_1822_);
return v___x_1823_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = lean_unsigned_to_nat(1u);
v___x_1825_ = lean_nat_to_int(v___x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(lean_object* v_x_1838_, lean_object* v_x_1839_, lean_object* v_x_1840_){
_start:
{
if (lean_obj_tag(v_x_1840_) == 0)
{
lean_dec(v_x_1838_);
return v_x_1839_;
}
else
{
lean_object* v_head_1841_; lean_object* v_tail_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1853_; 
v_head_1841_ = lean_ctor_get(v_x_1840_, 0);
v_tail_1842_ = lean_ctor_get(v_x_1840_, 1);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_x_1840_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1844_ = v_x_1840_;
v_isShared_1845_ = v_isSharedCheck_1853_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_tail_1842_);
lean_inc(v_head_1841_);
lean_dec(v_x_1840_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1853_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
lean_inc(v_x_1838_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set_tag(v___x_1844_, 5);
lean_ctor_set(v___x_1844_, 1, v_x_1838_);
lean_ctor_set(v___x_1844_, 0, v_x_1839_);
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_x_1839_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_x_1838_);
v___x_1847_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = lean_unsigned_to_nat(0u);
v___x_1849_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_1841_, v___x_1848_);
v___x_1850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1847_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v_x_1839_ = v___x_1850_;
v_x_1840_ = v_tail_1842_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(lean_object* v_x_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_){
_start:
{
if (lean_obj_tag(v_x_1856_) == 0)
{
lean_dec(v_x_1854_);
return v_x_1855_;
}
else
{
lean_object* v_head_1857_; lean_object* v_tail_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1869_; 
v_head_1857_ = lean_ctor_get(v_x_1856_, 0);
v_tail_1858_ = lean_ctor_get(v_x_1856_, 1);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_x_1856_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1860_ = v_x_1856_;
v_isShared_1861_ = v_isSharedCheck_1869_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_tail_1858_);
lean_inc(v_head_1857_);
lean_dec(v_x_1856_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1869_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
lean_inc(v_x_1854_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set_tag(v___x_1860_, 5);
lean_ctor_set(v___x_1860_, 1, v_x_1854_);
lean_ctor_set(v___x_1860_, 0, v_x_1855_);
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_x_1855_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_x_1854_);
v___x_1863_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1864_ = lean_unsigned_to_nat(0u);
v___x_1865_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_1857_, v___x_1864_);
v___x_1866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1863_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(v_x_1854_, v___x_1866_, v_tail_1858_);
return v___x_1867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_1870_, lean_object* v_x_1871_){
_start:
{
if (lean_obj_tag(v_x_1870_) == 0)
{
lean_object* v___x_1872_; 
lean_dec(v_x_1871_);
v___x_1872_ = lean_box(0);
return v___x_1872_;
}
else
{
lean_object* v_tail_1873_; 
v_tail_1873_ = lean_ctor_get(v_x_1870_, 1);
if (lean_obj_tag(v_tail_1873_) == 0)
{
lean_object* v_head_1874_; lean_object* v___x_1875_; 
lean_dec(v_x_1871_);
v_head_1874_ = lean_ctor_get(v_x_1870_, 0);
lean_inc(v_head_1874_);
lean_dec_ref_known(v_x_1870_, 2);
v___x_1875_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_1874_);
return v___x_1875_;
}
else
{
lean_object* v_head_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_inc(v_tail_1873_);
v_head_1876_ = lean_ctor_get(v_x_1870_, 0);
lean_inc(v_head_1876_);
lean_dec_ref_known(v_x_1870_, 2);
v___x_1877_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_1876_);
v___x_1878_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(v_x_1871_, v___x_1877_, v_tail_1873_);
return v___x_1878_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0));
v___x_1881_ = lean_string_length(v___x_1880_);
return v___x_1881_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_1883_ = lean_nat_to_int(v___x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_xs_1892_){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1893_ = lean_array_get_size(v_xs_1892_);
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = lean_nat_dec_eq(v___x_1893_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1896_ = lean_array_to_list(v_xs_1892_);
v___x_1897_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_1898_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_1896_, v___x_1897_);
v___x_1899_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_1900_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_1901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v___x_1898_);
v___x_1902_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_1903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1899_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = l_Std_Format_fill(v___x_1904_);
return v___x_1905_;
}
else
{
lean_object* v___x_1906_; 
lean_dec_ref(v_xs_1892_);
v___x_1906_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_1906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_1961_, lean_object* v_prec_1962_){
_start:
{
switch(lean_obj_tag(v_x_1961_))
{
case 0:
{
lean_object* v_string_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1983_; 
v_string_1963_ = lean_ctor_get(v_x_1961_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_x_1961_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1965_ = v_x_1961_;
v_isShared_1966_ = v_isSharedCheck_1983_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_string_1963_);
lean_dec(v_x_1961_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1983_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___y_1968_; lean_object* v___x_1979_; uint8_t v___x_1980_; 
v___x_1979_ = lean_unsigned_to_nat(1024u);
v___x_1980_ = lean_nat_dec_le(v___x_1979_, v_prec_1962_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_1968_ = v___x_1981_;
goto v___jp_1967_;
}
else
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_1968_ = v___x_1982_;
goto v___jp_1967_;
}
v___jp_1967_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1969_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__2));
v___x_1970_ = l_String_quote(v_string_1963_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set_tag(v___x_1965_, 3);
lean_ctor_set(v___x_1965_, 0, v___x_1970_);
v___x_1972_ = v___x_1965_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1969_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
lean_inc(v___y_1968_);
v___x_1974_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___y_1968_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = 0;
v___x_1976_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1976_, 0, v___x_1974_);
lean_ctor_set_uint8(v___x_1976_, sizeof(void*)*1, v___x_1975_);
v___x_1977_ = l_Repr_addAppParen(v___x_1976_, v_prec_1962_);
return v___x_1977_;
}
}
}
}
case 1:
{
lean_object* v_content_1984_; lean_object* v___y_1986_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v_content_1984_ = lean_ctor_get(v_x_1961_, 0);
lean_inc_ref(v_content_1984_);
lean_dec_ref_known(v_x_1961_, 1);
v___x_1994_ = lean_unsigned_to_nat(1024u);
v___x_1995_ = lean_nat_dec_le(v___x_1994_, v_prec_1962_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; 
v___x_1996_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_1986_ = v___x_1996_;
goto v___jp_1985_;
}
else
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_1986_ = v___x_1997_;
goto v___jp_1985_;
}
v___jp_1985_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1987_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__7));
v___x_1988_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_1984_);
v___x_1989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
lean_inc(v___y_1986_);
v___x_1990_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___y_1986_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = 0;
v___x_1992_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set_uint8(v___x_1992_, sizeof(void*)*1, v___x_1991_);
v___x_1993_ = l_Repr_addAppParen(v___x_1992_, v_prec_1962_);
return v___x_1993_;
}
}
case 2:
{
lean_object* v_content_1998_; lean_object* v___y_2000_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v_content_1998_ = lean_ctor_get(v_x_1961_, 0);
lean_inc_ref(v_content_1998_);
lean_dec_ref_known(v_x_1961_, 1);
v___x_2008_ = lean_unsigned_to_nat(1024u);
v___x_2009_ = lean_nat_dec_le(v___x_2008_, v_prec_1962_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2000_ = v___x_2010_;
goto v___jp_1999_;
}
else
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2000_ = v___x_2011_;
goto v___jp_1999_;
}
v___jp_1999_:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2001_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__10));
v___x_2002_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_1998_);
v___x_2003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2001_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
lean_inc(v___y_2000_);
v___x_2004_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___y_2000_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___x_2005_ = 0;
v___x_2006_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2006_, 0, v___x_2004_);
lean_ctor_set_uint8(v___x_2006_, sizeof(void*)*1, v___x_2005_);
v___x_2007_ = l_Repr_addAppParen(v___x_2006_, v_prec_1962_);
return v___x_2007_;
}
}
case 3:
{
lean_object* v_string_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2032_; 
v_string_2012_ = lean_ctor_get(v_x_1961_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_x_1961_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2014_ = v_x_1961_;
v_isShared_2015_ = v_isSharedCheck_2032_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_string_2012_);
lean_dec(v_x_1961_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2032_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___y_2017_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = lean_unsigned_to_nat(1024u);
v___x_2029_ = lean_nat_dec_le(v___x_2028_, v_prec_1962_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; 
v___x_2030_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2017_ = v___x_2030_;
goto v___jp_2016_;
}
else
{
lean_object* v___x_2031_; 
v___x_2031_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2017_ = v___x_2031_;
goto v___jp_2016_;
}
v___jp_2016_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2018_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__13));
v___x_2019_ = l_String_quote(v_string_2012_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2019_);
v___x_2021_ = v___x_2014_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2018_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
lean_inc(v___y_2017_);
v___x_2023_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___y_2017_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = 0;
v___x_2025_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2025_, 0, v___x_2023_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*1, v___x_2024_);
v___x_2026_ = l_Repr_addAppParen(v___x_2025_, v_prec_1962_);
return v___x_2026_;
}
}
}
}
case 4:
{
uint8_t v_mode_2033_; lean_object* v_string_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2059_; 
v_mode_2033_ = lean_ctor_get_uint8(v_x_1961_, sizeof(void*)*1);
v_string_2034_ = lean_ctor_get(v_x_1961_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_x_1961_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2036_ = v_x_1961_;
v_isShared_2037_ = v_isSharedCheck_2059_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_string_2034_);
lean_dec(v_x_1961_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2059_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___y_2039_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
v___x_2055_ = lean_unsigned_to_nat(1024u);
v___x_2056_ = lean_nat_dec_le(v___x_2055_, v_prec_1962_);
if (v___x_2056_ == 0)
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2039_ = v___x_2057_;
goto v___jp_2038_;
}
else
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2039_ = v___x_2058_;
goto v___jp_2038_;
}
v___jp_2038_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; lean_object* v___x_2052_; 
v___x_2040_ = lean_box(1);
v___x_2041_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__16));
v___x_2042_ = lean_unsigned_to_nat(1024u);
v___x_2043_ = l_Lean_Doc_instReprMathMode_repr(v_mode_2033_, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2041_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
lean_ctor_set(v___x_2045_, 1, v___x_2040_);
v___x_2046_ = l_String_quote(v_string_2034_);
v___x_2047_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
v___x_2048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2045_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
lean_inc(v___y_2039_);
v___x_2049_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___y_2039_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
v___x_2050_ = 0;
if (v_isShared_2037_ == 0)
{
lean_ctor_set_tag(v___x_2036_, 6);
lean_ctor_set(v___x_2036_, 0, v___x_2049_);
v___x_2052_ = v___x_2036_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2049_);
v___x_2052_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2053_; 
lean_ctor_set_uint8(v___x_2052_, sizeof(void*)*1, v___x_2050_);
v___x_2053_ = l_Repr_addAppParen(v___x_2052_, v_prec_1962_);
return v___x_2053_;
}
}
}
}
case 5:
{
lean_object* v_string_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2080_; 
v_string_2060_ = lean_ctor_get(v_x_1961_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_x_1961_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2062_ = v_x_1961_;
v_isShared_2063_ = v_isSharedCheck_2080_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_string_2060_);
lean_dec(v_x_1961_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2080_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___y_2065_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = lean_unsigned_to_nat(1024u);
v___x_2077_ = lean_nat_dec_le(v___x_2076_, v_prec_1962_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2065_ = v___x_2078_;
goto v___jp_2064_;
}
else
{
lean_object* v___x_2079_; 
v___x_2079_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2065_ = v___x_2079_;
goto v___jp_2064_;
}
v___jp_2064_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2066_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__19));
v___x_2067_ = l_String_quote(v_string_2060_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set_tag(v___x_2062_, 3);
lean_ctor_set(v___x_2062_, 0, v___x_2067_);
v___x_2069_ = v___x_2062_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2066_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
lean_inc(v___y_2065_);
v___x_2071_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___y_2065_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = 0;
v___x_2073_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2073_, 0, v___x_2071_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*1, v___x_2072_);
v___x_2074_ = l_Repr_addAppParen(v___x_2073_, v_prec_1962_);
return v___x_2074_;
}
}
}
}
case 6:
{
lean_object* v_content_2081_; lean_object* v_url_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2106_; 
v_content_2081_ = lean_ctor_get(v_x_1961_, 0);
v_url_2082_ = lean_ctor_get(v_x_1961_, 1);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_x_1961_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2084_ = v_x_1961_;
v_isShared_2085_ = v_isSharedCheck_2106_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_url_2082_);
lean_inc(v_content_2081_);
lean_dec(v_x_1961_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2106_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___y_2087_; lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = lean_unsigned_to_nat(1024u);
v___x_2103_ = lean_nat_dec_le(v___x_2102_, v_prec_1962_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; 
v___x_2104_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2087_ = v___x_2104_;
goto v___jp_2086_;
}
else
{
lean_object* v___x_2105_; 
v___x_2105_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2087_ = v___x_2105_;
goto v___jp_2086_;
}
v___jp_2086_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2088_ = lean_box(1);
v___x_2089_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__22));
v___x_2090_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2081_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 5);
lean_ctor_set(v___x_2084_, 1, v___x_2090_);
lean_ctor_set(v___x_2084_, 0, v___x_2089_);
v___x_2092_ = v___x_2084_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
lean_ctor_set(v___x_2093_, 1, v___x_2088_);
v___x_2094_ = l_String_quote(v_url_2082_);
v___x_2095_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
v___x_2096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2093_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
lean_inc(v___y_2087_);
v___x_2097_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___y_2087_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = 0;
v___x_2099_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2099_, 0, v___x_2097_);
lean_ctor_set_uint8(v___x_2099_, sizeof(void*)*1, v___x_2098_);
v___x_2100_ = l_Repr_addAppParen(v___x_2099_, v_prec_1962_);
return v___x_2100_;
}
}
}
}
case 7:
{
lean_object* v_name_2107_; lean_object* v_content_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2132_; 
v_name_2107_ = lean_ctor_get(v_x_1961_, 0);
v_content_2108_ = lean_ctor_get(v_x_1961_, 1);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_x_1961_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2110_ = v_x_1961_;
v_isShared_2111_ = v_isSharedCheck_2132_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_content_2108_);
lean_inc(v_name_2107_);
lean_dec(v_x_1961_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2132_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___y_2113_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2128_ = lean_unsigned_to_nat(1024u);
v___x_2129_ = lean_nat_dec_le(v___x_2128_, v_prec_1962_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; 
v___x_2130_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2113_ = v___x_2130_;
goto v___jp_2112_;
}
else
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2113_ = v___x_2131_;
goto v___jp_2112_;
}
v___jp_2112_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2114_ = lean_box(1);
v___x_2115_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__25));
v___x_2116_ = l_String_quote(v_name_2107_);
v___x_2117_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set_tag(v___x_2110_, 5);
lean_ctor_set(v___x_2110_, 1, v___x_2117_);
lean_ctor_set(v___x_2110_, 0, v___x_2115_);
v___x_2119_ = v___x_2110_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
lean_ctor_set(v___x_2120_, 1, v___x_2114_);
v___x_2121_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2108_);
v___x_2122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2120_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
lean_inc(v___y_2113_);
v___x_2123_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___y_2113_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = 0;
v___x_2125_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2125_, 0, v___x_2123_);
lean_ctor_set_uint8(v___x_2125_, sizeof(void*)*1, v___x_2124_);
v___x_2126_ = l_Repr_addAppParen(v___x_2125_, v_prec_1962_);
return v___x_2126_;
}
}
}
}
case 8:
{
lean_object* v_alt_2133_; lean_object* v_url_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2159_; 
v_alt_2133_ = lean_ctor_get(v_x_1961_, 0);
v_url_2134_ = lean_ctor_get(v_x_1961_, 1);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_x_1961_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2136_ = v_x_1961_;
v_isShared_2137_ = v_isSharedCheck_2159_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_url_2134_);
lean_inc(v_alt_2133_);
lean_dec(v_x_1961_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2159_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___y_2139_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2155_ = lean_unsigned_to_nat(1024u);
v___x_2156_ = lean_nat_dec_le(v___x_2155_, v_prec_1962_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; 
v___x_2157_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2139_ = v___x_2157_;
goto v___jp_2138_;
}
else
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2139_ = v___x_2158_;
goto v___jp_2138_;
}
v___jp_2138_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2140_ = lean_box(1);
v___x_2141_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__28));
v___x_2142_ = l_String_quote(v_alt_2133_);
v___x_2143_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set_tag(v___x_2136_, 5);
lean_ctor_set(v___x_2136_, 1, v___x_2143_);
lean_ctor_set(v___x_2136_, 0, v___x_2141_);
v___x_2145_ = v___x_2136_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
lean_ctor_set(v___x_2146_, 1, v___x_2140_);
v___x_2147_ = l_String_quote(v_url_2134_);
v___x_2148_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
v___x_2149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2146_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
lean_inc(v___y_2139_);
v___x_2150_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___y_2139_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = 0;
v___x_2152_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set_uint8(v___x_2152_, sizeof(void*)*1, v___x_2151_);
v___x_2153_ = l_Repr_addAppParen(v___x_2152_, v_prec_1962_);
return v___x_2153_;
}
}
}
}
case 9:
{
lean_object* v_content_2160_; lean_object* v___y_2162_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_content_2160_ = lean_ctor_get(v_x_1961_, 0);
lean_inc_ref(v_content_2160_);
lean_dec_ref_known(v_x_1961_, 1);
v___x_2170_ = lean_unsigned_to_nat(1024u);
v___x_2171_ = lean_nat_dec_le(v___x_2170_, v_prec_1962_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; 
v___x_2172_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2162_ = v___x_2172_;
goto v___jp_2161_;
}
else
{
lean_object* v___x_2173_; 
v___x_2173_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2162_ = v___x_2173_;
goto v___jp_2161_;
}
v___jp_2161_:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2163_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__31));
v___x_2164_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2160_);
v___x_2165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2163_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
lean_inc(v___y_2162_);
v___x_2166_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___y_2162_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = 0;
v___x_2168_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*1, v___x_2167_);
v___x_2169_ = l_Repr_addAppParen(v___x_2168_, v_prec_1962_);
return v___x_2169_;
}
}
default: 
{
lean_object* v_container_2174_; lean_object* v_content_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2225_; 
v_container_2174_ = lean_ctor_get(v_x_1961_, 0);
v_content_2175_ = lean_ctor_get(v_x_1961_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_x_1961_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2177_ = v_x_1961_;
v_isShared_2178_ = v_isSharedCheck_2225_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_content_2175_);
lean_inc(v_container_2174_);
lean_dec(v_x_1961_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2225_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2195_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v___x_2221_ = lean_unsigned_to_nat(1024u);
v___x_2222_ = lean_nat_dec_le(v___x_2221_, v_prec_1962_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2195_ = v___x_2223_;
goto v___jp_2194_;
}
else
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2195_ = v___x_2224_;
goto v___jp_2194_;
}
v___jp_2179_:
{
lean_object* v___x_2185_; 
lean_inc(v___y_2181_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set_tag(v___x_2177_, 5);
lean_ctor_set(v___x_2177_, 1, v___y_2183_);
lean_ctor_set(v___x_2177_, 0, v___y_2181_);
v___x_2185_ = v___x_2177_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___y_2181_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v___y_2183_);
v___x_2185_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_inc(v___y_2182_);
v___x_2186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
lean_ctor_set(v___x_2186_, 1, v___y_2182_);
v___x_2187_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2175_);
v___x_2188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2186_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
lean_inc(v___y_2180_);
v___x_2189_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___y_2180_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = 0;
v___x_2191_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set_uint8(v___x_2191_, sizeof(void*)*1, v___x_2190_);
v___x_2192_ = l_Repr_addAppParen(v___x_2191_, v_prec_1962_);
return v___x_2192_;
}
}
v___jp_2194_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = lean_box(1);
v___x_2197_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__34));
if (lean_obj_tag(v_container_2174_) == 0)
{
lean_object* v_val_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; 
v_val_2198_ = lean_ctor_get(v_container_2174_, 0);
lean_inc(v_val_2198_);
lean_dec_ref_known(v_container_2174_, 1);
v___x_2199_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__5));
v___x_2200_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_2198_);
lean_dec(v_val_2198_);
v___x_2201_ = lean_unsigned_to_nat(0u);
v___x_2202_ = l_Lean_Name_reprPrec(v___x_2200_, v___x_2201_);
v___x_2203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2199_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__7));
v___x_2205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2203_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = 0;
v___x_2207_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set_uint8(v___x_2207_, sizeof(void*)*1, v___x_2206_);
v___y_2180_ = v___y_2195_;
v___y_2181_ = v___x_2197_;
v___y_2182_ = v___x_2196_;
v___y_2183_ = v___x_2207_;
goto v___jp_2179_;
}
else
{
lean_object* v_index_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2220_; 
v_index_2208_ = lean_ctor_get(v_container_2174_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_container_2174_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2210_ = v_container_2174_;
v_isShared_2211_ = v_isSharedCheck_2220_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_index_2208_);
lean_dec(v_container_2174_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2220_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2212_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_2213_ = l_Nat_reprFast(v_index_2208_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set_tag(v___x_2210_, 3);
lean_ctor_set(v___x_2210_, 0, v___x_2213_);
v___x_2215_ = v___x_2210_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
lean_object* v___x_2216_; uint8_t v___x_2217_; lean_object* v___x_2218_; 
v___x_2216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2212_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = 0;
v___x_2218_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2218_, 0, v___x_2216_);
lean_ctor_set_uint8(v___x_2218_, sizeof(void*)*1, v___x_2217_);
v___y_2180_ = v___y_2195_;
v___y_2181_ = v___x_2197_;
v___y_2182_ = v___x_2196_;
v___y_2183_ = v___x_2218_;
goto v___jp_2179_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object* v___y_2226_){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = lean_unsigned_to_nat(0u);
v___x_2228_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v___y_2226_, v___x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_2229_, lean_object* v_prec_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_x_2229_, v_prec_2230_);
lean_dec(v_prec_2230_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(lean_object* v_xs_2232_){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; 
v___x_2233_ = lean_array_get_size(v_xs_2232_);
v___x_2234_ = lean_unsigned_to_nat(0u);
v___x_2235_ = lean_nat_dec_eq(v___x_2233_, v___x_2234_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2236_ = lean_array_to_list(v_xs_2232_);
v___x_2237_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2238_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_2236_, v___x_2237_);
v___x_2239_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2240_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
lean_ctor_set(v___x_2241_, 1, v___x_2238_);
v___x_2242_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2241_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2239_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = l_Std_Format_fill(v___x_2244_);
return v___x_2245_;
}
else
{
lean_object* v___x_2246_; 
lean_dec_ref(v_xs_2232_);
v___x_2246_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2246_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = lean_unsigned_to_nat(12u);
v___x_2278_ = lean_nat_to_int(v___x_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(lean_object* v_x_2279_, lean_object* v_x_2280_, lean_object* v_x_2281_){
_start:
{
if (lean_obj_tag(v_x_2281_) == 0)
{
lean_dec(v_x_2279_);
return v_x_2280_;
}
else
{
lean_object* v_head_2282_; lean_object* v_tail_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2294_; 
v_head_2282_ = lean_ctor_get(v_x_2281_, 0);
v_tail_2283_ = lean_ctor_get(v_x_2281_, 1);
v_isSharedCheck_2294_ = !lean_is_exclusive(v_x_2281_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2285_ = v_x_2281_;
v_isShared_2286_ = v_isSharedCheck_2294_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_tail_2283_);
lean_inc(v_head_2282_);
lean_dec(v_x_2281_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2294_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
lean_inc(v_x_2279_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set_tag(v___x_2285_, 5);
lean_ctor_set(v___x_2285_, 1, v_x_2279_);
lean_ctor_set(v___x_2285_, 0, v_x_2280_);
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_x_2280_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_x_2279_);
v___x_2288_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2289_ = lean_unsigned_to_nat(0u);
v___x_2290_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_2282_, v___x_2289_);
v___x_2291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2288_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v_x_2280_ = v___x_2291_;
v_x_2281_ = v_tail_2283_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(lean_object* v_x_2295_, lean_object* v_x_2296_, lean_object* v_x_2297_){
_start:
{
if (lean_obj_tag(v_x_2297_) == 0)
{
lean_dec(v_x_2295_);
return v_x_2296_;
}
else
{
lean_object* v_head_2298_; lean_object* v_tail_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2310_; 
v_head_2298_ = lean_ctor_get(v_x_2297_, 0);
v_tail_2299_ = lean_ctor_get(v_x_2297_, 1);
v_isSharedCheck_2310_ = !lean_is_exclusive(v_x_2297_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2301_ = v_x_2297_;
v_isShared_2302_ = v_isSharedCheck_2310_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_tail_2299_);
lean_inc(v_head_2298_);
lean_dec(v_x_2297_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2310_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
lean_inc(v_x_2295_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set_tag(v___x_2301_, 5);
lean_ctor_set(v___x_2301_, 1, v_x_2295_);
lean_ctor_set(v___x_2301_, 0, v_x_2296_);
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_x_2296_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_x_2295_);
v___x_2304_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2305_ = lean_unsigned_to_nat(0u);
v___x_2306_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_2298_, v___x_2305_);
v___x_2307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2304_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(v_x_2295_, v___x_2307_, v_tail_2299_);
return v___x_2308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(lean_object* v_x_2311_, lean_object* v_x_2312_){
_start:
{
if (lean_obj_tag(v_x_2311_) == 0)
{
lean_object* v___x_2313_; 
lean_dec(v_x_2312_);
v___x_2313_ = lean_box(0);
return v___x_2313_;
}
else
{
lean_object* v_tail_2314_; 
v_tail_2314_ = lean_ctor_get(v_x_2311_, 1);
if (lean_obj_tag(v_tail_2314_) == 0)
{
lean_object* v_head_2315_; lean_object* v___x_2316_; 
lean_dec(v_x_2312_);
v_head_2315_ = lean_ctor_get(v_x_2311_, 0);
lean_inc(v_head_2315_);
lean_dec_ref_known(v_x_2311_, 2);
v___x_2316_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_2315_);
return v___x_2316_;
}
else
{
lean_object* v_head_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
lean_inc(v_tail_2314_);
v_head_2317_ = lean_ctor_get(v_x_2311_, 0);
lean_inc(v_head_2317_);
lean_dec_ref_known(v_x_2311_, 2);
v___x_2318_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_2317_);
v___x_2319_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(v_x_2312_, v___x_2318_, v_tail_2314_);
return v___x_2319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(lean_object* v_xs_2320_){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2321_ = lean_array_get_size(v_xs_2320_);
v___x_2322_ = lean_unsigned_to_nat(0u);
v___x_2323_ = lean_nat_dec_eq(v___x_2321_, v___x_2322_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2324_ = lean_array_to_list(v_xs_2320_);
v___x_2325_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2326_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_2324_, v___x_2325_);
v___x_2327_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2328_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
lean_ctor_set(v___x_2329_, 1, v___x_2326_);
v___x_2330_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2329_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2327_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
v___x_2333_ = l_Std_Format_fill(v___x_2332_);
return v___x_2333_;
}
else
{
lean_object* v___x_2334_; 
lean_dec_ref(v_xs_2320_);
v___x_2334_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2334_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0));
v___x_2337_ = lean_string_length(v___x_2336_);
return v___x_2337_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9);
v___x_2339_ = lean_nat_to_int(v___x_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_x_2345_){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; uint8_t v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2346_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__6));
v___x_2347_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_2348_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_x_2345_);
v___x_2349_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2347_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = 0;
v___x_2351_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2351_, 0, v___x_2349_);
lean_ctor_set_uint8(v___x_2351_, sizeof(void*)*1, v___x_2350_);
v___x_2352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2346_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
v___x_2353_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_2354_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_2355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
lean_ctor_set(v___x_2355_, 1, v___x_2352_);
v___x_2356_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_2357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2353_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
lean_ctor_set_uint8(v___x_2359_, sizeof(void*)*1, v___x_2350_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(lean_object* v_x_2360_, lean_object* v_x_2361_, lean_object* v_x_2362_){
_start:
{
if (lean_obj_tag(v_x_2362_) == 0)
{
lean_dec(v_x_2360_);
return v_x_2361_;
}
else
{
lean_object* v_head_2363_; lean_object* v_tail_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2374_; 
v_head_2363_ = lean_ctor_get(v_x_2362_, 0);
v_tail_2364_ = lean_ctor_get(v_x_2362_, 1);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_x_2362_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2366_ = v_x_2362_;
v_isShared_2367_ = v_isSharedCheck_2374_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_tail_2364_);
lean_inc(v_head_2363_);
lean_dec(v_x_2362_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2374_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
lean_inc(v_x_2360_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set_tag(v___x_2366_, 5);
lean_ctor_set(v___x_2366_, 1, v_x_2360_);
lean_ctor_set(v___x_2366_, 0, v_x_2361_);
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_x_2361_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v_x_2360_);
v___x_2369_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_2363_);
v___x_2371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v_x_2361_ = v___x_2371_;
v_x_2362_ = v_tail_2364_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(lean_object* v_x_2375_, lean_object* v_x_2376_, lean_object* v_x_2377_){
_start:
{
if (lean_obj_tag(v_x_2377_) == 0)
{
lean_dec(v_x_2375_);
return v_x_2376_;
}
else
{
lean_object* v_head_2378_; lean_object* v_tail_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2389_; 
v_head_2378_ = lean_ctor_get(v_x_2377_, 0);
v_tail_2379_ = lean_ctor_get(v_x_2377_, 1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_x_2377_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2381_ = v_x_2377_;
v_isShared_2382_ = v_isSharedCheck_2389_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_tail_2379_);
lean_inc(v_head_2378_);
lean_dec(v_x_2377_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2389_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
lean_inc(v_x_2375_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set_tag(v___x_2381_, 5);
lean_ctor_set(v___x_2381_, 1, v_x_2375_);
lean_ctor_set(v___x_2381_, 0, v_x_2376_);
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_x_2376_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_x_2375_);
v___x_2384_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2385_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_2378_);
v___x_2386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2384_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(v_x_2375_, v___x_2386_, v_tail_2379_);
return v___x_2387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(lean_object* v_x_2390_, lean_object* v_x_2391_){
_start:
{
if (lean_obj_tag(v_x_2390_) == 0)
{
lean_object* v___x_2392_; 
lean_dec(v_x_2391_);
v___x_2392_ = lean_box(0);
return v___x_2392_;
}
else
{
lean_object* v_tail_2393_; 
v_tail_2393_ = lean_ctor_get(v_x_2390_, 1);
if (lean_obj_tag(v_tail_2393_) == 0)
{
lean_object* v_head_2394_; lean_object* v___x_2395_; 
lean_dec(v_x_2391_);
v_head_2394_ = lean_ctor_get(v_x_2390_, 0);
lean_inc(v_head_2394_);
lean_dec_ref_known(v_x_2390_, 2);
v___x_2395_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_2394_);
return v___x_2395_;
}
else
{
lean_object* v_head_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
lean_inc(v_tail_2393_);
v_head_2396_ = lean_ctor_get(v_x_2390_, 0);
lean_inc(v_head_2396_);
lean_dec_ref_known(v_x_2390_, 2);
v___x_2397_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_2396_);
v___x_2398_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(v_x_2391_, v___x_2397_, v_tail_2393_);
return v___x_2398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(lean_object* v_xs_2399_){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2400_ = lean_array_get_size(v_xs_2399_);
v___x_2401_ = lean_unsigned_to_nat(0u);
v___x_2402_ = lean_nat_dec_eq(v___x_2400_, v___x_2401_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2403_ = lean_array_to_list(v_xs_2399_);
v___x_2404_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2405_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(v___x_2403_, v___x_2404_);
v___x_2406_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2407_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2408_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
lean_ctor_set(v___x_2408_, 1, v___x_2405_);
v___x_2409_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2410_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2406_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = l_Std_Format_fill(v___x_2411_);
return v___x_2412_;
}
else
{
lean_object* v___x_2413_; 
lean_dec_ref(v_xs_2399_);
v___x_2413_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2413_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = lean_unsigned_to_nat(0u);
v___x_2421_ = lean_nat_to_int(v___x_2420_);
return v___x_2421_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = lean_unsigned_to_nat(8u);
v___x_2438_ = lean_nat_to_int(v___x_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_x_2442_){
_start:
{
lean_object* v_term_2443_; lean_object* v_desc_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2476_; 
v_term_2443_ = lean_ctor_get(v_x_2442_, 0);
v_desc_2444_ = lean_ctor_get(v_x_2442_, 1);
v_isSharedCheck_2476_ = !lean_is_exclusive(v_x_2442_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2446_ = v_x_2442_;
v_isShared_2447_ = v_isSharedCheck_2476_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_desc_2444_);
lean_inc(v_term_2443_);
lean_dec(v_x_2442_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2476_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2453_; 
v___x_2448_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_2449_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__3));
v___x_2450_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_2451_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_term_2443_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set_tag(v___x_2446_, 4);
lean_ctor_set(v___x_2446_, 1, v___x_2451_);
lean_ctor_set(v___x_2446_, 0, v___x_2450_);
v___x_2453_ = v___x_2446_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
uint8_t v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2454_ = 0;
v___x_2455_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2455_, 0, v___x_2453_);
lean_ctor_set_uint8(v___x_2455_, sizeof(void*)*1, v___x_2454_);
v___x_2456_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2449_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_2458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2456_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
v___x_2459_ = lean_box(1);
v___x_2460_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2458_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__6));
v___x_2462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
lean_ctor_set(v___x_2463_, 1, v___x_2448_);
v___x_2464_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_desc_2444_);
v___x_2465_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2450_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
lean_ctor_set_uint8(v___x_2466_, sizeof(void*)*1, v___x_2454_);
v___x_2467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2463_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_2469_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_2470_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
lean_ctor_set(v___x_2470_, 1, v___x_2467_);
v___x_2471_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_2472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2468_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
v___x_2474_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2474_, 0, v___x_2473_);
lean_ctor_set_uint8(v___x_2474_, sizeof(void*)*1, v___x_2454_);
return v___x_2474_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(lean_object* v_x_2477_, lean_object* v_x_2478_, lean_object* v_x_2479_){
_start:
{
if (lean_obj_tag(v_x_2479_) == 0)
{
lean_dec(v_x_2477_);
return v_x_2478_;
}
else
{
lean_object* v_head_2480_; lean_object* v_tail_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2491_; 
v_head_2480_ = lean_ctor_get(v_x_2479_, 0);
v_tail_2481_ = lean_ctor_get(v_x_2479_, 1);
v_isSharedCheck_2491_ = !lean_is_exclusive(v_x_2479_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2483_ = v_x_2479_;
v_isShared_2484_ = v_isSharedCheck_2491_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_tail_2481_);
lean_inc(v_head_2480_);
lean_dec(v_x_2479_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2491_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
lean_inc(v_x_2477_);
if (v_isShared_2484_ == 0)
{
lean_ctor_set_tag(v___x_2483_, 5);
lean_ctor_set(v___x_2483_, 1, v_x_2477_);
lean_ctor_set(v___x_2483_, 0, v_x_2478_);
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_x_2478_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_x_2477_);
v___x_2486_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_2480_);
v___x_2488_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v_x_2478_ = v___x_2488_;
v_x_2479_ = v_tail_2481_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(lean_object* v_x_2492_, lean_object* v_x_2493_, lean_object* v_x_2494_){
_start:
{
if (lean_obj_tag(v_x_2494_) == 0)
{
lean_dec(v_x_2492_);
return v_x_2493_;
}
else
{
lean_object* v_head_2495_; lean_object* v_tail_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2506_; 
v_head_2495_ = lean_ctor_get(v_x_2494_, 0);
v_tail_2496_ = lean_ctor_get(v_x_2494_, 1);
v_isSharedCheck_2506_ = !lean_is_exclusive(v_x_2494_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2498_ = v_x_2494_;
v_isShared_2499_ = v_isSharedCheck_2506_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_tail_2496_);
lean_inc(v_head_2495_);
lean_dec(v_x_2494_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2506_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
lean_inc(v_x_2492_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set_tag(v___x_2498_, 5);
lean_ctor_set(v___x_2498_, 1, v_x_2492_);
lean_ctor_set(v___x_2498_, 0, v_x_2493_);
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_x_2493_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_x_2492_);
v___x_2501_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_2495_);
v___x_2503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(v_x_2492_, v___x_2503_, v_tail_2496_);
return v___x_2504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(lean_object* v_x_2507_, lean_object* v_x_2508_){
_start:
{
if (lean_obj_tag(v_x_2507_) == 0)
{
lean_object* v___x_2509_; 
lean_dec(v_x_2508_);
v___x_2509_ = lean_box(0);
return v___x_2509_;
}
else
{
lean_object* v_tail_2510_; 
v_tail_2510_ = lean_ctor_get(v_x_2507_, 1);
if (lean_obj_tag(v_tail_2510_) == 0)
{
lean_object* v_head_2511_; lean_object* v___x_2512_; 
lean_dec(v_x_2508_);
v_head_2511_ = lean_ctor_get(v_x_2507_, 0);
lean_inc(v_head_2511_);
lean_dec_ref_known(v_x_2507_, 2);
v___x_2512_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_2511_);
return v___x_2512_;
}
else
{
lean_object* v_head_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_inc(v_tail_2510_);
v_head_2513_ = lean_ctor_get(v_x_2507_, 0);
lean_inc(v_head_2513_);
lean_dec_ref_known(v_x_2507_, 2);
v___x_2514_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_2513_);
v___x_2515_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(v_x_2508_, v___x_2514_, v_tail_2510_);
return v___x_2515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(lean_object* v_xs_2516_){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2517_ = lean_array_get_size(v_xs_2516_);
v___x_2518_ = lean_unsigned_to_nat(0u);
v___x_2519_ = lean_nat_dec_eq(v___x_2517_, v___x_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2520_ = lean_array_to_list(v_xs_2516_);
v___x_2521_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2522_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(v___x_2520_, v___x_2521_);
v___x_2523_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2524_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
lean_ctor_set(v___x_2525_, 1, v___x_2522_);
v___x_2526_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2523_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
v___x_2529_ = l_Std_Format_fill(v___x_2528_);
return v___x_2529_;
}
else
{
lean_object* v___x_2530_; 
lean_dec_ref(v_xs_2516_);
v___x_2530_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(lean_object* v_x_2549_, lean_object* v_prec_2550_){
_start:
{
switch(lean_obj_tag(v_x_2549_))
{
case 0:
{
lean_object* v_contents_2551_; lean_object* v___y_2553_; lean_object* v___x_2561_; uint8_t v___x_2562_; 
v_contents_2551_ = lean_ctor_get(v_x_2549_, 0);
lean_inc_ref(v_contents_2551_);
lean_dec_ref_known(v_x_2549_, 1);
v___x_2561_ = lean_unsigned_to_nat(1024u);
v___x_2562_ = lean_nat_dec_le(v___x_2561_, v_prec_2550_);
if (v___x_2562_ == 0)
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2553_ = v___x_2563_;
goto v___jp_2552_;
}
else
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2553_ = v___x_2564_;
goto v___jp_2552_;
}
v___jp_2552_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2554_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__2));
v___x_2555_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_contents_2551_);
v___x_2556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2554_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
lean_inc(v___y_2553_);
v___x_2557_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___y_2553_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = 0;
v___x_2559_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2559_, 0, v___x_2557_);
lean_ctor_set_uint8(v___x_2559_, sizeof(void*)*1, v___x_2558_);
v___x_2560_ = l_Repr_addAppParen(v___x_2559_, v_prec_2550_);
return v___x_2560_;
}
}
case 1:
{
lean_object* v_content_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2585_; 
v_content_2565_ = lean_ctor_get(v_x_2549_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_x_2549_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2567_ = v_x_2549_;
v_isShared_2568_ = v_isSharedCheck_2585_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_content_2565_);
lean_dec(v_x_2549_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2585_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___y_2570_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v___x_2581_ = lean_unsigned_to_nat(1024u);
v___x_2582_ = lean_nat_dec_le(v___x_2581_, v_prec_2550_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; 
v___x_2583_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2570_ = v___x_2583_;
goto v___jp_2569_;
}
else
{
lean_object* v___x_2584_; 
v___x_2584_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2570_ = v___x_2584_;
goto v___jp_2569_;
}
v___jp_2569_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2574_; 
v___x_2571_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__5));
v___x_2572_ = l_String_quote(v_content_2565_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set_tag(v___x_2567_, 3);
lean_ctor_set(v___x_2567_, 0, v___x_2572_);
v___x_2574_ = v___x_2567_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2571_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
lean_inc(v___y_2570_);
v___x_2576_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___y_2570_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = 0;
v___x_2578_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2578_, 0, v___x_2576_);
lean_ctor_set_uint8(v___x_2578_, sizeof(void*)*1, v___x_2577_);
v___x_2579_ = l_Repr_addAppParen(v___x_2578_, v_prec_2550_);
return v___x_2579_;
}
}
}
}
case 2:
{
lean_object* v_items_2586_; lean_object* v___y_2588_; lean_object* v___x_2596_; uint8_t v___x_2597_; 
v_items_2586_ = lean_ctor_get(v_x_2549_, 0);
lean_inc_ref(v_items_2586_);
lean_dec_ref_known(v_x_2549_, 1);
v___x_2596_ = lean_unsigned_to_nat(1024u);
v___x_2597_ = lean_nat_dec_le(v___x_2596_, v_prec_2550_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; 
v___x_2598_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2588_ = v___x_2598_;
goto v___jp_2587_;
}
else
{
lean_object* v___x_2599_; 
v___x_2599_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2588_ = v___x_2599_;
goto v___jp_2587_;
}
v___jp_2587_:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2589_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__8));
v___x_2590_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_2586_);
v___x_2591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2589_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
lean_inc(v___y_2588_);
v___x_2592_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___y_2588_);
lean_ctor_set(v___x_2592_, 1, v___x_2591_);
v___x_2593_ = 0;
v___x_2594_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2594_, 0, v___x_2592_);
lean_ctor_set_uint8(v___x_2594_, sizeof(void*)*1, v___x_2593_);
v___x_2595_ = l_Repr_addAppParen(v___x_2594_, v_prec_2550_);
return v___x_2595_;
}
}
case 3:
{
lean_object* v_start_2600_; lean_object* v_items_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2636_; 
v_start_2600_ = lean_ctor_get(v_x_2549_, 0);
v_items_2601_ = lean_ctor_get(v_x_2549_, 1);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_x_2549_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2603_ = v_x_2549_;
v_isShared_2604_ = v_isSharedCheck_2636_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_items_2601_);
lean_inc(v_start_2600_);
lean_dec(v_x_2549_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2636_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2621_; lean_object* v___x_2632_; uint8_t v___x_2633_; 
v___x_2632_ = lean_unsigned_to_nat(1024u);
v___x_2633_ = lean_nat_dec_le(v___x_2632_, v_prec_2550_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; 
v___x_2634_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2621_ = v___x_2634_;
goto v___jp_2620_;
}
else
{
lean_object* v___x_2635_; 
v___x_2635_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2621_ = v___x_2635_;
goto v___jp_2620_;
}
v___jp_2605_:
{
lean_object* v___x_2611_; 
lean_inc(v___y_2607_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set_tag(v___x_2603_, 5);
lean_ctor_set(v___x_2603_, 1, v___y_2609_);
lean_ctor_set(v___x_2603_, 0, v___y_2607_);
v___x_2611_ = v___x_2603_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___y_2607_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v___y_2609_);
v___x_2611_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; uint8_t v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
lean_inc(v___y_2608_);
v___x_2612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
lean_ctor_set(v___x_2612_, 1, v___y_2608_);
v___x_2613_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_2601_);
v___x_2614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2612_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
lean_inc(v___y_2606_);
v___x_2615_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___y_2606_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = 0;
v___x_2617_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2617_, 0, v___x_2615_);
lean_ctor_set_uint8(v___x_2617_, sizeof(void*)*1, v___x_2616_);
v___x_2618_ = l_Repr_addAppParen(v___x_2617_, v_prec_2550_);
return v___x_2618_;
}
}
v___jp_2620_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___x_2622_ = lean_box(1);
v___x_2623_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__11));
v___x_2624_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12, &l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12);
v___x_2625_ = lean_int_dec_lt(v_start_2600_, v___x_2624_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = l_Int_repr(v_start_2600_);
lean_dec(v_start_2600_);
v___x_2627_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
v___y_2606_ = v___y_2621_;
v___y_2607_ = v___x_2623_;
v___y_2608_ = v___x_2622_;
v___y_2609_ = v___x_2627_;
goto v___jp_2605_;
}
else
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2628_ = lean_unsigned_to_nat(1024u);
v___x_2629_ = l_Int_repr(v_start_2600_);
lean_dec(v_start_2600_);
v___x_2630_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
v___x_2631_ = l_Repr_addAppParen(v___x_2630_, v___x_2628_);
v___y_2606_ = v___y_2621_;
v___y_2607_ = v___x_2623_;
v___y_2608_ = v___x_2622_;
v___y_2609_ = v___x_2631_;
goto v___jp_2605_;
}
}
}
}
case 4:
{
lean_object* v_items_2637_; lean_object* v___y_2639_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
v_items_2637_ = lean_ctor_get(v_x_2549_, 0);
lean_inc_ref(v_items_2637_);
lean_dec_ref_known(v_x_2549_, 1);
v___x_2647_ = lean_unsigned_to_nat(1024u);
v___x_2648_ = lean_nat_dec_le(v___x_2647_, v_prec_2550_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; 
v___x_2649_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2639_ = v___x_2649_;
goto v___jp_2638_;
}
else
{
lean_object* v___x_2650_; 
v___x_2650_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2639_ = v___x_2650_;
goto v___jp_2638_;
}
v___jp_2638_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; uint8_t v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2640_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__15));
v___x_2641_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(v_items_2637_);
v___x_2642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2640_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
lean_inc(v___y_2639_);
v___x_2643_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2643_, 0, v___y_2639_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
v___x_2644_ = 0;
v___x_2645_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2645_, 0, v___x_2643_);
lean_ctor_set_uint8(v___x_2645_, sizeof(void*)*1, v___x_2644_);
v___x_2646_ = l_Repr_addAppParen(v___x_2645_, v_prec_2550_);
return v___x_2646_;
}
}
case 5:
{
lean_object* v_items_2651_; lean_object* v___y_2653_; lean_object* v___x_2661_; uint8_t v___x_2662_; 
v_items_2651_ = lean_ctor_get(v_x_2549_, 0);
lean_inc_ref(v_items_2651_);
lean_dec_ref_known(v_x_2549_, 1);
v___x_2661_ = lean_unsigned_to_nat(1024u);
v___x_2662_ = lean_nat_dec_le(v___x_2661_, v_prec_2550_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; 
v___x_2663_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2653_ = v___x_2663_;
goto v___jp_2652_;
}
else
{
lean_object* v___x_2664_; 
v___x_2664_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2653_ = v___x_2664_;
goto v___jp_2652_;
}
v___jp_2652_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2654_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__18));
v___x_2655_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_items_2651_);
v___x_2656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2654_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
lean_inc(v___y_2653_);
v___x_2657_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___y_2653_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = 0;
v___x_2659_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2659_, 0, v___x_2657_);
lean_ctor_set_uint8(v___x_2659_, sizeof(void*)*1, v___x_2658_);
v___x_2660_ = l_Repr_addAppParen(v___x_2659_, v_prec_2550_);
return v___x_2660_;
}
}
case 6:
{
lean_object* v_content_2665_; lean_object* v___y_2667_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v_content_2665_ = lean_ctor_get(v_x_2549_, 0);
lean_inc_ref(v_content_2665_);
lean_dec_ref_known(v_x_2549_, 1);
v___x_2675_ = lean_unsigned_to_nat(1024u);
v___x_2676_ = lean_nat_dec_le(v___x_2675_, v_prec_2550_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2667_ = v___x_2677_;
goto v___jp_2666_;
}
else
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2667_ = v___x_2678_;
goto v___jp_2666_;
}
v___jp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2668_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__21));
v___x_2669_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_2665_);
v___x_2670_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2668_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
lean_inc(v___y_2667_);
v___x_2671_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___y_2667_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = 0;
v___x_2673_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2673_, 0, v___x_2671_);
lean_ctor_set_uint8(v___x_2673_, sizeof(void*)*1, v___x_2672_);
v___x_2674_ = l_Repr_addAppParen(v___x_2673_, v_prec_2550_);
return v___x_2674_;
}
}
default: 
{
lean_object* v_container_2679_; lean_object* v_content_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2730_; 
v_container_2679_ = lean_ctor_get(v_x_2549_, 0);
v_content_2680_ = lean_ctor_get(v_x_2549_, 1);
v_isSharedCheck_2730_ = !lean_is_exclusive(v_x_2549_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2682_ = v_x_2549_;
v_isShared_2683_ = v_isSharedCheck_2730_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_content_2680_);
lean_inc(v_container_2679_);
lean_dec(v_x_2549_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2730_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2688_; lean_object* v___y_2700_; lean_object* v___x_2726_; uint8_t v___x_2727_; 
v___x_2726_ = lean_unsigned_to_nat(1024u);
v___x_2727_ = lean_nat_dec_le(v___x_2726_, v_prec_2550_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2728_; 
v___x_2728_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2700_ = v___x_2728_;
goto v___jp_2699_;
}
else
{
lean_object* v___x_2729_; 
v___x_2729_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2700_ = v___x_2729_;
goto v___jp_2699_;
}
v___jp_2684_:
{
lean_object* v___x_2690_; 
lean_inc(v___y_2685_);
if (v_isShared_2683_ == 0)
{
lean_ctor_set_tag(v___x_2682_, 5);
lean_ctor_set(v___x_2682_, 1, v___y_2688_);
lean_ctor_set(v___x_2682_, 0, v___y_2685_);
v___x_2690_ = v___x_2682_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___y_2685_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v___y_2688_);
v___x_2690_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
lean_inc(v___y_2686_);
v___x_2691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2690_);
lean_ctor_set(v___x_2691_, 1, v___y_2686_);
v___x_2692_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_2680_);
v___x_2693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2691_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
lean_inc(v___y_2687_);
v___x_2694_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___y_2687_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = 0;
v___x_2696_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2696_, 0, v___x_2694_);
lean_ctor_set_uint8(v___x_2696_, sizeof(void*)*1, v___x_2695_);
v___x_2697_ = l_Repr_addAppParen(v___x_2696_, v_prec_2550_);
return v___x_2697_;
}
}
v___jp_2699_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = lean_box(1);
v___x_2702_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__24));
if (lean_obj_tag(v_container_2679_) == 0)
{
lean_object* v_val_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; lean_object* v___x_2712_; 
v_val_2703_ = lean_ctor_get(v_container_2679_, 0);
lean_inc(v_val_2703_);
lean_dec_ref_known(v_container_2679_, 1);
v___x_2704_ = ((lean_object*)(l_Lean_instReprElabBlock___lam__0___closed__3));
v___x_2705_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_2703_);
lean_dec(v_val_2703_);
v___x_2706_ = lean_unsigned_to_nat(0u);
v___x_2707_ = l_Lean_Name_reprPrec(v___x_2705_, v___x_2706_);
v___x_2708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2704_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__7));
v___x_2710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2708_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = 0;
v___x_2712_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2712_, 0, v___x_2710_);
lean_ctor_set_uint8(v___x_2712_, sizeof(void*)*1, v___x_2711_);
v___y_2685_ = v___x_2702_;
v___y_2686_ = v___x_2701_;
v___y_2687_ = v___y_2700_;
v___y_2688_ = v___x_2712_;
goto v___jp_2684_;
}
else
{
lean_object* v_index_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2725_; 
v_index_2713_ = lean_ctor_get(v_container_2679_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_container_2679_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2715_ = v_container_2679_;
v_isShared_2716_ = v_isSharedCheck_2725_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_index_2713_);
lean_dec(v_container_2679_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2725_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2720_; 
v___x_2717_ = ((lean_object*)(l_Lean_instReprElabBlock___lam__0___closed__6));
v___x_2718_ = l_Nat_reprFast(v_index_2713_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set_tag(v___x_2715_, 3);
lean_ctor_set(v___x_2715_, 0, v___x_2718_);
v___x_2720_ = v___x_2715_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2718_);
v___x_2720_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2721_; uint8_t v___x_2722_; lean_object* v___x_2723_; 
v___x_2721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2717_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = 0;
v___x_2723_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2723_, 0, v___x_2721_);
lean_ctor_set_uint8(v___x_2723_, sizeof(void*)*1, v___x_2722_);
v___y_2685_ = v___x_2702_;
v___y_2686_ = v___x_2701_;
v___y_2687_ = v___y_2700_;
v___y_2688_ = v___x_2723_;
goto v___jp_2684_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(lean_object* v___y_2731_){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2732_ = lean_unsigned_to_nat(0u);
v___x_2733_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v___y_2731_, v___x_2732_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___boxed(lean_object* v_x_2734_, lean_object* v_prec_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_x_2734_, v_prec_2735_);
lean_dec(v_prec_2735_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(lean_object* v_xs_2737_){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2738_ = lean_array_get_size(v_xs_2737_);
v___x_2739_ = lean_unsigned_to_nat(0u);
v___x_2740_ = lean_nat_dec_eq(v___x_2738_, v___x_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2741_ = lean_array_to_list(v_xs_2737_);
v___x_2742_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2743_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_2741_, v___x_2742_);
v___x_2744_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2745_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2745_);
lean_ctor_set(v___x_2746_, 1, v___x_2743_);
v___x_2747_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2746_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2744_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = l_Std_Format_fill(v___x_2749_);
return v___x_2750_;
}
else
{
lean_object* v___x_2751_; 
lean_dec_ref(v_xs_2737_);
v___x_2751_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2751_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(lean_object* v_x_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = ((lean_object*)(l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__1));
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___boxed(lean_object* v_x_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_2757_);
lean_dec(v_x_2757_);
return v_res_2758_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = lean_unsigned_to_nat(9u);
v___x_2769_ = lean_nat_to_int(v___x_2768_);
return v___x_2769_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2773_ = lean_unsigned_to_nat(15u);
v___x_2774_ = lean_nat_to_int(v___x_2773_);
return v___x_2774_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12(void){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = lean_unsigned_to_nat(11u);
v___x_2782_ = lean_nat_to_int(v___x_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(lean_object* v_x_2786_, lean_object* v_x_2787_, lean_object* v_x_2788_){
_start:
{
if (lean_obj_tag(v_x_2788_) == 0)
{
lean_dec(v_x_2786_);
return v_x_2787_;
}
else
{
lean_object* v_head_2789_; lean_object* v_tail_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2800_; 
v_head_2789_ = lean_ctor_get(v_x_2788_, 0);
v_tail_2790_ = lean_ctor_get(v_x_2788_, 1);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_x_2788_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2792_ = v_x_2788_;
v_isShared_2793_ = v_isSharedCheck_2800_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_tail_2790_);
lean_inc(v_head_2789_);
lean_dec(v_x_2788_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2800_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
lean_inc(v_x_2786_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set_tag(v___x_2792_, 5);
lean_ctor_set(v___x_2792_, 1, v_x_2786_);
lean_ctor_set(v___x_2792_, 0, v_x_2787_);
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_x_2787_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_x_2786_);
v___x_2795_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2796_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_2789_);
v___x_2797_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2795_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(v_x_2786_, v___x_2797_, v_tail_2790_);
return v___x_2798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(lean_object* v_x_2801_, lean_object* v_x_2802_){
_start:
{
if (lean_obj_tag(v_x_2801_) == 0)
{
lean_object* v___x_2803_; 
lean_dec(v_x_2802_);
v___x_2803_ = lean_box(0);
return v___x_2803_;
}
else
{
lean_object* v_tail_2804_; 
v_tail_2804_ = lean_ctor_get(v_x_2801_, 1);
if (lean_obj_tag(v_tail_2804_) == 0)
{
lean_object* v_head_2805_; lean_object* v___x_2806_; 
lean_dec(v_x_2802_);
v_head_2805_ = lean_ctor_get(v_x_2801_, 0);
lean_inc(v_head_2805_);
lean_dec_ref_known(v_x_2801_, 2);
v___x_2806_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_2805_);
return v___x_2806_;
}
else
{
lean_object* v_head_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
lean_inc(v_tail_2804_);
v_head_2807_ = lean_ctor_get(v_x_2801_, 0);
lean_inc(v_head_2807_);
lean_dec_ref_known(v_x_2801_, 2);
v___x_2808_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_2807_);
v___x_2809_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(v_x_2802_, v___x_2808_, v_tail_2804_);
return v___x_2809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(lean_object* v_xs_2810_){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2811_ = lean_array_get_size(v_xs_2810_);
v___x_2812_ = lean_unsigned_to_nat(0u);
v___x_2813_ = lean_nat_dec_eq(v___x_2811_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2814_ = lean_array_to_list(v_xs_2810_);
v___x_2815_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2816_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(v___x_2814_, v___x_2815_);
v___x_2817_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2818_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2819_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
lean_ctor_set(v___x_2819_, 1, v___x_2816_);
v___x_2820_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2821_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2819_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2817_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
v___x_2823_ = l_Std_Format_fill(v___x_2822_);
return v___x_2823_;
}
else
{
lean_object* v___x_2824_; 
lean_dec_ref(v_xs_2810_);
v___x_2824_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(lean_object* v_x_2825_){
_start:
{
lean_object* v_title_2826_; lean_object* v_titleString_2827_; lean_object* v_metadata_2828_; lean_object* v_content_2829_; lean_object* v_subParts_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; uint8_t v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v_title_2826_ = lean_ctor_get(v_x_2825_, 0);
lean_inc_ref(v_title_2826_);
v_titleString_2827_ = lean_ctor_get(v_x_2825_, 1);
lean_inc_ref(v_titleString_2827_);
v_metadata_2828_ = lean_ctor_get(v_x_2825_, 2);
lean_inc(v_metadata_2828_);
v_content_2829_ = lean_ctor_get(v_x_2825_, 3);
lean_inc_ref(v_content_2829_);
v_subParts_2830_ = lean_ctor_get(v_x_2825_, 4);
lean_inc_ref(v_subParts_2830_);
lean_dec_ref(v_x_2825_);
v___x_2831_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_2832_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__3));
v___x_2833_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4);
v___x_2834_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_title_2826_);
v___x_2835_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = 0;
v___x_2837_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2837_, 0, v___x_2835_);
lean_ctor_set_uint8(v___x_2837_, sizeof(void*)*1, v___x_2836_);
v___x_2838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2832_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_2840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2838_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
v___x_2841_ = lean_box(1);
v___x_2842_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2840_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
v___x_2843_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__6));
v___x_2844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2842_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
v___x_2845_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
lean_ctor_set(v___x_2845_, 1, v___x_2831_);
v___x_2846_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7);
v___x_2847_ = l_String_quote(v_titleString_2827_);
v___x_2848_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
v___x_2849_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2846_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
lean_ctor_set_uint8(v___x_2850_, sizeof(void*)*1, v___x_2836_);
v___x_2851_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2845_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
lean_ctor_set(v___x_2852_, 1, v___x_2839_);
v___x_2853_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
lean_ctor_set(v___x_2853_, 1, v___x_2841_);
v___x_2854_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__9));
v___x_2855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2853_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
v___x_2856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
lean_ctor_set(v___x_2856_, 1, v___x_2831_);
v___x_2857_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_2858_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_metadata_2828_);
lean_dec(v_metadata_2828_);
v___x_2859_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2857_);
lean_ctor_set(v___x_2859_, 1, v___x_2858_);
v___x_2860_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
lean_ctor_set_uint8(v___x_2860_, sizeof(void*)*1, v___x_2836_);
v___x_2861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2856_);
lean_ctor_set(v___x_2861_, 1, v___x_2860_);
v___x_2862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
lean_ctor_set(v___x_2862_, 1, v___x_2839_);
v___x_2863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2862_);
lean_ctor_set(v___x_2863_, 1, v___x_2841_);
v___x_2864_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__11));
v___x_2865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2863_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
lean_ctor_set(v___x_2866_, 1, v___x_2831_);
v___x_2867_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12);
v___x_2868_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_content_2829_);
v___x_2869_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2867_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v___x_2870_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
lean_ctor_set_uint8(v___x_2870_, sizeof(void*)*1, v___x_2836_);
v___x_2871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2866_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
v___x_2872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
lean_ctor_set(v___x_2872_, 1, v___x_2839_);
v___x_2873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
lean_ctor_set(v___x_2873_, 1, v___x_2841_);
v___x_2874_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__14));
v___x_2875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2873_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
v___x_2876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
lean_ctor_set(v___x_2876_, 1, v___x_2831_);
v___x_2877_ = l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(v_subParts_2830_);
v___x_2878_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2857_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
v___x_2879_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
lean_ctor_set_uint8(v___x_2879_, sizeof(void*)*1, v___x_2836_);
v___x_2880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2876_);
lean_ctor_set(v___x_2880_, 1, v___x_2879_);
v___x_2881_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_2882_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_2883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2882_);
lean_ctor_set(v___x_2883_, 1, v___x_2880_);
v___x_2884_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_2885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2883_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
v___x_2886_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2881_);
lean_ctor_set(v___x_2886_, 1, v___x_2885_);
v___x_2887_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
lean_ctor_set_uint8(v___x_2887_, sizeof(void*)*1, v___x_2836_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(lean_object* v_x_2888_, lean_object* v_x_2889_, lean_object* v_x_2890_){
_start:
{
if (lean_obj_tag(v_x_2890_) == 0)
{
lean_dec(v_x_2888_);
return v_x_2889_;
}
else
{
lean_object* v_head_2891_; lean_object* v_tail_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2902_; 
v_head_2891_ = lean_ctor_get(v_x_2890_, 0);
v_tail_2892_ = lean_ctor_get(v_x_2890_, 1);
v_isSharedCheck_2902_ = !lean_is_exclusive(v_x_2890_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2894_ = v_x_2890_;
v_isShared_2895_ = v_isSharedCheck_2902_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_tail_2892_);
lean_inc(v_head_2891_);
lean_dec(v_x_2890_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2902_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
lean_inc(v_x_2888_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set_tag(v___x_2894_, 5);
lean_ctor_set(v___x_2894_, 1, v_x_2888_);
lean_ctor_set(v___x_2894_, 0, v_x_2889_);
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_x_2889_);
lean_ctor_set(v_reuseFailAlloc_2901_, 1, v_x_2888_);
v___x_2897_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_2891_);
v___x_2899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2897_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
v_x_2889_ = v___x_2899_;
v_x_2890_ = v_tail_2892_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(lean_object* v_x_2903_, lean_object* v_x_2904_){
_start:
{
lean_object* v_fst_2905_; lean_object* v_snd_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2916_; 
v_fst_2905_ = lean_ctor_get(v_x_2903_, 0);
v_snd_2906_ = lean_ctor_get(v_x_2903_, 1);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_x_2903_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2908_ = v_x_2903_;
v_isShared_2909_ = v_isSharedCheck_2916_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_snd_2906_);
lean_inc(v_fst_2905_);
lean_dec(v_x_2903_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2916_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2910_ = l_Lean_instReprDeclarationRange_repr___redArg(v_fst_2905_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set_tag(v___x_2908_, 1);
lean_ctor_set(v___x_2908_, 1, v_x_2904_);
lean_ctor_set(v___x_2908_, 0, v___x_2910_);
v___x_2912_ = v___x_2908_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2915_, 1, v_x_2904_);
v___x_2912_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_snd_2906_);
v___x_2914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
lean_ctor_set(v___x_2914_, 1, v___x_2912_);
return v___x_2914_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(lean_object* v_x_2917_, lean_object* v_x_2918_, lean_object* v_x_2919_){
_start:
{
if (lean_obj_tag(v_x_2919_) == 0)
{
lean_dec(v_x_2917_);
return v_x_2918_;
}
else
{
lean_object* v_head_2920_; lean_object* v_tail_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2930_; 
v_head_2920_ = lean_ctor_get(v_x_2919_, 0);
v_tail_2921_ = lean_ctor_get(v_x_2919_, 1);
v_isSharedCheck_2930_ = !lean_is_exclusive(v_x_2919_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2923_ = v_x_2919_;
v_isShared_2924_ = v_isSharedCheck_2930_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_tail_2921_);
lean_inc(v_head_2920_);
lean_dec(v_x_2919_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2930_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
lean_inc(v_x_2917_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set_tag(v___x_2923_, 5);
lean_ctor_set(v___x_2923_, 1, v_x_2917_);
lean_ctor_set(v___x_2923_, 0, v_x_2918_);
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_x_2918_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_x_2917_);
v___x_2926_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
lean_object* v___x_2927_; 
v___x_2927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
lean_ctor_set(v___x_2927_, 1, v_head_2920_);
v_x_2918_ = v___x_2927_;
v_x_2919_ = v_tail_2921_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(lean_object* v_x_2931_, lean_object* v_x_2932_){
_start:
{
if (lean_obj_tag(v_x_2931_) == 0)
{
lean_object* v___x_2933_; 
lean_dec(v_x_2932_);
v___x_2933_ = lean_box(0);
return v___x_2933_;
}
else
{
lean_object* v_tail_2934_; 
v_tail_2934_ = lean_ctor_get(v_x_2931_, 1);
if (lean_obj_tag(v_tail_2934_) == 0)
{
lean_object* v_head_2935_; 
lean_dec(v_x_2932_);
v_head_2935_ = lean_ctor_get(v_x_2931_, 0);
lean_inc(v_head_2935_);
lean_dec_ref_known(v_x_2931_, 2);
return v_head_2935_;
}
else
{
lean_object* v_head_2936_; lean_object* v___x_2937_; 
lean_inc(v_tail_2934_);
v_head_2936_ = lean_ctor_get(v_x_2931_, 0);
lean_inc(v_head_2936_);
lean_dec_ref_known(v_x_2931_, 2);
v___x_2937_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(v_x_2932_, v_head_2936_, v_tail_2934_);
return v___x_2937_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0));
v___x_2941_ = lean_string_length(v___x_2940_);
return v___x_2941_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2);
v___x_2943_ = lean_nat_to_int(v___x_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(lean_object* v_x_2948_){
_start:
{
lean_object* v_fst_2949_; lean_object* v_snd_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2972_; 
v_fst_2949_ = lean_ctor_get(v_x_2948_, 0);
v_snd_2950_ = lean_ctor_get(v_x_2948_, 1);
v_isSharedCheck_2972_ = !lean_is_exclusive(v_x_2948_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2952_ = v_x_2948_;
v_isShared_2953_ = v_isSharedCheck_2972_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_snd_2950_);
lean_inc(v_fst_2949_);
lean_dec(v_x_2948_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2972_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2958_; 
v___x_2954_ = l_Nat_reprFast(v_fst_2949_);
v___x_2955_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
v___x_2956_ = lean_box(0);
if (v_isShared_2953_ == 0)
{
lean_ctor_set_tag(v___x_2952_, 1);
lean_ctor_set(v___x_2952_, 1, v___x_2956_);
lean_ctor_set(v___x_2952_, 0, v___x_2955_);
v___x_2958_ = v___x_2952_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2955_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v___x_2956_);
v___x_2958_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; uint8_t v___x_2969_; lean_object* v___x_2970_; 
v___x_2959_ = l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(v_snd_2950_, v___x_2958_);
v___x_2960_ = l_List_reverse___redArg(v___x_2959_);
v___x_2961_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2962_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(v___x_2960_, v___x_2961_);
v___x_2963_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3);
v___x_2964_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4));
v___x_2965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
lean_ctor_set(v___x_2965_, 1, v___x_2962_);
v___x_2966_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__5));
v___x_2967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2965_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
v___x_2968_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2963_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
v___x_2969_ = 0;
v___x_2970_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2970_, 0, v___x_2968_);
lean_ctor_set_uint8(v___x_2970_, sizeof(void*)*1, v___x_2969_);
return v___x_2970_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(lean_object* v_x_2973_, lean_object* v_x_2974_, lean_object* v_x_2975_){
_start:
{
if (lean_obj_tag(v_x_2975_) == 0)
{
lean_dec(v_x_2973_);
return v_x_2974_;
}
else
{
lean_object* v_head_2976_; lean_object* v_tail_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2987_; 
v_head_2976_ = lean_ctor_get(v_x_2975_, 0);
v_tail_2977_ = lean_ctor_get(v_x_2975_, 1);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_x_2975_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2979_ = v_x_2975_;
v_isShared_2980_ = v_isSharedCheck_2987_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_tail_2977_);
lean_inc(v_head_2976_);
lean_dec(v_x_2975_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2987_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
lean_inc(v_x_2973_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set_tag(v___x_2979_, 5);
lean_ctor_set(v___x_2979_, 1, v_x_2973_);
lean_ctor_set(v___x_2979_, 0, v_x_2974_);
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_x_2974_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_x_2973_);
v___x_2982_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_2976_);
v___x_2984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2982_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v_x_2974_ = v___x_2984_;
v_x_2975_ = v_tail_2977_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(lean_object* v_x_2988_, lean_object* v_x_2989_, lean_object* v_x_2990_){
_start:
{
if (lean_obj_tag(v_x_2990_) == 0)
{
lean_dec(v_x_2988_);
return v_x_2989_;
}
else
{
lean_object* v_head_2991_; lean_object* v_tail_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3002_; 
v_head_2991_ = lean_ctor_get(v_x_2990_, 0);
v_tail_2992_ = lean_ctor_get(v_x_2990_, 1);
v_isSharedCheck_3002_ = !lean_is_exclusive(v_x_2990_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2994_ = v_x_2990_;
v_isShared_2995_ = v_isSharedCheck_3002_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_tail_2992_);
lean_inc(v_head_2991_);
lean_dec(v_x_2990_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3002_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
lean_inc(v_x_2988_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set_tag(v___x_2994_, 5);
lean_ctor_set(v___x_2994_, 1, v_x_2988_);
lean_ctor_set(v___x_2994_, 0, v_x_2989_);
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_x_2989_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_x_2988_);
v___x_2997_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2998_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_2991_);
v___x_2999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2997_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
v___x_3000_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(v_x_2988_, v___x_2999_, v_tail_2992_);
return v___x_3000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(lean_object* v_x_3003_, lean_object* v_x_3004_){
_start:
{
if (lean_obj_tag(v_x_3003_) == 0)
{
lean_object* v___x_3005_; 
lean_dec(v_x_3004_);
v___x_3005_ = lean_box(0);
return v___x_3005_;
}
else
{
lean_object* v_tail_3006_; 
v_tail_3006_ = lean_ctor_get(v_x_3003_, 1);
if (lean_obj_tag(v_tail_3006_) == 0)
{
lean_object* v_head_3007_; lean_object* v___x_3008_; 
lean_dec(v_x_3004_);
v_head_3007_ = lean_ctor_get(v_x_3003_, 0);
lean_inc(v_head_3007_);
lean_dec_ref_known(v_x_3003_, 2);
v___x_3008_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3007_);
return v___x_3008_;
}
else
{
lean_object* v_head_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
lean_inc(v_tail_3006_);
v_head_3009_ = lean_ctor_get(v_x_3003_, 0);
lean_inc(v_head_3009_);
lean_dec_ref_known(v_x_3003_, 2);
v___x_3010_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3009_);
v___x_3011_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(v_x_3004_, v___x_3010_, v_tail_3006_);
return v___x_3011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(lean_object* v_xs_3012_){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v___x_3013_ = lean_array_get_size(v_xs_3012_);
v___x_3014_ = lean_unsigned_to_nat(0u);
v___x_3015_ = lean_nat_dec_eq(v___x_3013_, v___x_3014_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3016_ = lean_array_to_list(v_xs_3012_);
v___x_3017_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3018_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(v___x_3016_, v___x_3017_);
v___x_3019_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_3020_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
lean_ctor_set(v___x_3021_, 1, v___x_3018_);
v___x_3022_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_3023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3021_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
v___x_3024_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3019_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = l_Std_Format_fill(v___x_3024_);
return v___x_3025_;
}
else
{
lean_object* v___x_3026_; 
lean_dec_ref(v_xs_3012_);
v___x_3026_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_3026_;
}
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = lean_unsigned_to_nat(20u);
v___x_3043_ = lean_nat_to_int(v___x_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(lean_object* v_x_3044_){
_start:
{
lean_object* v_text_3045_; lean_object* v_sections_3046_; lean_object* v_declarationRange_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; uint8_t v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v_text_3045_ = lean_ctor_get(v_x_3044_, 0);
lean_inc_ref(v_text_3045_);
v_sections_3046_ = lean_ctor_get(v_x_3044_, 1);
lean_inc_ref(v_sections_3046_);
v_declarationRange_3047_ = lean_ctor_get(v_x_3044_, 2);
lean_inc_ref(v_declarationRange_3047_);
lean_dec_ref(v_x_3044_);
v___x_3048_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3049_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__3));
v___x_3050_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_3051_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_text_3045_);
v___x_3052_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3050_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___x_3053_ = 0;
v___x_3054_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3054_, 0, v___x_3052_);
lean_ctor_set_uint8(v___x_3054_, sizeof(void*)*1, v___x_3053_);
v___x_3055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3049_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
v___x_3056_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3055_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
v___x_3058_ = lean_box(1);
v___x_3059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3057_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
v___x_3060_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__5));
v___x_3061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3059_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
v___x_3062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
lean_ctor_set(v___x_3062_, 1, v___x_3048_);
v___x_3063_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3064_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(v_sections_3046_);
v___x_3065_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3063_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
lean_ctor_set_uint8(v___x_3066_, sizeof(void*)*1, v___x_3053_);
v___x_3067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3062_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
v___x_3068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
lean_ctor_set(v___x_3068_, 1, v___x_3056_);
v___x_3069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
lean_ctor_set(v___x_3069_, 1, v___x_3058_);
v___x_3070_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__7));
v___x_3071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3069_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set(v___x_3072_, 1, v___x_3048_);
v___x_3073_ = lean_obj_once(&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8, &l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8_once, _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8);
v___x_3074_ = l_Lean_instReprDeclarationRange_repr___redArg(v_declarationRange_3047_);
v___x_3075_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
lean_ctor_set_uint8(v___x_3076_, sizeof(void*)*1, v___x_3053_);
v___x_3077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3072_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3079_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3079_);
lean_ctor_set(v___x_3080_, 1, v___x_3077_);
v___x_3081_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3080_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
v___x_3083_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3078_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
lean_ctor_set_uint8(v___x_3084_, sizeof(void*)*1, v___x_3053_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr(lean_object* v_x_3085_, lean_object* v_prec_3086_){
_start:
{
lean_object* v___x_3087_; 
v___x_3087_ = l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(v_x_3085_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___boxed(lean_object* v_x_3088_, lean_object* v_prec_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Lean_VersoModuleDocs_instReprSnippet_repr(v_x_3088_, v_prec_3089_);
lean_dec(v_prec_3089_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(lean_object* v_x_3091_, lean_object* v_x_3092_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_x_3091_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___boxed(lean_object* v_x_3094_, lean_object* v_x_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(v_x_3094_, v_x_3095_);
lean_dec(v_x_3095_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_3097_, lean_object* v_prec_3098_){
_start:
{
lean_object* v___x_3099_; 
v___x_3099_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_x_3097_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_x_3100_, lean_object* v_prec_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(v_x_3100_, v_prec_3101_);
lean_dec(v_prec_3101_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(lean_object* v_x_3103_, lean_object* v_prec_3104_){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_x_3103_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_x_3106_, lean_object* v_prec_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(v_x_3106_, v_prec_3107_);
lean_dec(v_prec_3107_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(lean_object* v_x_3109_, lean_object* v_x_3110_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_3109_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___boxed(lean_object* v_x_3112_, lean_object* v_x_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(v_x_3112_, v_x_3113_);
lean_dec(v_x_3113_);
lean_dec(v_x_3112_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(lean_object* v_x_3115_, lean_object* v_prec_3116_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_x_3115_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___boxed(lean_object* v_x_3118_, lean_object* v_prec_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(v_x_3118_, v_prec_3119_);
lean_dec(v_prec_3119_);
return v_res_3120_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_Snippet_canNestIn(lean_object* v_level_3123_, lean_object* v_snippet_3124_){
_start:
{
lean_object* v_sections_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; uint8_t v___x_3128_; 
v_sections_3125_ = lean_ctor_get(v_snippet_3124_, 1);
v___x_3126_ = lean_unsigned_to_nat(0u);
v___x_3127_ = lean_array_get_size(v_sections_3125_);
v___x_3128_ = lean_nat_dec_lt(v___x_3126_, v___x_3127_);
if (v___x_3128_ == 0)
{
uint8_t v___x_3129_; 
v___x_3129_ = 1;
return v___x_3129_;
}
else
{
lean_object* v___x_3130_; lean_object* v_fst_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; uint8_t v___x_3134_; 
v___x_3130_ = lean_array_fget_borrowed(v_sections_3125_, v___x_3126_);
v_fst_3131_ = lean_ctor_get(v___x_3130_, 0);
v___x_3132_ = lean_unsigned_to_nat(1u);
v___x_3133_ = lean_nat_add(v_level_3123_, v___x_3132_);
v___x_3134_ = lean_nat_dec_le(v_fst_3131_, v___x_3133_);
lean_dec(v___x_3133_);
return v___x_3134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_canNestIn___boxed(lean_object* v_level_3135_, lean_object* v_snippet_3136_){
_start:
{
uint8_t v_res_3137_; lean_object* v_r_3138_; 
v_res_3137_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_level_3135_, v_snippet_3136_);
lean_dec_ref(v_snippet_3136_);
lean_dec(v_level_3135_);
v_r_3138_ = lean_box(v_res_3137_);
return v_r_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting(lean_object* v_snippet_3139_){
_start:
{
lean_object* v_sections_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; 
v_sections_3140_ = lean_ctor_get(v_snippet_3139_, 1);
v___x_3141_ = lean_array_get_size(v_sections_3140_);
v___x_3142_ = lean_unsigned_to_nat(1u);
v___x_3143_ = lean_nat_sub(v___x_3141_, v___x_3142_);
v___x_3144_ = lean_nat_dec_lt(v___x_3143_, v___x_3141_);
if (v___x_3144_ == 0)
{
lean_object* v___x_3145_; 
lean_dec(v___x_3143_);
v___x_3145_ = lean_box(0);
return v___x_3145_;
}
else
{
lean_object* v___x_3146_; lean_object* v_fst_3147_; lean_object* v___x_3148_; 
v___x_3146_ = lean_array_fget_borrowed(v_sections_3140_, v___x_3143_);
lean_dec(v___x_3143_);
v_fst_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_fst_3147_);
v___x_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3148_, 0, v_fst_3147_);
return v___x_3148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting___boxed(lean_object* v_snippet_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_3149_);
lean_dec_ref(v_snippet_3149_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addBlock(lean_object* v_snippet_3151_, lean_object* v_block_3152_){
_start:
{
lean_object* v_text_3153_; lean_object* v_sections_3154_; lean_object* v_declarationRange_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; uint8_t v___x_3158_; 
v_text_3153_ = lean_ctor_get(v_snippet_3151_, 0);
v_sections_3154_ = lean_ctor_get(v_snippet_3151_, 1);
v_declarationRange_3155_ = lean_ctor_get(v_snippet_3151_, 2);
v___x_3156_ = lean_array_get_size(v_sections_3154_);
v___x_3157_ = lean_unsigned_to_nat(0u);
v___x_3158_ = lean_nat_dec_eq(v___x_3156_, v___x_3157_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; lean_object* v___x_3160_; uint8_t v___x_3161_; 
v___x_3159_ = lean_unsigned_to_nat(1u);
v___x_3160_ = lean_nat_sub(v___x_3156_, v___x_3159_);
v___x_3161_ = lean_nat_dec_lt(v___x_3160_, v___x_3156_);
if (v___x_3161_ == 0)
{
lean_dec(v___x_3160_);
lean_dec_ref(v_block_3152_);
return v_snippet_3151_;
}
else
{
lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3205_; 
lean_inc_ref(v_declarationRange_3155_);
lean_inc_ref(v_sections_3154_);
lean_inc_ref(v_text_3153_);
v_isSharedCheck_3205_ = !lean_is_exclusive(v_snippet_3151_);
if (v_isSharedCheck_3205_ == 0)
{
lean_object* v_unused_3206_; lean_object* v_unused_3207_; lean_object* v_unused_3208_; 
v_unused_3206_ = lean_ctor_get(v_snippet_3151_, 2);
lean_dec(v_unused_3206_);
v_unused_3207_ = lean_ctor_get(v_snippet_3151_, 1);
lean_dec(v_unused_3207_);
v_unused_3208_ = lean_ctor_get(v_snippet_3151_, 0);
lean_dec(v_unused_3208_);
v___x_3163_ = v_snippet_3151_;
v_isShared_3164_ = v_isSharedCheck_3205_;
goto v_resetjp_3162_;
}
else
{
lean_dec(v_snippet_3151_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3205_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v_v_3165_; lean_object* v_snd_3166_; lean_object* v_snd_3167_; lean_object* v_fst_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3203_; 
v_v_3165_ = lean_array_fget(v_sections_3154_, v___x_3160_);
v_snd_3166_ = lean_ctor_get(v_v_3165_, 1);
lean_inc(v_snd_3166_);
v_snd_3167_ = lean_ctor_get(v_snd_3166_, 1);
lean_inc(v_snd_3167_);
v_fst_3168_ = lean_ctor_get(v_v_3165_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v_v_3165_);
if (v_isSharedCheck_3203_ == 0)
{
lean_object* v_unused_3204_; 
v_unused_3204_ = lean_ctor_get(v_v_3165_, 1);
lean_dec(v_unused_3204_);
v___x_3170_ = v_v_3165_;
v_isShared_3171_ = v_isSharedCheck_3203_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_fst_3168_);
lean_dec(v_v_3165_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3203_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v_fst_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3201_; 
v_fst_3172_ = lean_ctor_get(v_snd_3166_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v_snd_3166_);
if (v_isSharedCheck_3201_ == 0)
{
lean_object* v_unused_3202_; 
v_unused_3202_ = lean_ctor_get(v_snd_3166_, 1);
lean_dec(v_unused_3202_);
v___x_3174_ = v_snd_3166_;
v_isShared_3175_ = v_isSharedCheck_3201_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_fst_3172_);
lean_dec(v_snd_3166_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3201_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v_title_3176_; lean_object* v_titleString_3177_; lean_object* v_metadata_3178_; lean_object* v_content_3179_; lean_object* v_subParts_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3200_; 
v_title_3176_ = lean_ctor_get(v_snd_3167_, 0);
v_titleString_3177_ = lean_ctor_get(v_snd_3167_, 1);
v_metadata_3178_ = lean_ctor_get(v_snd_3167_, 2);
v_content_3179_ = lean_ctor_get(v_snd_3167_, 3);
v_subParts_3180_ = lean_ctor_get(v_snd_3167_, 4);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_snd_3167_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3182_ = v_snd_3167_;
v_isShared_3183_ = v_isSharedCheck_3200_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_subParts_3180_);
lean_inc(v_content_3179_);
lean_inc(v_metadata_3178_);
lean_inc(v_titleString_3177_);
lean_inc(v_title_3176_);
lean_dec(v_snd_3167_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3200_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3184_; lean_object* v_xs_x27_3185_; lean_object* v___x_3186_; lean_object* v___x_3188_; 
v___x_3184_ = lean_box(0);
v_xs_x27_3185_ = lean_array_fset(v_sections_3154_, v___x_3160_, v___x_3184_);
v___x_3186_ = lean_array_push(v_content_3179_, v_block_3152_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 3, v___x_3186_);
v___x_3188_ = v___x_3182_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_title_3176_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_titleString_3177_);
lean_ctor_set(v_reuseFailAlloc_3199_, 2, v_metadata_3178_);
lean_ctor_set(v_reuseFailAlloc_3199_, 3, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3199_, 4, v_subParts_3180_);
v___x_3188_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
lean_object* v___x_3190_; 
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 1, v___x_3188_);
v___x_3190_ = v___x_3174_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_fst_3172_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v___x_3188_);
v___x_3190_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3192_; 
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 1, v___x_3190_);
v___x_3192_ = v___x_3170_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_fst_3168_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v___x_3190_);
v___x_3192_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
lean_object* v___x_3193_; lean_object* v___x_3195_; 
v___x_3193_ = lean_array_fset(v_xs_x27_3185_, v___x_3160_, v___x_3192_);
lean_dec(v___x_3160_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 1, v___x_3193_);
v___x_3195_ = v___x_3163_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_text_3153_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v___x_3193_);
lean_ctor_set(v_reuseFailAlloc_3196_, 2, v_declarationRange_3155_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
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
lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3216_; 
lean_inc_ref(v_declarationRange_3155_);
lean_inc_ref(v_sections_3154_);
lean_inc_ref(v_text_3153_);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_snippet_3151_);
if (v_isSharedCheck_3216_ == 0)
{
lean_object* v_unused_3217_; lean_object* v_unused_3218_; lean_object* v_unused_3219_; 
v_unused_3217_ = lean_ctor_get(v_snippet_3151_, 2);
lean_dec(v_unused_3217_);
v_unused_3218_ = lean_ctor_get(v_snippet_3151_, 1);
lean_dec(v_unused_3218_);
v_unused_3219_ = lean_ctor_get(v_snippet_3151_, 0);
lean_dec(v_unused_3219_);
v___x_3210_ = v_snippet_3151_;
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
else
{
lean_dec(v_snippet_3151_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3212_ = lean_array_push(v_text_3153_, v_block_3152_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3212_);
v___x_3214_ = v___x_3210_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3212_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v_sections_3154_);
lean_ctor_set(v_reuseFailAlloc_3215_, 2, v_declarationRange_3155_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addPart(lean_object* v_snippet_3220_, lean_object* v_level_3221_, lean_object* v_range_3222_, lean_object* v_part_3223_){
_start:
{
lean_object* v_text_3224_; lean_object* v_sections_3225_; lean_object* v_declarationRange_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3236_; 
v_text_3224_ = lean_ctor_get(v_snippet_3220_, 0);
v_sections_3225_ = lean_ctor_get(v_snippet_3220_, 1);
v_declarationRange_3226_ = lean_ctor_get(v_snippet_3220_, 2);
v_isSharedCheck_3236_ = !lean_is_exclusive(v_snippet_3220_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3228_ = v_snippet_3220_;
v_isShared_3229_ = v_isSharedCheck_3236_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_declarationRange_3226_);
lean_inc(v_sections_3225_);
lean_inc(v_text_3224_);
lean_dec(v_snippet_3220_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3236_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3234_; 
v___x_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3230_, 0, v_range_3222_);
lean_ctor_set(v___x_3230_, 1, v_part_3223_);
v___x_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3231_, 0, v_level_3221_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
v___x_3232_ = lean_array_push(v_sections_3225_, v___x_3231_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 1, v___x_3232_);
v___x_3234_ = v___x_3228_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_text_3224_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3235_, 2, v_declarationRange_3226_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0(void){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = lean_unsigned_to_nat(32u);
v___x_3238_ = lean_mk_empty_array_with_capacity(v___x_3237_);
v___x_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3238_);
return v___x_3239_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1(void){
_start:
{
size_t v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3240_ = ((size_t)5ULL);
v___x_3241_ = lean_unsigned_to_nat(0u);
v___x_3242_ = lean_unsigned_to_nat(32u);
v___x_3243_ = lean_mk_empty_array_with_capacity(v___x_3242_);
v___x_3244_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_3245_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3245_, 0, v___x_3244_);
lean_ctor_set(v___x_3245_, 1, v___x_3243_);
lean_ctor_set(v___x_3245_, 2, v___x_3241_);
lean_ctor_set(v___x_3245_, 3, v___x_3241_);
lean_ctor_set_usize(v___x_3245_, 4, v___x_3240_);
return v___x_3245_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default(void){
_start:
{
lean_object* v___x_3246_; 
v___x_3246_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__1, &l_Lean_instInhabitedVersoModuleDocs_default___closed__1_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1);
return v___x_3246_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs(void){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Lean_instInhabitedVersoModuleDocs_default;
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(lean_object* v_as_3248_, lean_object* v_i_3249_){
_start:
{
lean_object* v_zero_3250_; uint8_t v_isZero_3251_; 
v_zero_3250_ = lean_unsigned_to_nat(0u);
v_isZero_3251_ = lean_nat_dec_eq(v_i_3249_, v_zero_3250_);
if (v_isZero_3251_ == 1)
{
lean_object* v___x_3252_; 
lean_dec(v_i_3249_);
v___x_3252_ = lean_box(0);
return v___x_3252_;
}
else
{
lean_object* v_one_3253_; lean_object* v_n_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v_one_3253_ = lean_unsigned_to_nat(1u);
v_n_3254_ = lean_nat_sub(v_i_3249_, v_one_3253_);
lean_dec(v_i_3249_);
v___x_3255_ = lean_array_fget_borrowed(v_as_3248_, v_n_3254_);
v___x_3256_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v___x_3255_);
if (lean_obj_tag(v___x_3256_) == 0)
{
v_i_3249_ = v_n_3254_;
goto _start;
}
else
{
lean_dec(v_n_3254_);
return v___x_3256_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg___boxed(lean_object* v_as_3258_, lean_object* v_i_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_as_3258_, v_i_3259_);
lean_dec_ref(v_as_3258_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(lean_object* v_as_3261_, lean_object* v_i_3262_){
_start:
{
lean_object* v_zero_3263_; uint8_t v_isZero_3264_; 
v_zero_3263_ = lean_unsigned_to_nat(0u);
v_isZero_3264_ = lean_nat_dec_eq(v_i_3262_, v_zero_3263_);
if (v_isZero_3264_ == 1)
{
lean_object* v___x_3265_; 
lean_dec(v_i_3262_);
v___x_3265_ = lean_box(0);
return v___x_3265_;
}
else
{
lean_object* v_one_3266_; lean_object* v_n_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v_one_3266_ = lean_unsigned_to_nat(1u);
v_n_3267_ = lean_nat_sub(v_i_3262_, v_one_3266_);
lean_dec(v_i_3262_);
v___x_3268_ = lean_array_fget_borrowed(v_as_3261_, v_n_3267_);
v___x_3269_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v___x_3268_);
if (lean_obj_tag(v___x_3269_) == 0)
{
v_i_3262_ = v_n_3267_;
goto _start;
}
else
{
lean_dec(v_n_3267_);
return v___x_3269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(lean_object* v_x_3271_){
_start:
{
if (lean_obj_tag(v_x_3271_) == 0)
{
lean_object* v_cs_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v_cs_3272_ = lean_ctor_get(v_x_3271_, 0);
v___x_3273_ = lean_array_get_size(v_cs_3272_);
v___x_3274_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_cs_3272_, v___x_3273_);
return v___x_3274_;
}
else
{
lean_object* v_vs_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_vs_3275_ = lean_ctor_get(v_x_3271_, 0);
v___x_3276_ = lean_array_get_size(v_vs_3275_);
v___x_3277_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_vs_3275_, v___x_3276_);
return v___x_3277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1___boxed(lean_object* v_x_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v_x_3278_);
lean_dec_ref(v_x_3278_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_as_3280_, lean_object* v_i_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_as_3280_, v_i_3281_);
lean_dec_ref(v_as_3280_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(lean_object* v_t_3283_){
_start:
{
lean_object* v_root_3284_; lean_object* v_tail_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_root_3284_ = lean_ctor_get(v_t_3283_, 0);
v_tail_3285_ = lean_ctor_get(v_t_3283_, 1);
v___x_3286_ = lean_array_get_size(v_tail_3285_);
v___x_3287_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_tail_3285_, v___x_3286_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v___x_3288_; 
v___x_3288_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v_root_3284_);
return v___x_3288_;
}
else
{
return v___x_3287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0___boxed(lean_object* v_t_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_t_3289_);
lean_dec_ref(v_t_3289_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_terminalNesting(lean_object* v_x_3291_){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_x_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_terminalNesting___boxed(lean_object* v_x_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Lean_VersoModuleDocs_terminalNesting(v_x_3293_);
lean_dec_ref(v_x_3293_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0(lean_object* v_as_3295_, lean_object* v_i_3296_, lean_object* v_a_3297_){
_start:
{
lean_object* v___x_3298_; 
v___x_3298_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_as_3295_, v_i_3296_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___boxed(lean_object* v_as_3299_, lean_object* v_i_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0(v_as_3299_, v_i_3300_, v_a_3301_);
lean_dec_ref(v_as_3299_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2(lean_object* v_as_3303_, lean_object* v_i_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_as_3303_, v_i_3304_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___boxed(lean_object* v_as_3307_, lean_object* v_i_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2(v_as_3307_, v_i_3308_, v_a_3309_);
lean_dec_ref(v_as_3307_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0(lean_object* v___x_3317_, lean_object* v_v_3318_, lean_object* v_x_3319_){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; uint8_t v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3320_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___x_3321_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3322_ = lean_box(1);
v___x_3323_ = ((lean_object*)(l_Lean_instReprVersoModuleDocs___lam__0___closed__2));
v___x_3324_ = l_Lean_PersistentArray_toArray___redArg(v_v_3318_);
v___x_3325_ = l_Array_repr___redArg(v___x_3317_, v___x_3324_);
v___x_3326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3323_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
v___x_3327_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3320_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = 0;
v___x_3329_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3329_, 0, v___x_3327_);
lean_ctor_set_uint8(v___x_3329_, sizeof(void*)*1, v___x_3328_);
lean_inc_ref(v___x_3329_);
v___x_3330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3321_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
v___x_3331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
lean_ctor_set(v___x_3331_, 1, v___x_3322_);
v___x_3332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3331_);
lean_ctor_set(v___x_3332_, 1, v___x_3329_);
v___x_3333_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3332_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3320_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
lean_ctor_set_uint8(v___x_3336_, sizeof(void*)*1, v___x_3328_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0___boxed(lean_object* v___x_3337_, lean_object* v_v_3338_, lean_object* v_x_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_instReprVersoModuleDocs___lam__0(v___x_3337_, v_v_3338_, v_x_3339_);
lean_dec(v_x_3339_);
lean_dec_ref(v_v_3338_);
return v_res_3340_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_isEmpty(lean_object* v_docs_3344_){
_start:
{
uint8_t v___x_3345_; 
v___x_3345_ = l_Lean_PersistentArray_isEmpty___redArg(v_docs_3344_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_isEmpty___boxed(lean_object* v_docs_3346_){
_start:
{
uint8_t v_res_3347_; lean_object* v_r_3348_; 
v_res_3347_ = l_Lean_VersoModuleDocs_isEmpty(v_docs_3346_);
lean_dec_ref(v_docs_3346_);
v_r_3348_ = lean_box(v_res_3347_);
return v_r_3348_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_canAdd(lean_object* v_docs_3349_, lean_object* v_snippet_3350_){
_start:
{
lean_object* v___x_3351_; 
v___x_3351_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_3349_);
if (lean_obj_tag(v___x_3351_) == 1)
{
lean_object* v_val_3352_; uint8_t v___x_3353_; 
v_val_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_val_3352_);
lean_dec_ref_known(v___x_3351_, 1);
v___x_3353_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_3352_, v_snippet_3350_);
lean_dec(v_val_3352_);
return v___x_3353_;
}
else
{
uint8_t v___x_3354_; 
lean_dec(v___x_3351_);
v___x_3354_ = 1;
return v___x_3354_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_canAdd___boxed(lean_object* v_docs_3355_, lean_object* v_snippet_3356_){
_start:
{
uint8_t v_res_3357_; lean_object* v_r_3358_; 
v_res_3357_ = l_Lean_VersoModuleDocs_canAdd(v_docs_3355_, v_snippet_3356_);
lean_dec_ref(v_snippet_3356_);
lean_dec_ref(v_docs_3355_);
v_r_3358_ = lean_box(v_res_3357_);
return v_r_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add(lean_object* v_docs_3362_, lean_object* v_snippet_3363_){
_start:
{
uint8_t v___x_3364_; 
v___x_3364_ = l_Lean_VersoModuleDocs_canAdd(v_docs_3362_, v_snippet_3363_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; 
lean_dec_ref(v_snippet_3363_);
lean_dec_ref(v_docs_3362_);
v___x_3365_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__1));
return v___x_3365_;
}
else
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = l_Lean_PersistentArray_push___redArg(v_docs_3362_, v_snippet_3363_);
v___x_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3366_);
return v___x_3367_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(lean_object* v_msg_3368_){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_3370_ = lean_panic_fn_borrowed(v___x_3369_, v_msg_3368_);
return v___x_3370_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_add_x21___closed__2(void){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3373_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__0));
v___x_3374_ = lean_unsigned_to_nat(4u);
v___x_3375_ = lean_unsigned_to_nat(367u);
v___x_3376_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__1));
v___x_3377_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__0));
v___x_3378_ = l_mkPanicMessageWithDecl(v___x_3377_, v___x_3376_, v___x_3375_, v___x_3374_, v___x_3373_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add_x21(lean_object* v_docs_3379_, lean_object* v_snippet_3380_){
_start:
{
lean_object* v___x_3381_; 
v___x_3381_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_3379_);
if (lean_obj_tag(v___x_3381_) == 1)
{
lean_object* v_val_3382_; uint8_t v___x_3383_; 
v_val_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_val_3382_);
lean_dec_ref_known(v___x_3381_, 1);
v___x_3383_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_3382_, v_snippet_3380_);
lean_dec(v_val_3382_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
lean_dec_ref(v_snippet_3380_);
lean_dec_ref(v_docs_3379_);
v___x_3384_ = lean_obj_once(&l_Lean_VersoModuleDocs_add_x21___closed__2, &l_Lean_VersoModuleDocs_add_x21___closed__2_once, _init_l_Lean_VersoModuleDocs_add_x21___closed__2);
v___x_3385_ = l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(v___x_3384_);
return v___x_3385_;
}
else
{
lean_object* v___x_3386_; 
v___x_3386_ = l_Lean_PersistentArray_push___redArg(v_docs_3379_, v_snippet_3380_);
return v___x_3386_;
}
}
else
{
lean_object* v___x_3387_; 
lean_dec(v___x_3381_);
v___x_3387_ = l_Lean_PersistentArray_push___redArg(v_docs_3379_, v_snippet_3380_);
return v___x_3387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(lean_object* v_ctx_3388_){
_start:
{
lean_object* v_context_3389_; lean_object* v___x_3390_; 
v_context_3389_ = lean_ctor_get(v_ctx_3388_, 2);
v___x_3390_ = lean_array_get_size(v_context_3389_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level___boxed(lean_object* v_ctx_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_3391_);
lean_dec_ref(v_ctx_3391_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(lean_object* v_ctx_3396_){
_start:
{
lean_object* v_content_3397_; lean_object* v_priorParts_3398_; lean_object* v_context_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3422_; 
v_content_3397_ = lean_ctor_get(v_ctx_3396_, 0);
v_priorParts_3398_ = lean_ctor_get(v_ctx_3396_, 1);
v_context_3399_ = lean_ctor_get(v_ctx_3396_, 2);
v_isSharedCheck_3422_ = !lean_is_exclusive(v_ctx_3396_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3401_ = v_ctx_3396_;
v_isShared_3402_ = v_isSharedCheck_3422_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_context_3399_);
lean_inc(v_priorParts_3398_);
lean_inc(v_content_3397_);
lean_dec(v_ctx_3396_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3422_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; uint8_t v___x_3405_; 
v___x_3403_ = lean_array_get_size(v_context_3399_);
v___x_3404_ = lean_unsigned_to_nat(0u);
v___x_3405_ = lean_nat_dec_eq(v___x_3403_, v___x_3404_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v_last_3408_; lean_object* v_content_3409_; lean_object* v_priorParts_3410_; lean_object* v_titleString_3411_; lean_object* v_title_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3418_; 
v___x_3406_ = lean_unsigned_to_nat(1u);
v___x_3407_ = lean_nat_sub(v___x_3403_, v___x_3406_);
v_last_3408_ = lean_array_fget_borrowed(v_context_3399_, v___x_3407_);
lean_dec(v___x_3407_);
v_content_3409_ = lean_ctor_get(v_last_3408_, 0);
lean_inc_ref(v_content_3409_);
v_priorParts_3410_ = lean_ctor_get(v_last_3408_, 1);
v_titleString_3411_ = lean_ctor_get(v_last_3408_, 2);
v_title_3412_ = lean_ctor_get(v_last_3408_, 3);
v___x_3413_ = lean_box(0);
lean_inc_ref(v_titleString_3411_);
lean_inc_ref(v_title_3412_);
v___x_3414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3414_, 0, v_title_3412_);
lean_ctor_set(v___x_3414_, 1, v_titleString_3411_);
lean_ctor_set(v___x_3414_, 2, v___x_3413_);
lean_ctor_set(v___x_3414_, 3, v_content_3397_);
lean_ctor_set(v___x_3414_, 4, v_priorParts_3398_);
lean_inc_ref(v_priorParts_3410_);
v___x_3415_ = lean_array_push(v_priorParts_3410_, v___x_3414_);
v___x_3416_ = lean_array_pop(v_context_3399_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 2, v___x_3416_);
lean_ctor_set(v___x_3401_, 1, v___x_3415_);
lean_ctor_set(v___x_3401_, 0, v_content_3409_);
v___x_3418_ = v___x_3401_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_content_3409_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3420_, 2, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_object* v___x_3419_; 
v___x_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3418_);
return v___x_3419_;
}
}
else
{
lean_object* v___x_3421_; 
lean_del_object(v___x_3401_);
lean_dec_ref(v_context_3399_);
lean_dec_ref(v_priorParts_3398_);
lean_dec_ref(v_content_3397_);
v___x_3421_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__1));
return v___x_3421_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(lean_object* v_ctx_3423_){
_start:
{
lean_object* v_context_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; uint8_t v___x_3427_; 
v_context_3424_ = lean_ctor_get(v_ctx_3423_, 2);
v___x_3425_ = lean_array_get_size(v_context_3424_);
v___x_3426_ = lean_unsigned_to_nat(0u);
v___x_3427_ = lean_nat_dec_eq(v___x_3425_, v___x_3426_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; 
v___x_3428_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_3423_);
if (lean_obj_tag(v___x_3428_) == 0)
{
return v___x_3428_;
}
else
{
lean_object* v_a_3429_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
lean_dec_ref_known(v___x_3428_, 1);
v_ctx_3423_ = v_a_3429_;
goto _start;
}
}
else
{
lean_object* v___x_3431_; 
v___x_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3431_, 0, v_ctx_3423_);
return v___x_3431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(lean_object* v_ctx_3434_, lean_object* v_partLevel_3435_, lean_object* v_part_3436_){
_start:
{
lean_object* v___x_3437_; uint8_t v___x_3438_; 
v___x_3437_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_3434_);
v___x_3438_ = lean_nat_dec_lt(v___x_3437_, v_partLevel_3435_);
if (v___x_3438_ == 0)
{
uint8_t v___x_3439_; 
v___x_3439_ = lean_nat_dec_eq(v_partLevel_3435_, v___x_3437_);
lean_dec(v___x_3437_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; 
v___x_3440_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_3434_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_dec_ref(v_part_3436_);
lean_dec(v_partLevel_3435_);
return v___x_3440_;
}
else
{
lean_object* v_a_3441_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_a_3441_);
lean_dec_ref_known(v___x_3440_, 1);
v_ctx_3434_ = v_a_3441_;
goto _start;
}
}
else
{
lean_object* v_content_3443_; lean_object* v_priorParts_3444_; lean_object* v_context_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3454_; 
lean_dec(v_partLevel_3435_);
v_content_3443_ = lean_ctor_get(v_ctx_3434_, 0);
v_priorParts_3444_ = lean_ctor_get(v_ctx_3434_, 1);
v_context_3445_ = lean_ctor_get(v_ctx_3434_, 2);
v_isSharedCheck_3454_ = !lean_is_exclusive(v_ctx_3434_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3447_ = v_ctx_3434_;
v_isShared_3448_ = v_isSharedCheck_3454_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_context_3445_);
lean_inc(v_priorParts_3444_);
lean_inc(v_content_3443_);
lean_dec(v_ctx_3434_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3454_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; lean_object* v___x_3451_; 
v___x_3449_ = lean_array_push(v_priorParts_3444_, v_part_3436_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 1, v___x_3449_);
v___x_3451_ = v___x_3447_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_content_3443_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v___x_3449_);
lean_ctor_set(v_reuseFailAlloc_3453_, 2, v_context_3445_);
v___x_3451_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
return v___x_3452_;
}
}
}
}
else
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
lean_dec_ref(v_part_3436_);
lean_dec_ref(v_ctx_3434_);
v___x_3455_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__0));
v___x_3456_ = l_Nat_reprFast(v___x_3437_);
v___x_3457_ = lean_string_append(v___x_3455_, v___x_3456_);
lean_dec_ref(v___x_3456_);
v___x_3458_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__1));
v___x_3459_ = lean_string_append(v___x_3457_, v___x_3458_);
v___x_3460_ = l_Nat_reprFast(v_partLevel_3435_);
v___x_3461_ = lean_string_append(v___x_3459_, v___x_3460_);
lean_dec_ref(v___x_3460_);
v___x_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3461_);
return v___x_3462_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(lean_object* v_ctx_3466_, lean_object* v_blocks_3467_){
_start:
{
lean_object* v_content_3468_; lean_object* v_priorParts_3469_; lean_object* v_context_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3483_; 
v_content_3468_ = lean_ctor_get(v_ctx_3466_, 0);
v_priorParts_3469_ = lean_ctor_get(v_ctx_3466_, 1);
v_context_3470_ = lean_ctor_get(v_ctx_3466_, 2);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_ctx_3466_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3472_ = v_ctx_3466_;
v_isShared_3473_ = v_isSharedCheck_3483_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_context_3470_);
lean_inc(v_priorParts_3469_);
lean_inc(v_content_3468_);
lean_dec(v_ctx_3466_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3483_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; uint8_t v___x_3476_; 
v___x_3474_ = lean_array_get_size(v_priorParts_3469_);
v___x_3475_ = lean_unsigned_to_nat(0u);
v___x_3476_ = lean_nat_dec_eq(v___x_3474_, v___x_3475_);
if (v___x_3476_ == 0)
{
lean_object* v___x_3477_; 
lean_del_object(v___x_3472_);
lean_dec_ref(v_context_3470_);
lean_dec_ref(v_priorParts_3469_);
lean_dec_ref(v_content_3468_);
v___x_3477_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__1));
return v___x_3477_;
}
else
{
lean_object* v___x_3478_; lean_object* v___x_3480_; 
v___x_3478_ = l_Array_append___redArg(v_content_3468_, v_blocks_3467_);
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 0, v___x_3478_);
v___x_3480_ = v___x_3472_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3478_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_priorParts_3469_);
lean_ctor_set(v_reuseFailAlloc_3482_, 2, v_context_3470_);
v___x_3480_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
lean_object* v___x_3481_; 
v___x_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
return v___x_3481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___boxed(lean_object* v_ctx_3484_, lean_object* v_blocks_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_3484_, v_blocks_3485_);
lean_dec_ref(v_blocks_3485_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(lean_object* v_as_3487_, size_t v_sz_3488_, size_t v_i_3489_, lean_object* v_b_3490_){
_start:
{
uint8_t v___x_3491_; 
v___x_3491_ = lean_usize_dec_lt(v_i_3489_, v_sz_3488_);
if (v___x_3491_ == 0)
{
lean_object* v___x_3492_; 
v___x_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3492_, 0, v_b_3490_);
return v___x_3492_;
}
else
{
lean_object* v_a_3493_; lean_object* v_snd_3494_; lean_object* v_fst_3495_; lean_object* v_snd_3496_; lean_object* v___x_3497_; 
v_a_3493_ = lean_array_uget_borrowed(v_as_3487_, v_i_3489_);
v_snd_3494_ = lean_ctor_get(v_a_3493_, 1);
v_fst_3495_ = lean_ctor_get(v_a_3493_, 0);
v_snd_3496_ = lean_ctor_get(v_snd_3494_, 1);
lean_inc(v_snd_3496_);
lean_inc(v_fst_3495_);
v___x_3497_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(v_b_3490_, v_fst_3495_, v_snd_3496_);
if (lean_obj_tag(v___x_3497_) == 0)
{
return v___x_3497_;
}
else
{
lean_object* v_a_3498_; size_t v___x_3499_; size_t v___x_3500_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
v___x_3499_ = ((size_t)1ULL);
v___x_3500_ = lean_usize_add(v_i_3489_, v___x_3499_);
v_i_3489_ = v___x_3500_;
v_b_3490_ = v_a_3498_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0___boxed(lean_object* v_as_3502_, lean_object* v_sz_3503_, lean_object* v_i_3504_, lean_object* v_b_3505_){
_start:
{
size_t v_sz_boxed_3506_; size_t v_i_boxed_3507_; lean_object* v_res_3508_; 
v_sz_boxed_3506_ = lean_unbox_usize(v_sz_3503_);
lean_dec(v_sz_3503_);
v_i_boxed_3507_ = lean_unbox_usize(v_i_3504_);
lean_dec(v_i_3504_);
v_res_3508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_as_3502_, v_sz_boxed_3506_, v_i_boxed_3507_, v_b_3505_);
lean_dec_ref(v_as_3502_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(lean_object* v_ctx_3509_, lean_object* v_snippet_3510_){
_start:
{
lean_object* v_text_3511_; lean_object* v_sections_3512_; lean_object* v___x_3513_; 
v_text_3511_ = lean_ctor_get(v_snippet_3510_, 0);
v_sections_3512_ = lean_ctor_get(v_snippet_3510_, 1);
v___x_3513_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_3509_, v_text_3511_);
if (lean_obj_tag(v___x_3513_) == 0)
{
return v___x_3513_;
}
else
{
lean_object* v_a_3514_; size_t v_sz_3515_; size_t v___x_3516_; lean_object* v___x_3517_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v_sz_3515_ = lean_array_size(v_sections_3512_);
v___x_3516_ = ((size_t)0ULL);
v___x_3517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_sections_3512_, v_sz_3515_, v___x_3516_, v_a_3514_);
return v___x_3517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet___boxed(lean_object* v_ctx_3518_, lean_object* v_snippet_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_ctx_3518_, v_snippet_3519_);
lean_dec_ref(v_snippet_3519_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(lean_object* v_as_3521_, size_t v_sz_3522_, size_t v_i_3523_, lean_object* v_b_3524_){
_start:
{
uint8_t v___x_3525_; 
v___x_3525_ = lean_usize_dec_lt(v_i_3523_, v_sz_3522_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; 
v___x_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3526_, 0, v_b_3524_);
return v___x_3526_;
}
else
{
lean_object* v_snd_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3549_; 
v_snd_3527_ = lean_ctor_get(v_b_3524_, 1);
v_isSharedCheck_3549_ = !lean_is_exclusive(v_b_3524_);
if (v_isSharedCheck_3549_ == 0)
{
lean_object* v_unused_3550_; 
v_unused_3550_ = lean_ctor_get(v_b_3524_, 0);
lean_dec(v_unused_3550_);
v___x_3529_ = v_b_3524_;
v_isShared_3530_ = v_isSharedCheck_3549_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_snd_3527_);
lean_dec(v_b_3524_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3549_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v_a_3531_; lean_object* v___x_3532_; 
v_a_3531_ = lean_array_uget_borrowed(v_as_3521_, v_i_3523_);
v___x_3532_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_3527_, v_a_3531_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_del_object(v___x_3529_);
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3532_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3532_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3542_; lean_object* v___x_3544_; 
v_a_3541_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v___x_3532_, 1);
v___x_3542_ = lean_box(0);
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 1, v_a_3541_);
lean_ctor_set(v___x_3529_, 0, v___x_3542_);
v___x_3544_ = v___x_3529_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3542_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_a_3541_);
v___x_3544_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
size_t v___x_3545_; size_t v___x_3546_; 
v___x_3545_ = ((size_t)1ULL);
v___x_3546_ = lean_usize_add(v_i_3523_, v___x_3545_);
v_i_3523_ = v___x_3546_;
v_b_3524_ = v___x_3544_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4___boxed(lean_object* v_as_3551_, lean_object* v_sz_3552_, lean_object* v_i_3553_, lean_object* v_b_3554_){
_start:
{
size_t v_sz_boxed_3555_; size_t v_i_boxed_3556_; lean_object* v_res_3557_; 
v_sz_boxed_3555_ = lean_unbox_usize(v_sz_3552_);
lean_dec(v_sz_3552_);
v_i_boxed_3556_ = lean_unbox_usize(v_i_3553_);
lean_dec(v_i_3553_);
v_res_3557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_3551_, v_sz_boxed_3555_, v_i_boxed_3556_, v_b_3554_);
lean_dec_ref(v_as_3551_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(lean_object* v_as_3558_, size_t v_sz_3559_, size_t v_i_3560_, lean_object* v_b_3561_){
_start:
{
uint8_t v___x_3562_; 
v___x_3562_ = lean_usize_dec_lt(v_i_3560_, v_sz_3559_);
if (v___x_3562_ == 0)
{
lean_object* v___x_3563_; 
v___x_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3563_, 0, v_b_3561_);
return v___x_3563_;
}
else
{
lean_object* v_snd_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3586_; 
v_snd_3564_ = lean_ctor_get(v_b_3561_, 1);
v_isSharedCheck_3586_ = !lean_is_exclusive(v_b_3561_);
if (v_isSharedCheck_3586_ == 0)
{
lean_object* v_unused_3587_; 
v_unused_3587_ = lean_ctor_get(v_b_3561_, 0);
lean_dec(v_unused_3587_);
v___x_3566_ = v_b_3561_;
v_isShared_3567_ = v_isSharedCheck_3586_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_snd_3564_);
lean_dec(v_b_3561_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3586_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v_a_3568_; lean_object* v___x_3569_; 
v_a_3568_ = lean_array_uget_borrowed(v_as_3558_, v_i_3560_);
v___x_3569_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_3564_, v_a_3568_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
lean_del_object(v___x_3566_);
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3569_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3569_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3579_; lean_object* v___x_3581_; 
v_a_3578_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3578_);
lean_dec_ref_known(v___x_3569_, 1);
v___x_3579_ = lean_box(0);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 1, v_a_3578_);
lean_ctor_set(v___x_3566_, 0, v___x_3579_);
v___x_3581_ = v___x_3566_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3579_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_a_3578_);
v___x_3581_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
size_t v___x_3582_; size_t v___x_3583_; lean_object* v___x_3584_; 
v___x_3582_ = ((size_t)1ULL);
v___x_3583_ = lean_usize_add(v_i_3560_, v___x_3582_);
v___x_3584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_3558_, v_sz_3559_, v___x_3583_, v___x_3581_);
return v___x_3584_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1___boxed(lean_object* v_as_3588_, lean_object* v_sz_3589_, lean_object* v_i_3590_, lean_object* v_b_3591_){
_start:
{
size_t v_sz_boxed_3592_; size_t v_i_boxed_3593_; lean_object* v_res_3594_; 
v_sz_boxed_3592_ = lean_unbox_usize(v_sz_3589_);
lean_dec(v_sz_3589_);
v_i_boxed_3593_ = lean_unbox_usize(v_i_3590_);
lean_dec(v_i_3590_);
v_res_3594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_as_3588_, v_sz_boxed_3592_, v_i_boxed_3593_, v_b_3591_);
lean_dec_ref(v_as_3588_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_3595_, size_t v_sz_3596_, size_t v_i_3597_, lean_object* v_b_3598_){
_start:
{
uint8_t v___x_3599_; 
v___x_3599_ = lean_usize_dec_lt(v_i_3597_, v_sz_3596_);
if (v___x_3599_ == 0)
{
lean_object* v___x_3600_; 
v___x_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3600_, 0, v_b_3598_);
return v___x_3600_;
}
else
{
lean_object* v_snd_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3623_; 
v_snd_3601_ = lean_ctor_get(v_b_3598_, 1);
v_isSharedCheck_3623_ = !lean_is_exclusive(v_b_3598_);
if (v_isSharedCheck_3623_ == 0)
{
lean_object* v_unused_3624_; 
v_unused_3624_ = lean_ctor_get(v_b_3598_, 0);
lean_dec(v_unused_3624_);
v___x_3603_ = v_b_3598_;
v_isShared_3604_ = v_isSharedCheck_3623_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_snd_3601_);
lean_dec(v_b_3598_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3623_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v_a_3605_; lean_object* v___x_3606_; 
v_a_3605_ = lean_array_uget_borrowed(v_as_3595_, v_i_3597_);
v___x_3606_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_3601_, v_a_3605_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_del_object(v___x_3603_);
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3606_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3606_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3616_; lean_object* v___x_3618_; 
v_a_3615_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3615_);
lean_dec_ref_known(v___x_3606_, 1);
v___x_3616_ = lean_box(0);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 1, v_a_3615_);
lean_ctor_set(v___x_3603_, 0, v___x_3616_);
v___x_3618_ = v___x_3603_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3616_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v_a_3615_);
v___x_3618_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
size_t v___x_3619_; size_t v___x_3620_; 
v___x_3619_ = ((size_t)1ULL);
v___x_3620_ = lean_usize_add(v_i_3597_, v___x_3619_);
v_i_3597_ = v___x_3620_;
v_b_3598_ = v___x_3618_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_3625_, lean_object* v_sz_3626_, lean_object* v_i_3627_, lean_object* v_b_3628_){
_start:
{
size_t v_sz_boxed_3629_; size_t v_i_boxed_3630_; lean_object* v_res_3631_; 
v_sz_boxed_3629_ = lean_unbox_usize(v_sz_3626_);
lean_dec(v_sz_3626_);
v_i_boxed_3630_ = lean_unbox_usize(v_i_3627_);
lean_dec(v_i_3627_);
v_res_3631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_3625_, v_sz_boxed_3629_, v_i_boxed_3630_, v_b_3628_);
lean_dec_ref(v_as_3625_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(lean_object* v_as_3632_, size_t v_sz_3633_, size_t v_i_3634_, lean_object* v_b_3635_){
_start:
{
uint8_t v___x_3636_; 
v___x_3636_ = lean_usize_dec_lt(v_i_3634_, v_sz_3633_);
if (v___x_3636_ == 0)
{
lean_object* v___x_3637_; 
v___x_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3637_, 0, v_b_3635_);
return v___x_3637_;
}
else
{
lean_object* v_snd_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3660_; 
v_snd_3638_ = lean_ctor_get(v_b_3635_, 1);
v_isSharedCheck_3660_ = !lean_is_exclusive(v_b_3635_);
if (v_isSharedCheck_3660_ == 0)
{
lean_object* v_unused_3661_; 
v_unused_3661_ = lean_ctor_get(v_b_3635_, 0);
lean_dec(v_unused_3661_);
v___x_3640_ = v_b_3635_;
v_isShared_3641_ = v_isSharedCheck_3660_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_snd_3638_);
lean_dec(v_b_3635_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3660_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v_a_3642_; lean_object* v___x_3643_; 
v_a_3642_ = lean_array_uget_borrowed(v_as_3632_, v_i_3634_);
v___x_3643_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_3638_, v_a_3642_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
lean_del_object(v___x_3640_);
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3643_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3643_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
else
{
lean_object* v_a_3652_; lean_object* v___x_3653_; lean_object* v___x_3655_; 
v_a_3652_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3652_);
lean_dec_ref_known(v___x_3643_, 1);
v___x_3653_ = lean_box(0);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 1, v_a_3652_);
lean_ctor_set(v___x_3640_, 0, v___x_3653_);
v___x_3655_ = v___x_3640_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_a_3652_);
v___x_3655_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
size_t v___x_3656_; size_t v___x_3657_; lean_object* v___x_3658_; 
v___x_3656_ = ((size_t)1ULL);
v___x_3657_ = lean_usize_add(v_i_3634_, v___x_3656_);
v___x_3658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_3632_, v_sz_3633_, v___x_3657_, v___x_3655_);
return v___x_3658_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3662_, lean_object* v_sz_3663_, lean_object* v_i_3664_, lean_object* v_b_3665_){
_start:
{
size_t v_sz_boxed_3666_; size_t v_i_boxed_3667_; lean_object* v_res_3668_; 
v_sz_boxed_3666_ = lean_unbox_usize(v_sz_3663_);
lean_dec(v_sz_3663_);
v_i_boxed_3667_ = lean_unbox_usize(v_i_3664_);
lean_dec(v_i_3664_);
v_res_3668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_as_3662_, v_sz_boxed_3666_, v_i_boxed_3667_, v_b_3665_);
lean_dec_ref(v_as_3662_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(lean_object* v_init_3669_, lean_object* v_n_3670_, lean_object* v_b_3671_){
_start:
{
if (lean_obj_tag(v_n_3670_) == 0)
{
lean_object* v_cs_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; size_t v_sz_3675_; size_t v___x_3676_; lean_object* v___x_3677_; 
v_cs_3672_ = lean_ctor_get(v_n_3670_, 0);
v___x_3673_ = lean_box(0);
v___x_3674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3673_);
lean_ctor_set(v___x_3674_, 1, v_b_3671_);
v_sz_3675_ = lean_array_size(v_cs_3672_);
v___x_3676_ = ((size_t)0ULL);
v___x_3677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_init_3669_, v_cs_3672_, v_sz_3675_, v___x_3676_, v___x_3674_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3677_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3677_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3700_; 
v_a_3686_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3688_ = v___x_3677_;
v_isShared_3689_ = v_isSharedCheck_3700_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3677_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3700_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v_fst_3690_; 
v_fst_3690_ = lean_ctor_get(v_a_3686_, 0);
if (lean_obj_tag(v_fst_3690_) == 0)
{
lean_object* v_snd_3691_; lean_object* v___x_3692_; lean_object* v___x_3694_; 
v_snd_3691_ = lean_ctor_get(v_a_3686_, 1);
lean_inc(v_snd_3691_);
lean_dec(v_a_3686_);
v___x_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3692_, 0, v_snd_3691_);
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 0, v___x_3692_);
v___x_3694_ = v___x_3688_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3692_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
else
{
lean_object* v_val_3696_; lean_object* v___x_3698_; 
lean_inc_ref(v_fst_3690_);
lean_dec(v_a_3686_);
v_val_3696_ = lean_ctor_get(v_fst_3690_, 0);
lean_inc(v_val_3696_);
lean_dec_ref_known(v_fst_3690_, 1);
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 0, v_val_3696_);
v___x_3698_ = v___x_3688_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_val_3696_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
}
else
{
lean_object* v_vs_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; size_t v_sz_3704_; size_t v___x_3705_; lean_object* v___x_3706_; 
v_vs_3701_ = lean_ctor_get(v_n_3670_, 0);
v___x_3702_ = lean_box(0);
v___x_3703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3702_);
lean_ctor_set(v___x_3703_, 1, v_b_3671_);
v_sz_3704_ = lean_array_size(v_vs_3701_);
v___x_3705_ = ((size_t)0ULL);
v___x_3706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_vs_3701_, v_sz_3704_, v___x_3705_, v___x_3703_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3714_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3709_ = v___x_3706_;
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3706_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3712_; 
if (v_isShared_3710_ == 0)
{
v___x_3712_ = v___x_3709_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3707_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
else
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3729_; 
v_a_3715_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3717_ = v___x_3706_;
v_isShared_3718_ = v_isSharedCheck_3729_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3706_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3729_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v_fst_3719_; 
v_fst_3719_ = lean_ctor_get(v_a_3715_, 0);
if (lean_obj_tag(v_fst_3719_) == 0)
{
lean_object* v_snd_3720_; lean_object* v___x_3721_; lean_object* v___x_3723_; 
v_snd_3720_ = lean_ctor_get(v_a_3715_, 1);
lean_inc(v_snd_3720_);
lean_dec(v_a_3715_);
v___x_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3721_, 0, v_snd_3720_);
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v___x_3721_);
v___x_3723_ = v___x_3717_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3721_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
else
{
lean_object* v_val_3725_; lean_object* v___x_3727_; 
lean_inc_ref(v_fst_3719_);
lean_dec(v_a_3715_);
v_val_3725_ = lean_ctor_get(v_fst_3719_, 0);
lean_inc(v_val_3725_);
lean_dec_ref_known(v_fst_3719_, 1);
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v_val_3725_);
v___x_3727_ = v___x_3717_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_val_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(lean_object* v_init_3730_, lean_object* v_as_3731_, size_t v_sz_3732_, size_t v_i_3733_, lean_object* v_b_3734_){
_start:
{
uint8_t v___x_3735_; 
v___x_3735_ = lean_usize_dec_lt(v_i_3733_, v_sz_3732_);
if (v___x_3735_ == 0)
{
lean_object* v___x_3736_; 
v___x_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3736_, 0, v_b_3734_);
return v___x_3736_;
}
else
{
lean_object* v_snd_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3771_; 
v_snd_3737_ = lean_ctor_get(v_b_3734_, 1);
v_isSharedCheck_3771_ = !lean_is_exclusive(v_b_3734_);
if (v_isSharedCheck_3771_ == 0)
{
lean_object* v_unused_3772_; 
v_unused_3772_ = lean_ctor_get(v_b_3734_, 0);
lean_dec(v_unused_3772_);
v___x_3739_ = v_b_3734_;
v_isShared_3740_ = v_isSharedCheck_3771_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_snd_3737_);
lean_dec(v_b_3734_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3771_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v_a_3741_; lean_object* v___x_3742_; 
v_a_3741_ = lean_array_uget_borrowed(v_as_3731_, v_i_3733_);
lean_inc(v_snd_3737_);
v___x_3742_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_3730_, v_a_3741_, v_snd_3737_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_del_object(v___x_3739_);
lean_dec(v_snd_3737_);
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3742_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3742_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
else
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3770_; 
v_a_3751_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3753_ = v___x_3742_;
v_isShared_3754_ = v_isSharedCheck_3770_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3742_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3770_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
if (lean_obj_tag(v_a_3751_) == 0)
{
lean_object* v___x_3755_; lean_object* v___x_3757_; 
v___x_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3755_, 0, v_a_3751_);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v___x_3755_);
v___x_3757_ = v___x_3739_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3755_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_snd_3737_);
v___x_3757_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
lean_object* v___x_3759_; 
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 0, v___x_3757_);
v___x_3759_ = v___x_3753_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3763_; lean_object* v___x_3765_; 
lean_del_object(v___x_3753_);
lean_dec(v_snd_3737_);
v_a_3762_ = lean_ctor_get(v_a_3751_, 0);
lean_inc(v_a_3762_);
lean_dec_ref_known(v_a_3751_, 1);
v___x_3763_ = lean_box(0);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 1, v_a_3762_);
lean_ctor_set(v___x_3739_, 0, v___x_3763_);
v___x_3765_ = v___x_3739_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3763_);
lean_ctor_set(v_reuseFailAlloc_3769_, 1, v_a_3762_);
v___x_3765_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
size_t v___x_3766_; size_t v___x_3767_; 
v___x_3766_ = ((size_t)1ULL);
v___x_3767_ = lean_usize_add(v_i_3733_, v___x_3766_);
v_i_3733_ = v___x_3767_;
v_b_3734_ = v___x_3765_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3773_, lean_object* v_as_3774_, lean_object* v_sz_3775_, lean_object* v_i_3776_, lean_object* v_b_3777_){
_start:
{
size_t v_sz_boxed_3778_; size_t v_i_boxed_3779_; lean_object* v_res_3780_; 
v_sz_boxed_3778_ = lean_unbox_usize(v_sz_3775_);
lean_dec(v_sz_3775_);
v_i_boxed_3779_ = lean_unbox_usize(v_i_3776_);
lean_dec(v_i_3776_);
v_res_3780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_init_3773_, v_as_3774_, v_sz_boxed_3778_, v_i_boxed_3779_, v_b_3777_);
lean_dec_ref(v_as_3774_);
lean_dec_ref(v_init_3773_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0___boxed(lean_object* v_init_3781_, lean_object* v_n_3782_, lean_object* v_b_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_3781_, v_n_3782_, v_b_3783_);
lean_dec_ref(v_n_3782_);
lean_dec_ref(v_init_3781_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(lean_object* v_t_3785_, lean_object* v_init_3786_){
_start:
{
lean_object* v_root_3787_; lean_object* v_tail_3788_; lean_object* v___x_3789_; 
v_root_3787_ = lean_ctor_get(v_t_3785_, 0);
v_tail_3788_ = lean_ctor_get(v_t_3785_, 1);
lean_inc_ref(v_init_3786_);
v___x_3789_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_3786_, v_root_3787_, v_init_3786_);
lean_dec_ref(v_init_3786_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v___x_3789_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3789_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3790_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3834_; 
v_a_3798_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3800_ = v___x_3789_;
v_isShared_3801_ = v_isSharedCheck_3834_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3789_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3834_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
if (lean_obj_tag(v_a_3798_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3804_; 
v_a_3802_ = lean_ctor_get(v_a_3798_, 0);
lean_inc(v_a_3802_);
lean_dec_ref_known(v_a_3798_, 1);
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 0, v_a_3802_);
v___x_3804_ = v___x_3800_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3802_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; size_t v_sz_3809_; size_t v___x_3810_; lean_object* v___x_3811_; 
lean_del_object(v___x_3800_);
v_a_3806_ = lean_ctor_get(v_a_3798_, 0);
lean_inc(v_a_3806_);
lean_dec_ref_known(v_a_3798_, 1);
v___x_3807_ = lean_box(0);
v___x_3808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3807_);
lean_ctor_set(v___x_3808_, 1, v_a_3806_);
v_sz_3809_ = lean_array_size(v_tail_3788_);
v___x_3810_ = ((size_t)0ULL);
v___x_3811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_tail_3788_, v_sz_3809_, v___x_3810_, v___x_3808_);
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3811_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3811_);
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
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3833_; 
v_a_3820_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3822_ = v___x_3811_;
v_isShared_3823_ = v_isSharedCheck_3833_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3811_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3833_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v_fst_3824_; 
v_fst_3824_ = lean_ctor_get(v_a_3820_, 0);
if (lean_obj_tag(v_fst_3824_) == 0)
{
lean_object* v_snd_3825_; lean_object* v___x_3827_; 
v_snd_3825_ = lean_ctor_get(v_a_3820_, 1);
lean_inc(v_snd_3825_);
lean_dec(v_a_3820_);
if (v_isShared_3823_ == 0)
{
lean_ctor_set(v___x_3822_, 0, v_snd_3825_);
v___x_3827_ = v___x_3822_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_snd_3825_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
else
{
lean_object* v_val_3829_; lean_object* v___x_3831_; 
lean_inc_ref(v_fst_3824_);
lean_dec(v_a_3820_);
v_val_3829_ = lean_ctor_get(v_fst_3824_, 0);
lean_inc(v_val_3829_);
lean_dec_ref_known(v_fst_3824_, 1);
if (v_isShared_3823_ == 0)
{
lean_ctor_set(v___x_3822_, 0, v_val_3829_);
v___x_3831_ = v___x_3822_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_val_3829_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0___boxed(lean_object* v_t_3835_, lean_object* v_init_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(v_t_3835_, v_init_3836_);
lean_dec_ref(v_t_3835_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble(lean_object* v_docs_3840_){
_start:
{
lean_object* v_ctx_3841_; lean_object* v___x_3842_; 
v_ctx_3841_ = ((lean_object*)(l_Lean_VersoModuleDocs_assemble___closed__0));
v___x_3842_ = l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(v_docs_3840_, v_ctx_3841_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3842_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3842_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
else
{
lean_object* v_a_3851_; lean_object* v___x_3852_; 
v_a_3851_ = lean_ctor_get(v___x_3842_, 0);
lean_inc(v_a_3851_);
lean_dec_ref_known(v___x_3842_, 1);
v___x_3852_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(v_a_3851_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3852_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3852_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
else
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3871_; 
v_a_3861_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3863_ = v___x_3852_;
v_isShared_3864_ = v_isSharedCheck_3871_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3852_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3871_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v_content_3865_; lean_object* v_priorParts_3866_; lean_object* v___x_3867_; lean_object* v___x_3869_; 
v_content_3865_ = lean_ctor_get(v_a_3861_, 0);
lean_inc_ref(v_content_3865_);
v_priorParts_3866_ = lean_ctor_get(v_a_3861_, 1);
lean_inc_ref(v_priorParts_3866_);
lean_dec(v_a_3861_);
v___x_3867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3867_, 0, v_content_3865_);
lean_ctor_set(v___x_3867_, 1, v_priorParts_3866_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3867_);
v___x_3869_ = v___x_3863_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v___x_3867_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble___boxed(lean_object* v_docs_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Lean_VersoModuleDocs_assemble(v_docs_3872_);
lean_dec_ref(v_docs_3872_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v_es_3874_){
_start:
{
lean_object* v___x_3875_; 
v___x_3875_ = lean_array_mk(v_es_3874_);
return v___x_3875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v_x_3878_, lean_object* v_x_3879_, lean_object* v_es_3880_){
_start:
{
lean_object* v_ents_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v_ents_3881_ = lean_array_mk(v_es_3880_);
v___x_3882_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_));
lean_inc_ref(v_ents_3881_);
v___x_3883_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
lean_ctor_set(v___x_3883_, 1, v_ents_3881_);
lean_ctor_set(v___x_3883_, 2, v_ents_3881_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v_x_3884_, lean_object* v_x_3885_, lean_object* v_es_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(v_x_3884_, v_x_3885_, v_es_3886_);
lean_dec_ref(v_x_3885_);
lean_dec_ref(v_x_3884_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v___x_3888_, lean_object* v_x_3889_){
_start:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; size_t v___x_3893_; lean_object* v___x_3894_; 
v___x_3890_ = lean_unsigned_to_nat(32u);
v___x_3891_ = lean_mk_empty_array_with_capacity(v___x_3890_);
v___x_3892_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_3893_ = ((size_t)5ULL);
lean_inc(v___x_3888_);
v___x_3894_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3894_, 0, v___x_3892_);
lean_ctor_set(v___x_3894_, 1, v___x_3891_);
lean_ctor_set(v___x_3894_, 2, v___x_3888_);
lean_ctor_set(v___x_3894_, 3, v___x_3888_);
lean_ctor_set_usize(v___x_3894_, 4, v___x_3893_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v___x_3895_, lean_object* v_x_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(v___x_3895_, v_x_3896_);
lean_dec_ref(v_x_3896_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3919_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_));
v___x_3920_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_3919_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v_a_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_();
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainVersoModuleDocs(lean_object* v_env_3923_){
_start:
{
lean_object* v___x_3924_; lean_object* v_toEnvExtension_3925_; lean_object* v_asyncMode_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3924_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_3925_ = lean_ctor_get(v___x_3924_, 0);
v_asyncMode_3926_ = lean_ctor_get(v_toEnvExtension_3925_, 2);
v___x_3927_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_3928_ = lean_box(0);
v___x_3929_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3927_, v___x_3924_, v_env_3923_, v_asyncMode_3926_, v___x_3928_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDocs(lean_object* v_env_3930_){
_start:
{
lean_object* v___x_3931_; 
v___x_3931_ = l_Lean_getMainVersoModuleDocs(v_env_3930_);
return v___x_3931_;
}
}
static lean_object* _init_l_Lean_getVersoModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3932_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_3933_ = lean_box(0);
v___x_3934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
lean_ctor_set(v___x_3934_, 1, v___x_3932_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f(lean_object* v_env_3935_, lean_object* v_moduleName_3936_){
_start:
{
lean_object* v___x_3937_; 
v___x_3937_ = l_Lean_Environment_getModuleIdx_x3f(v_env_3935_, v_moduleName_3936_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v___x_3938_; 
v___x_3938_ = lean_box(0);
return v___x_3938_;
}
else
{
lean_object* v_val_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3950_; 
v_val_3939_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3941_ = v___x_3937_;
v_isShared_3942_ = v_isSharedCheck_3950_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_val_3939_);
lean_dec(v___x_3937_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3950_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; uint8_t v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3948_; 
v___x_3943_ = lean_obj_once(&l_Lean_getVersoModuleDoc_x3f___closed__0, &l_Lean_getVersoModuleDoc_x3f___closed__0_once, _init_l_Lean_getVersoModuleDoc_x3f___closed__0);
v___x_3944_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v___x_3945_ = 1;
v___x_3946_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3943_, v___x_3944_, v_env_3935_, v_val_3939_, v___x_3945_);
lean_dec(v_val_3939_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 0, v___x_3946_);
v___x_3948_ = v___x_3941_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3946_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f___boxed(lean_object* v_env_3951_, lean_object* v_moduleName_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l_Lean_getVersoModuleDoc_x3f(v_env_3951_, v_moduleName_3952_);
lean_dec(v_moduleName_3952_);
lean_dec_ref(v_env_3951_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet___lam__0(lean_object* v___x_3954_, lean_object* v_snippet_3955_, lean_object* v_s_3956_){
_start:
{
lean_object* v_addEntryFn_3957_; lean_object* v_importedEntries_3958_; lean_object* v_state_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3967_; 
v_addEntryFn_3957_ = lean_ctor_get(v___x_3954_, 3);
lean_inc(v_addEntryFn_3957_);
lean_dec_ref(v___x_3954_);
v_importedEntries_3958_ = lean_ctor_get(v_s_3956_, 0);
v_state_3959_ = lean_ctor_get(v_s_3956_, 1);
v_isSharedCheck_3967_ = !lean_is_exclusive(v_s_3956_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3961_ = v_s_3956_;
v_isShared_3962_ = v_isSharedCheck_3967_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_state_3959_);
lean_inc(v_importedEntries_3958_);
lean_dec(v_s_3956_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3967_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v_state_3963_; lean_object* v___x_3965_; 
v_state_3963_ = lean_apply_2(v_addEntryFn_3957_, v_state_3959_, v_snippet_3955_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 1, v_state_3963_);
v___x_3965_ = v___x_3961_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_importedEntries_3958_);
lean_ctor_set(v_reuseFailAlloc_3966_, 1, v_state_3963_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet(lean_object* v_env_3970_, lean_object* v_snippet_3971_){
_start:
{
lean_object* v_docs_3972_; uint8_t v___x_3973_; 
lean_inc_ref(v_env_3970_);
v_docs_3972_ = l_Lean_getMainVersoModuleDocs(v_env_3970_);
v___x_3973_ = l_Lean_VersoModuleDocs_canAdd(v_docs_3972_, v_snippet_3971_);
if (v___x_3973_ == 0)
{
lean_object* v___x_3974_; lean_object* v___y_3976_; lean_object* v___x_3981_; 
lean_dec_ref(v_snippet_3971_);
lean_dec_ref(v_env_3970_);
v___x_3974_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__0));
v___x_3981_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_3972_);
lean_dec_ref(v_docs_3972_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v___x_3982_; 
v___x_3982_ = ((lean_object*)(l_Lean_throwIfHasDocString___redArg___closed__0));
v___y_3976_ = v___x_3982_;
goto v___jp_3975_;
}
else
{
lean_object* v_val_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v_val_3983_ = lean_ctor_get(v___x_3981_, 0);
lean_inc(v_val_3983_);
lean_dec_ref_known(v___x_3981_, 1);
v___x_3984_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__1));
v___x_3985_ = l_Nat_reprFast(v_val_3983_);
v___x_3986_ = lean_string_append(v___x_3984_, v___x_3985_);
lean_dec_ref(v___x_3985_);
v___x_3987_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1));
v___x_3988_ = lean_string_append(v___x_3986_, v___x_3987_);
v___y_3976_ = v___x_3988_;
goto v___jp_3975_;
}
v___jp_3975_:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3977_ = lean_string_append(v___x_3974_, v___y_3976_);
lean_dec_ref(v___y_3976_);
v___x_3978_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1));
v___x_3979_ = lean_string_append(v___x_3977_, v___x_3978_);
v___x_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3979_);
return v___x_3980_;
}
}
else
{
lean_object* v___x_3989_; lean_object* v_toEnvExtension_3990_; lean_object* v_asyncMode_3991_; uint8_t v_logWrites_3992_; lean_object* v___f_3993_; lean_object* v___x_3994_; 
lean_dec_ref(v_docs_3972_);
v___x_3989_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_3990_ = lean_ctor_get(v___x_3989_, 0);
v_asyncMode_3991_ = lean_ctor_get(v_toEnvExtension_3990_, 2);
v_logWrites_3992_ = lean_ctor_get_uint8(v_toEnvExtension_3990_, sizeof(void*)*6);
v___f_3993_ = lean_alloc_closure((void*)(l_Lean_addVersoModuleDocSnippet___lam__0), 3, 2);
lean_closure_set(v___f_3993_, 0, v___x_3989_);
lean_closure_set(v___f_3993_, 1, v_snippet_3971_);
v___x_3994_ = lean_box(0);
if (v_logWrites_3992_ == 0)
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
lean_inc_ref(v_toEnvExtension_3990_);
v___x_3995_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3990_, v_env_3970_, v___f_3993_, v_asyncMode_3991_, v___x_3994_, v___x_3973_);
v___x_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3995_);
return v___x_3996_;
}
else
{
lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
lean_inc_ref_n(v_toEnvExtension_3990_, 2);
v___x_3997_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3990_, v_env_3970_);
lean_dec_ref(v_env_3970_);
v___x_3998_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3990_, v___x_3997_, v___f_3993_, v_asyncMode_3991_, v___x_3994_, v___x_3973_);
v___x_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3998_);
return v___x_3999_;
}
}
}
}
lean_object* runtime_initialize_Lean_DeclarationRange(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_DeferredCheck(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Extra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Length(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrivateName(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Extension(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_DeferredCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Extra(builtin);
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
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrivateName(builtin);
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
lean_object* initialize_Lean_DocString_Types(uint8_t builtin);
lean_object* initialize_Lean_DocString_DeferredCheck(uint8_t builtin);
lean_object* initialize_Init_Data_String_Extra(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Length(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Lean_PrivateName(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Extension(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_DeferredCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Extra(builtin);
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
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrivateName(builtin);
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
