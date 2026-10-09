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
lean_object* l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(lean_object* v_name_209_, lean_object* v_decl_210_, lean_object* v_ref_211_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_209_ = stack[0].m_obj;
lean_object* v_decl_210_ = stack[1].m_obj;
lean_object* v_ref_211_ = stack[2].m_obj;
lean_object* v_res_237_;
v_res_237_ = l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v_name_209_, v_decl_210_, v_ref_211_);
stack->m_obj
 = v_res_237_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_238_, lean_object* v_decl_239_, lean_object* v_ref_240_, lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v_name_238_, v_decl_239_, v_ref_240_);
lean_dec_ref(v_decl_239_);
return v_res_242_;
}
}
lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_260_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_261_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_262_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__6_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_263_ = l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v___x_260_, v___x_261_, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_264_;
v_res_264_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_();
stack->m_obj
 = v_res_264_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4____boxed(lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_();
return v_res_266_;
}
}
lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_284_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__1_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_285_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_286_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__4_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_));
v___x_287_ = l_Lean_Option_register___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4__spec__0(v___x_284_, v___x_285_, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_288_;
v_res_288_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_();
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4____boxed(lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2096677768____hygCtx___hyg_4_();
return v_res_290_;
}
}
lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_box(1);
v___x_293_ = lean_st_mk_ref(v___x_292_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_295_;
v_res_295_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_();
stack->m_obj
 = v_res_295_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2____boxed(lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1174734686____hygCtx___hyg_2_();
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_298_, lean_object* v_x_299_){
_start:
{
if (lean_obj_tag(v_x_299_) == 0)
{
lean_object* v_k_300_; lean_object* v_v_301_; lean_object* v_l_302_; lean_object* v_r_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v_k_300_ = lean_ctor_get(v_x_299_, 1);
v_v_301_ = lean_ctor_get(v_x_299_, 2);
v_l_302_ = lean_ctor_get(v_x_299_, 3);
v_r_303_ = lean_ctor_get(v_x_299_, 4);
v___x_304_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_298_, v_l_302_);
lean_inc(v_v_301_);
lean_inc(v_k_300_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v_k_300_);
lean_ctor_set(v___x_305_, 1, v_v_301_);
v___x_306_ = lean_array_push(v___x_304_, v___x_305_);
v_init_298_ = v___x_306_;
v_x_299_ = v_r_303_;
goto _start;
}
else
{
return v_init_298_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_308_, lean_object* v_x_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_308_, v_x_309_);
lean_dec(v_x_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(lean_object* v_x_315_, lean_object* v_s_316_){
_start:
{
lean_object* v___x_317_; lean_object* v_ents_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_317_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v_ents_318_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v___x_317_, v_s_316_);
v___x_319_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
lean_inc_ref(v_ents_318_);
v___x_320_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_ents_318_);
lean_ctor_set(v___x_320_, 2, v_ents_318_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object* v_x_321_, lean_object* v_s_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(v_x_321_, v_s_322_);
lean_dec(v_s_322_);
lean_dec_ref(v_x_321_);
return v_res_323_;
}
}
lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; lean_object* v___x_336_; 
v___f_332_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_333_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_334_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_335_ = 0;
v___x_336_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_333_, v___x_334_, v___x_335_, v___f_332_);
return v___x_336_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_337_;
v_res_337_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_();
stack->m_obj
 = v_res_337_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2____boxed(lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_();
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0(lean_object* v_init_340_, lean_object* v_t_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0_spec__0(v_init_340_, v_t_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_343_, lean_object* v_t_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2__spec__0(v_init_343_, v_t_344_);
lean_dec(v_t_344_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_346_, lean_object* v_x_347_){
_start:
{
if (lean_obj_tag(v_x_347_) == 0)
{
lean_object* v_k_348_; lean_object* v_v_349_; lean_object* v_l_350_; lean_object* v_r_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_k_348_ = lean_ctor_get(v_x_347_, 1);
v_v_349_ = lean_ctor_get(v_x_347_, 2);
v_l_350_ = lean_ctor_get(v_x_347_, 3);
v_r_351_ = lean_ctor_get(v_x_347_, 4);
v___x_352_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_346_, v_l_350_);
lean_inc(v_v_349_);
lean_inc(v_k_348_);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v_k_348_);
lean_ctor_set(v___x_353_, 1, v_v_349_);
v___x_354_ = lean_array_push(v___x_352_, v___x_353_);
v_init_346_ = v___x_354_;
v_x_347_ = v_r_351_;
goto _start;
}
else
{
return v_init_346_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_356_, lean_object* v_x_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_356_, v_x_357_);
lean_dec(v_x_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(lean_object* v_x_363_, lean_object* v_s_364_){
_start:
{
lean_object* v___x_365_; lean_object* v_ents_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_365_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v_ents_366_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v___x_365_, v_s_364_);
v___x_367_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
lean_inc_ref(v_ents_366_);
v___x_368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v_ents_366_);
lean_ctor_set(v___x_368_, 2, v_ents_366_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed(lean_object* v_x_369_, lean_object* v_s_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(v_x_369_, v_s_370_);
lean_dec(v_s_370_);
lean_dec_ref(v_x_369_);
return v_res_371_;
}
}
lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_401_; lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; lean_object* v___x_405_; 
v___f_401_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_402_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__11_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_403_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__12_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_));
v___x_404_ = 0;
v___x_405_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_402_, v___x_403_, v___x_404_, v___f_401_);
return v___x_405_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_406_;
v_res_406_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_();
stack->m_obj
 = v_res_406_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2____boxed(lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2_();
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0(lean_object* v_init_409_, lean_object* v_t_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0_spec__0(v_init_409_, v_t_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_412_, lean_object* v_t_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2763720193____hygCtx___hyg_2__spec__0(v_init_412_, v_t_413_);
lean_dec(v_t_413_);
return v_res_414_;
}
}
lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_box(1);
v___x_417_ = lean_st_mk_ref(v___x_416_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_419_;
v_res_419_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
stack->m_obj
 = v_res_419_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2____boxed(lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_797151674____hygCtx___hyg_2_();
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_422_, lean_object* v_x_423_){
_start:
{
if (lean_obj_tag(v_x_423_) == 0)
{
lean_object* v_k_424_; lean_object* v_v_425_; lean_object* v_l_426_; lean_object* v_r_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_k_424_ = lean_ctor_get(v_x_423_, 1);
v_v_425_ = lean_ctor_get(v_x_423_, 2);
v_l_426_ = lean_ctor_get(v_x_423_, 3);
v_r_427_ = lean_ctor_get(v_x_423_, 4);
v___x_428_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_422_, v_l_426_);
lean_inc(v_v_425_);
lean_inc(v_k_424_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v_k_424_);
lean_ctor_set(v___x_429_, 1, v_v_425_);
v___x_430_ = lean_array_push(v___x_428_, v___x_429_);
v_init_422_ = v___x_430_;
v_x_423_ = v_r_427_;
goto _start;
}
else
{
return v_init_422_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_432_, lean_object* v_x_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_432_, v_x_433_);
lean_dec(v_x_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(lean_object* v_x_439_, lean_object* v_s_440_){
_start:
{
lean_object* v___x_441_; lean_object* v_ents_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_441_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v_ents_442_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v___x_441_, v_s_440_);
v___x_443_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
lean_inc_ref(v_ents_442_);
v___x_444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v_ents_442_);
lean_ctor_set(v___x_444_, 2, v_ents_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object* v_x_445_, lean_object* v_s_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(v_x_445_, v_s_446_);
lean_dec(v_s_446_);
lean_dec_ref(v_x_445_);
return v_res_447_;
}
}
lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; 
v___f_454_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__0_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v___x_455_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__2_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_));
v___x_456_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__3_00___x40_Lean_DocString_Extension_101684723____hygCtx___hyg_2_));
v___x_457_ = 0;
v___x_458_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_455_, v___x_456_, v___x_457_, v___f_454_);
return v___x_458_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_459_;
v_res_459_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_();
stack->m_obj
 = v_res_459_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2____boxed(lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2_();
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0(lean_object* v_init_462_, lean_object* v_t_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0_spec__0(v_init_462_, v_t_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_465_, lean_object* v_t_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_2538023809____hygCtx___hyg_2__spec__0(v_init_465_, v_t_466_);
lean_dec(v_t_466_);
return v_res_467_;
}
}
lean_object* l_Lean_addBuiltinDocString(lean_object* v_declName_468_, lean_object* v_docString_469_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_471_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_472_ = lean_st_ref_take(v___x_471_);
v___x_473_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_468_, v_docString_469_, v___x_472_);
v___x_474_ = lean_st_ref_put(v___x_471_, v___x_473_);
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT void l_Lean_addBuiltinDocString_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_468_ = stack[0].m_obj;
lean_object* v_docString_469_ = stack[1].m_obj;
lean_object* v_res_476_;
v_res_476_ = l_Lean_addBuiltinDocString(v_declName_468_, v_docString_469_);
stack->m_obj
 = v_res_476_;
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDocString___boxed(lean_object* v_declName_477_, lean_object* v_docString_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_addBuiltinDocString(v_declName_477_, v_docString_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(lean_object* v_k_481_, lean_object* v_t_482_){
_start:
{
if (lean_obj_tag(v_t_482_) == 0)
{
lean_object* v_k_483_; lean_object* v_v_484_; lean_object* v_l_485_; lean_object* v_r_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_1140_; 
v_k_483_ = lean_ctor_get(v_t_482_, 1);
v_v_484_ = lean_ctor_get(v_t_482_, 2);
v_l_485_ = lean_ctor_get(v_t_482_, 3);
v_r_486_ = lean_ctor_get(v_t_482_, 4);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_t_482_);
if (v_isSharedCheck_1140_ == 0)
{
lean_object* v_unused_1141_; 
v_unused_1141_ = lean_ctor_get(v_t_482_, 0);
lean_dec(v_unused_1141_);
v___x_488_ = v_t_482_;
v_isShared_489_ = v_isSharedCheck_1140_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_r_486_);
lean_inc(v_l_485_);
lean_inc(v_v_484_);
lean_inc(v_k_483_);
lean_dec(v_t_482_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_1140_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
uint8_t v___x_490_; 
v___x_490_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_481_, v_k_483_);
switch(v___x_490_)
{
case 0:
{
lean_object* v_impl_491_; lean_object* v___x_492_; 
v_impl_491_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_481_, v_l_485_);
v___x_492_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_491_) == 0)
{
if (lean_obj_tag(v_r_486_) == 0)
{
lean_object* v_size_493_; lean_object* v_size_494_; lean_object* v_k_495_; lean_object* v_v_496_; lean_object* v_l_497_; lean_object* v_r_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_size_493_ = lean_ctor_get(v_impl_491_, 0);
v_size_494_ = lean_ctor_get(v_r_486_, 0);
v_k_495_ = lean_ctor_get(v_r_486_, 1);
v_v_496_ = lean_ctor_get(v_r_486_, 2);
v_l_497_ = lean_ctor_get(v_r_486_, 3);
lean_inc(v_l_497_);
v_r_498_ = lean_ctor_get(v_r_486_, 4);
v___x_499_ = lean_unsigned_to_nat(3u);
v___x_500_ = lean_nat_mul(v___x_499_, v_size_493_);
v___x_501_ = lean_nat_dec_lt(v___x_500_, v_size_494_);
lean_dec(v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
lean_dec(v_l_497_);
v___x_502_ = lean_nat_add(v___x_492_, v_size_493_);
v___x_503_ = lean_nat_add(v___x_502_, v_size_494_);
lean_dec(v___x_502_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 3, v_impl_491_);
lean_ctor_set(v___x_488_, 0, v___x_503_);
v___x_505_ = v___x_488_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v_impl_491_);
lean_ctor_set(v_reuseFailAlloc_506_, 4, v_r_486_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_570_; 
lean_inc(v_r_498_);
lean_inc(v_v_496_);
lean_inc(v_k_495_);
lean_inc(v_size_494_);
v_isSharedCheck_570_ = !lean_is_exclusive(v_r_486_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; lean_object* v_unused_572_; lean_object* v_unused_573_; lean_object* v_unused_574_; lean_object* v_unused_575_; 
v_unused_571_ = lean_ctor_get(v_r_486_, 4);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_r_486_, 3);
lean_dec(v_unused_572_);
v_unused_573_ = lean_ctor_get(v_r_486_, 2);
lean_dec(v_unused_573_);
v_unused_574_ = lean_ctor_get(v_r_486_, 1);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v_r_486_, 0);
lean_dec(v_unused_575_);
v___x_508_ = v_r_486_;
v_isShared_509_ = v_isSharedCheck_570_;
goto v_resetjp_507_;
}
else
{
lean_dec(v_r_486_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_570_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v_size_510_; lean_object* v_k_511_; lean_object* v_v_512_; lean_object* v_l_513_; lean_object* v_r_514_; lean_object* v_size_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v_size_510_ = lean_ctor_get(v_l_497_, 0);
v_k_511_ = lean_ctor_get(v_l_497_, 1);
v_v_512_ = lean_ctor_get(v_l_497_, 2);
v_l_513_ = lean_ctor_get(v_l_497_, 3);
v_r_514_ = lean_ctor_get(v_l_497_, 4);
v_size_515_ = lean_ctor_get(v_r_498_, 0);
v___x_516_ = lean_unsigned_to_nat(2u);
v___x_517_ = lean_nat_mul(v___x_516_, v_size_515_);
v___x_518_ = lean_nat_dec_lt(v_size_510_, v___x_517_);
lean_dec(v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_546_; 
lean_inc(v_r_514_);
lean_inc(v_l_513_);
lean_inc(v_v_512_);
lean_inc(v_k_511_);
v_isSharedCheck_546_ = !lean_is_exclusive(v_l_497_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; lean_object* v_unused_548_; lean_object* v_unused_549_; lean_object* v_unused_550_; lean_object* v_unused_551_; 
v_unused_547_ = lean_ctor_get(v_l_497_, 4);
lean_dec(v_unused_547_);
v_unused_548_ = lean_ctor_get(v_l_497_, 3);
lean_dec(v_unused_548_);
v_unused_549_ = lean_ctor_get(v_l_497_, 2);
lean_dec(v_unused_549_);
v_unused_550_ = lean_ctor_get(v_l_497_, 1);
lean_dec(v_unused_550_);
v_unused_551_ = lean_ctor_get(v_l_497_, 0);
lean_dec(v_unused_551_);
v___x_520_ = v_l_497_;
v_isShared_521_ = v_isSharedCheck_546_;
goto v_resetjp_519_;
}
else
{
lean_dec(v_l_497_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_546_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_536_; 
v___x_522_ = lean_nat_add(v___x_492_, v_size_493_);
v___x_523_ = lean_nat_add(v___x_522_, v_size_494_);
lean_dec(v_size_494_);
if (lean_obj_tag(v_l_513_) == 0)
{
lean_object* v_size_544_; 
v_size_544_ = lean_ctor_get(v_l_513_, 0);
lean_inc(v_size_544_);
v___y_536_ = v_size_544_;
goto v___jp_535_;
}
else
{
lean_object* v___x_545_; 
v___x_545_ = lean_unsigned_to_nat(0u);
v___y_536_ = v___x_545_;
goto v___jp_535_;
}
v___jp_524_:
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = lean_nat_add(v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec(v___y_526_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 4, v_r_498_);
lean_ctor_set(v___x_520_, 3, v_r_514_);
lean_ctor_set(v___x_520_, 2, v_v_496_);
lean_ctor_set(v___x_520_, 1, v_k_495_);
lean_ctor_set(v___x_520_, 0, v___x_528_);
v___x_530_ = v___x_520_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_534_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_534_, 3, v_r_514_);
lean_ctor_set(v_reuseFailAlloc_534_, 4, v_r_498_);
v___x_530_ = v_reuseFailAlloc_534_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_532_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 4, v___x_530_);
lean_ctor_set(v___x_508_, 3, v___y_525_);
lean_ctor_set(v___x_508_, 2, v_v_512_);
lean_ctor_set(v___x_508_, 1, v_k_511_);
lean_ctor_set(v___x_508_, 0, v___x_523_);
v___x_532_ = v___x_508_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_k_511_);
lean_ctor_set(v_reuseFailAlloc_533_, 2, v_v_512_);
lean_ctor_set(v_reuseFailAlloc_533_, 3, v___y_525_);
lean_ctor_set(v_reuseFailAlloc_533_, 4, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
v___jp_535_:
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = lean_nat_add(v___x_522_, v___y_536_);
lean_dec(v___y_536_);
lean_dec(v___x_522_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v_l_513_);
lean_ctor_set(v___x_488_, 3, v_impl_491_);
lean_ctor_set(v___x_488_, 0, v___x_537_);
v___x_539_ = v___x_488_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_543_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_543_, 3, v_impl_491_);
lean_ctor_set(v_reuseFailAlloc_543_, 4, v_l_513_);
v___x_539_ = v_reuseFailAlloc_543_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; 
v___x_540_ = lean_nat_add(v___x_492_, v_size_515_);
if (lean_obj_tag(v_r_514_) == 0)
{
lean_object* v_size_541_; 
v_size_541_ = lean_ctor_get(v_r_514_, 0);
lean_inc(v_size_541_);
v___y_525_ = v___x_539_;
v___y_526_ = v___x_540_;
v___y_527_ = v_size_541_;
goto v___jp_524_;
}
else
{
lean_object* v___x_542_; 
v___x_542_ = lean_unsigned_to_nat(0u);
v___y_525_ = v___x_539_;
v___y_526_ = v___x_540_;
v___y_527_ = v___x_542_;
goto v___jp_524_;
}
}
}
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
lean_del_object(v___x_488_);
v___x_552_ = lean_nat_add(v___x_492_, v_size_493_);
v___x_553_ = lean_nat_add(v___x_552_, v_size_494_);
lean_dec(v_size_494_);
v___x_554_ = lean_nat_add(v___x_552_, v_size_510_);
lean_dec(v___x_552_);
lean_inc_ref(v_impl_491_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 4, v_l_497_);
lean_ctor_set(v___x_508_, 3, v_impl_491_);
lean_ctor_set(v___x_508_, 2, v_v_484_);
lean_ctor_set(v___x_508_, 1, v_k_483_);
lean_ctor_set(v___x_508_, 0, v___x_554_);
v___x_556_ = v___x_508_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_impl_491_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v_l_497_);
v___x_556_ = v_reuseFailAlloc_569_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_isSharedCheck_563_ = !lean_is_exclusive(v_impl_491_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; lean_object* v_unused_565_; lean_object* v_unused_566_; lean_object* v_unused_567_; lean_object* v_unused_568_; 
v_unused_564_ = lean_ctor_get(v_impl_491_, 4);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v_impl_491_, 3);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_impl_491_, 2);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_impl_491_, 1);
lean_dec(v_unused_567_);
v_unused_568_ = lean_ctor_get(v_impl_491_, 0);
lean_dec(v_unused_568_);
v___x_558_ = v_impl_491_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_dec(v_impl_491_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 4, v_r_498_);
lean_ctor_set(v___x_558_, 3, v___x_556_);
lean_ctor_set(v___x_558_, 2, v_v_496_);
lean_ctor_set(v___x_558_, 1, v_k_495_);
lean_ctor_set(v___x_558_, 0, v___x_553_);
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_k_495_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_v_496_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_562_, 4, v_r_498_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
v_size_576_ = lean_ctor_get(v_impl_491_, 0);
v___x_577_ = lean_nat_add(v___x_492_, v_size_576_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 3, v_impl_491_);
lean_ctor_set(v___x_488_, 0, v___x_577_);
v___x_579_ = v___x_488_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_580_, 3, v_impl_491_);
lean_ctor_set(v_reuseFailAlloc_580_, 4, v_r_486_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
else
{
if (lean_obj_tag(v_r_486_) == 0)
{
lean_object* v_l_581_; 
v_l_581_ = lean_ctor_get(v_r_486_, 3);
lean_inc(v_l_581_);
if (lean_obj_tag(v_l_581_) == 0)
{
lean_object* v_r_582_; 
v_r_582_ = lean_ctor_get(v_r_486_, 4);
lean_inc(v_r_582_);
if (lean_obj_tag(v_r_582_) == 0)
{
lean_object* v_size_583_; lean_object* v_k_584_; lean_object* v_v_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_598_; 
v_size_583_ = lean_ctor_get(v_r_486_, 0);
v_k_584_ = lean_ctor_get(v_r_486_, 1);
v_v_585_ = lean_ctor_get(v_r_486_, 2);
v_isSharedCheck_598_ = !lean_is_exclusive(v_r_486_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; lean_object* v_unused_600_; 
v_unused_599_ = lean_ctor_get(v_r_486_, 4);
lean_dec(v_unused_599_);
v_unused_600_ = lean_ctor_get(v_r_486_, 3);
lean_dec(v_unused_600_);
v___x_587_ = v_r_486_;
v_isShared_588_ = v_isSharedCheck_598_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_v_585_);
lean_inc(v_k_584_);
lean_inc(v_size_583_);
lean_dec(v_r_486_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_598_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_size_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v_size_589_ = lean_ctor_get(v_l_581_, 0);
v___x_590_ = lean_nat_add(v___x_492_, v_size_583_);
lean_dec(v_size_583_);
v___x_591_ = lean_nat_add(v___x_492_, v_size_589_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 4, v_l_581_);
lean_ctor_set(v___x_587_, 3, v_impl_491_);
lean_ctor_set(v___x_587_, 2, v_v_484_);
lean_ctor_set(v___x_587_, 1, v_k_483_);
lean_ctor_set(v___x_587_, 0, v___x_591_);
v___x_593_ = v___x_587_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v_impl_491_);
lean_ctor_set(v_reuseFailAlloc_597_, 4, v_l_581_);
v___x_593_ = v_reuseFailAlloc_597_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_595_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v_r_582_);
lean_ctor_set(v___x_488_, 3, v___x_593_);
lean_ctor_set(v___x_488_, 2, v_v_585_);
lean_ctor_set(v___x_488_, 1, v_k_584_);
lean_ctor_set(v___x_488_, 0, v___x_590_);
v___x_595_ = v___x_488_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_596_, 3, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_596_, 4, v_r_582_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
else
{
lean_object* v_k_601_; lean_object* v_v_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_625_; 
v_k_601_ = lean_ctor_get(v_r_486_, 1);
v_v_602_ = lean_ctor_get(v_r_486_, 2);
v_isSharedCheck_625_ = !lean_is_exclusive(v_r_486_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; lean_object* v_unused_627_; lean_object* v_unused_628_; 
v_unused_626_ = lean_ctor_get(v_r_486_, 4);
lean_dec(v_unused_626_);
v_unused_627_ = lean_ctor_get(v_r_486_, 3);
lean_dec(v_unused_627_);
v_unused_628_ = lean_ctor_get(v_r_486_, 0);
lean_dec(v_unused_628_);
v___x_604_ = v_r_486_;
v_isShared_605_ = v_isSharedCheck_625_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_v_602_);
lean_inc(v_k_601_);
lean_dec(v_r_486_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_625_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v_k_606_; lean_object* v_v_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_621_; 
v_k_606_ = lean_ctor_get(v_l_581_, 1);
v_v_607_ = lean_ctor_get(v_l_581_, 2);
v_isSharedCheck_621_ = !lean_is_exclusive(v_l_581_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; lean_object* v_unused_623_; lean_object* v_unused_624_; 
v_unused_622_ = lean_ctor_get(v_l_581_, 4);
lean_dec(v_unused_622_);
v_unused_623_ = lean_ctor_get(v_l_581_, 3);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v_l_581_, 0);
lean_dec(v_unused_624_);
v___x_609_ = v_l_581_;
v_isShared_610_ = v_isSharedCheck_621_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_v_607_);
lean_inc(v_k_606_);
lean_dec(v_l_581_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_621_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_unsigned_to_nat(3u);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 4, v_r_582_);
lean_ctor_set(v___x_609_, 3, v_r_582_);
lean_ctor_set(v___x_609_, 2, v_v_484_);
lean_ctor_set(v___x_609_, 1, v_k_483_);
lean_ctor_set(v___x_609_, 0, v___x_492_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v_r_582_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v_r_582_);
v___x_613_ = v_reuseFailAlloc_620_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_615_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 3, v_r_582_);
lean_ctor_set(v___x_604_, 0, v___x_492_);
v___x_615_ = v___x_604_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_k_601_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_v_602_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v_r_582_);
lean_ctor_set(v_reuseFailAlloc_619_, 4, v_r_582_);
v___x_615_ = v_reuseFailAlloc_619_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_617_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v___x_615_);
lean_ctor_set(v___x_488_, 3, v___x_613_);
lean_ctor_set(v___x_488_, 2, v_v_607_);
lean_ctor_set(v___x_488_, 1, v_k_606_);
lean_ctor_set(v___x_488_, 0, v___x_611_);
v___x_617_ = v___x_488_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_k_606_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v_v_607_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_629_; 
v_r_629_ = lean_ctor_get(v_r_486_, 4);
lean_inc(v_r_629_);
if (lean_obj_tag(v_r_629_) == 0)
{
lean_object* v_k_630_; lean_object* v_v_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_642_; 
v_k_630_ = lean_ctor_get(v_r_486_, 1);
v_v_631_ = lean_ctor_get(v_r_486_, 2);
v_isSharedCheck_642_ = !lean_is_exclusive(v_r_486_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; lean_object* v_unused_644_; lean_object* v_unused_645_; 
v_unused_643_ = lean_ctor_get(v_r_486_, 4);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v_r_486_, 3);
lean_dec(v_unused_644_);
v_unused_645_ = lean_ctor_get(v_r_486_, 0);
lean_dec(v_unused_645_);
v___x_633_ = v_r_486_;
v_isShared_634_ = v_isSharedCheck_642_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_v_631_);
lean_inc(v_k_630_);
lean_dec(v_r_486_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_642_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_635_ = lean_unsigned_to_nat(3u);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v_l_581_);
lean_ctor_set(v___x_633_, 2, v_v_484_);
lean_ctor_set(v___x_633_, 1, v_k_483_);
lean_ctor_set(v___x_633_, 0, v___x_492_);
v___x_637_ = v___x_633_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_641_, 3, v_l_581_);
lean_ctor_set(v_reuseFailAlloc_641_, 4, v_l_581_);
v___x_637_ = v_reuseFailAlloc_641_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_639_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v_r_629_);
lean_ctor_set(v___x_488_, 3, v___x_637_);
lean_ctor_set(v___x_488_, 2, v_v_631_);
lean_ctor_set(v___x_488_, 1, v_k_630_);
lean_ctor_set(v___x_488_, 0, v___x_635_);
v___x_639_ = v___x_488_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_k_630_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v_v_631_);
lean_ctor_set(v_reuseFailAlloc_640_, 3, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_640_, 4, v_r_629_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
else
{
lean_object* v_size_646_; lean_object* v_k_647_; lean_object* v_v_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_659_; 
v_size_646_ = lean_ctor_get(v_r_486_, 0);
v_k_647_ = lean_ctor_get(v_r_486_, 1);
v_v_648_ = lean_ctor_get(v_r_486_, 2);
v_isSharedCheck_659_ = !lean_is_exclusive(v_r_486_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; lean_object* v_unused_661_; 
v_unused_660_ = lean_ctor_get(v_r_486_, 4);
lean_dec(v_unused_660_);
v_unused_661_ = lean_ctor_get(v_r_486_, 3);
lean_dec(v_unused_661_);
v___x_650_ = v_r_486_;
v_isShared_651_ = v_isSharedCheck_659_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_v_648_);
lean_inc(v_k_647_);
lean_inc(v_size_646_);
lean_dec(v_r_486_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_659_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 3, v_r_629_);
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_size_646_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_k_647_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v_v_648_);
lean_ctor_set(v_reuseFailAlloc_658_, 3, v_r_629_);
lean_ctor_set(v_reuseFailAlloc_658_, 4, v_r_629_);
v___x_653_ = v_reuseFailAlloc_658_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_654_ = lean_unsigned_to_nat(2u);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v___x_653_);
lean_ctor_set(v___x_488_, 3, v_r_629_);
lean_ctor_set(v___x_488_, 0, v___x_654_);
v___x_656_ = v___x_488_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_657_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_657_, 3, v_r_629_);
lean_ctor_set(v_reuseFailAlloc_657_, 4, v___x_653_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
}
else
{
lean_object* v___x_663_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 3, v_r_486_);
lean_ctor_set(v___x_488_, 0, v___x_492_);
v___x_663_ = v___x_488_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_664_, 3, v_r_486_);
lean_ctor_set(v_reuseFailAlloc_664_, 4, v_r_486_);
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
case 1:
{
lean_del_object(v___x_488_);
lean_dec(v_v_484_);
lean_dec(v_k_483_);
if (lean_obj_tag(v_l_485_) == 0)
{
if (lean_obj_tag(v_r_486_) == 0)
{
lean_object* v_size_665_; lean_object* v_k_666_; lean_object* v_v_667_; lean_object* v_l_668_; lean_object* v_r_669_; lean_object* v_size_670_; lean_object* v_k_671_; lean_object* v_v_672_; lean_object* v_l_673_; lean_object* v_r_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v_size_665_ = lean_ctor_get(v_l_485_, 0);
v_k_666_ = lean_ctor_get(v_l_485_, 1);
v_v_667_ = lean_ctor_get(v_l_485_, 2);
v_l_668_ = lean_ctor_get(v_l_485_, 3);
v_r_669_ = lean_ctor_get(v_l_485_, 4);
lean_inc(v_r_669_);
v_size_670_ = lean_ctor_get(v_r_486_, 0);
v_k_671_ = lean_ctor_get(v_r_486_, 1);
v_v_672_ = lean_ctor_get(v_r_486_, 2);
v_l_673_ = lean_ctor_get(v_r_486_, 3);
lean_inc(v_l_673_);
v_r_674_ = lean_ctor_get(v_r_486_, 4);
v___x_675_ = lean_unsigned_to_nat(1u);
v___x_676_ = lean_nat_dec_lt(v_size_665_, v_size_670_);
if (v___x_676_ == 0)
{
lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_812_; 
lean_inc(v_l_668_);
lean_inc(v_v_667_);
lean_inc(v_k_666_);
v_isSharedCheck_812_ = !lean_is_exclusive(v_l_485_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; lean_object* v_unused_814_; lean_object* v_unused_815_; lean_object* v_unused_816_; lean_object* v_unused_817_; 
v_unused_813_ = lean_ctor_get(v_l_485_, 4);
lean_dec(v_unused_813_);
v_unused_814_ = lean_ctor_get(v_l_485_, 3);
lean_dec(v_unused_814_);
v_unused_815_ = lean_ctor_get(v_l_485_, 2);
lean_dec(v_unused_815_);
v_unused_816_ = lean_ctor_get(v_l_485_, 1);
lean_dec(v_unused_816_);
v_unused_817_ = lean_ctor_get(v_l_485_, 0);
lean_dec(v_unused_817_);
v___x_678_ = v_l_485_;
v_isShared_679_ = v_isSharedCheck_812_;
goto v_resetjp_677_;
}
else
{
lean_dec(v_l_485_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_812_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v_tree_681_; 
v___x_680_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_666_, v_v_667_, v_l_668_, v_r_669_);
v_tree_681_ = lean_ctor_get(v___x_680_, 2);
if (lean_obj_tag(v_tree_681_) == 0)
{
lean_object* v_k_682_; lean_object* v_v_683_; lean_object* v_size_684_; lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
lean_inc_ref(v_tree_681_);
v_k_682_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_k_682_);
v_v_683_ = lean_ctor_get(v___x_680_, 1);
lean_inc(v_v_683_);
lean_dec_ref(v___x_680_);
v_size_684_ = lean_ctor_get(v_tree_681_, 0);
v___x_685_ = lean_unsigned_to_nat(3u);
v___x_686_ = lean_nat_mul(v___x_685_, v_size_684_);
v___x_687_ = lean_nat_dec_lt(v___x_686_, v_size_670_);
lean_dec(v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
lean_dec(v_l_673_);
v___x_688_ = lean_nat_add(v___x_675_, v_size_684_);
v___x_689_ = lean_nat_add(v___x_688_, v_size_670_);
lean_dec(v___x_688_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 4, v_r_486_);
lean_ctor_set(v___x_678_, 3, v_tree_681_);
lean_ctor_set(v___x_678_, 2, v_v_683_);
lean_ctor_set(v___x_678_, 1, v_k_682_);
lean_ctor_set(v___x_678_, 0, v___x_689_);
v___x_691_ = v___x_678_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_k_682_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_v_683_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_tree_681_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_r_486_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
else
{
lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_747_; 
lean_inc(v_r_674_);
lean_inc(v_v_672_);
lean_inc(v_k_671_);
lean_inc(v_size_670_);
v_isSharedCheck_747_ = !lean_is_exclusive(v_r_486_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; lean_object* v_unused_749_; lean_object* v_unused_750_; lean_object* v_unused_751_; lean_object* v_unused_752_; 
v_unused_748_ = lean_ctor_get(v_r_486_, 4);
lean_dec(v_unused_748_);
v_unused_749_ = lean_ctor_get(v_r_486_, 3);
lean_dec(v_unused_749_);
v_unused_750_ = lean_ctor_get(v_r_486_, 2);
lean_dec(v_unused_750_);
v_unused_751_ = lean_ctor_get(v_r_486_, 1);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_r_486_, 0);
lean_dec(v_unused_752_);
v___x_694_ = v_r_486_;
v_isShared_695_ = v_isSharedCheck_747_;
goto v_resetjp_693_;
}
else
{
lean_dec(v_r_486_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_747_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_size_696_; lean_object* v_k_697_; lean_object* v_v_698_; lean_object* v_l_699_; lean_object* v_r_700_; lean_object* v_size_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v_size_696_ = lean_ctor_get(v_l_673_, 0);
v_k_697_ = lean_ctor_get(v_l_673_, 1);
v_v_698_ = lean_ctor_get(v_l_673_, 2);
v_l_699_ = lean_ctor_get(v_l_673_, 3);
v_r_700_ = lean_ctor_get(v_l_673_, 4);
v_size_701_ = lean_ctor_get(v_r_674_, 0);
v___x_702_ = lean_unsigned_to_nat(2u);
v___x_703_ = lean_nat_mul(v___x_702_, v_size_701_);
v___x_704_ = lean_nat_dec_lt(v_size_696_, v___x_703_);
lean_dec(v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_732_; 
lean_inc(v_r_700_);
lean_inc(v_l_699_);
lean_inc(v_v_698_);
lean_inc(v_k_697_);
v_isSharedCheck_732_ = !lean_is_exclusive(v_l_673_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; lean_object* v_unused_734_; lean_object* v_unused_735_; lean_object* v_unused_736_; lean_object* v_unused_737_; 
v_unused_733_ = lean_ctor_get(v_l_673_, 4);
lean_dec(v_unused_733_);
v_unused_734_ = lean_ctor_get(v_l_673_, 3);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_l_673_, 2);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_l_673_, 1);
lean_dec(v_unused_736_);
v_unused_737_ = lean_ctor_get(v_l_673_, 0);
lean_dec(v_unused_737_);
v___x_706_ = v_l_673_;
v_isShared_707_ = v_isSharedCheck_732_;
goto v_resetjp_705_;
}
else
{
lean_dec(v_l_673_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_732_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_722_; 
v___x_708_ = lean_nat_add(v___x_675_, v_size_684_);
v___x_709_ = lean_nat_add(v___x_708_, v_size_670_);
lean_dec(v_size_670_);
if (lean_obj_tag(v_l_699_) == 0)
{
lean_object* v_size_730_; 
v_size_730_ = lean_ctor_get(v_l_699_, 0);
lean_inc(v_size_730_);
v___y_722_ = v_size_730_;
goto v___jp_721_;
}
else
{
lean_object* v___x_731_; 
v___x_731_ = lean_unsigned_to_nat(0u);
v___y_722_ = v___x_731_;
goto v___jp_721_;
}
v___jp_710_:
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = lean_nat_add(v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec(v___y_712_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 4, v_r_674_);
lean_ctor_set(v___x_706_, 3, v_r_700_);
lean_ctor_set(v___x_706_, 2, v_v_672_);
lean_ctor_set(v___x_706_, 1, v_k_671_);
lean_ctor_set(v___x_706_, 0, v___x_714_);
v___x_716_ = v___x_706_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_k_671_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_v_672_);
lean_ctor_set(v_reuseFailAlloc_720_, 3, v_r_700_);
lean_ctor_set(v_reuseFailAlloc_720_, 4, v_r_674_);
v___x_716_ = v_reuseFailAlloc_720_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 4, v___x_716_);
lean_ctor_set(v___x_694_, 3, v___y_711_);
lean_ctor_set(v___x_694_, 2, v_v_698_);
lean_ctor_set(v___x_694_, 1, v_k_697_);
lean_ctor_set(v___x_694_, 0, v___x_709_);
v___x_718_ = v___x_694_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_k_697_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_v_698_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v___y_711_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
v___jp_721_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_723_ = lean_nat_add(v___x_708_, v___y_722_);
lean_dec(v___y_722_);
lean_dec(v___x_708_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 4, v_l_699_);
lean_ctor_set(v___x_678_, 3, v_tree_681_);
lean_ctor_set(v___x_678_, 2, v_v_683_);
lean_ctor_set(v___x_678_, 1, v_k_682_);
lean_ctor_set(v___x_678_, 0, v___x_723_);
v___x_725_ = v___x_678_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_k_682_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v_v_683_);
lean_ctor_set(v_reuseFailAlloc_729_, 3, v_tree_681_);
lean_ctor_set(v_reuseFailAlloc_729_, 4, v_l_699_);
v___x_725_ = v_reuseFailAlloc_729_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; 
v___x_726_ = lean_nat_add(v___x_675_, v_size_701_);
if (lean_obj_tag(v_r_700_) == 0)
{
lean_object* v_size_727_; 
v_size_727_ = lean_ctor_get(v_r_700_, 0);
lean_inc(v_size_727_);
v___y_711_ = v___x_725_;
v___y_712_ = v___x_726_;
v___y_713_ = v_size_727_;
goto v___jp_710_;
}
else
{
lean_object* v___x_728_; 
v___x_728_ = lean_unsigned_to_nat(0u);
v___y_711_ = v___x_725_;
v___y_712_ = v___x_726_;
v___y_713_ = v___x_728_;
goto v___jp_710_;
}
}
}
}
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_738_ = lean_nat_add(v___x_675_, v_size_684_);
v___x_739_ = lean_nat_add(v___x_738_, v_size_670_);
lean_dec(v_size_670_);
v___x_740_ = lean_nat_add(v___x_738_, v_size_696_);
lean_dec(v___x_738_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 4, v_l_673_);
lean_ctor_set(v___x_694_, 3, v_tree_681_);
lean_ctor_set(v___x_694_, 2, v_v_683_);
lean_ctor_set(v___x_694_, 1, v_k_682_);
lean_ctor_set(v___x_694_, 0, v___x_740_);
v___x_742_ = v___x_694_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_k_682_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_v_683_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v_tree_681_);
lean_ctor_set(v_reuseFailAlloc_746_, 4, v_l_673_);
v___x_742_ = v_reuseFailAlloc_746_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_744_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 4, v_r_674_);
lean_ctor_set(v___x_678_, 3, v___x_742_);
lean_ctor_set(v___x_678_, 2, v_v_672_);
lean_ctor_set(v___x_678_, 1, v_k_671_);
lean_ctor_set(v___x_678_, 0, v___x_739_);
v___x_744_ = v___x_678_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_k_671_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_v_672_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_745_, 4, v_r_674_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
}
else
{
lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_806_; 
lean_inc(v_r_674_);
lean_inc(v_v_672_);
lean_inc(v_k_671_);
lean_inc(v_size_670_);
v_isSharedCheck_806_ = !lean_is_exclusive(v_r_486_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; lean_object* v_unused_808_; lean_object* v_unused_809_; lean_object* v_unused_810_; lean_object* v_unused_811_; 
v_unused_807_ = lean_ctor_get(v_r_486_, 4);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_r_486_, 3);
lean_dec(v_unused_808_);
v_unused_809_ = lean_ctor_get(v_r_486_, 2);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_r_486_, 1);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_r_486_, 0);
lean_dec(v_unused_811_);
v___x_754_ = v_r_486_;
v_isShared_755_ = v_isSharedCheck_806_;
goto v_resetjp_753_;
}
else
{
lean_dec(v_r_486_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_806_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
if (lean_obj_tag(v_l_673_) == 0)
{
if (lean_obj_tag(v_r_674_) == 0)
{
lean_object* v_k_756_; lean_object* v_v_757_; lean_object* v_size_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
lean_inc(v_tree_681_);
v_k_756_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_k_756_);
v_v_757_ = lean_ctor_get(v___x_680_, 1);
lean_inc(v_v_757_);
lean_dec_ref(v___x_680_);
v_size_758_ = lean_ctor_get(v_l_673_, 0);
v___x_759_ = lean_nat_add(v___x_675_, v_size_670_);
lean_dec(v_size_670_);
v___x_760_ = lean_nat_add(v___x_675_, v_size_758_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 4, v_l_673_);
lean_ctor_set(v___x_754_, 3, v_tree_681_);
lean_ctor_set(v___x_754_, 2, v_v_757_);
lean_ctor_set(v___x_754_, 1, v_k_756_);
lean_ctor_set(v___x_754_, 0, v___x_760_);
v___x_762_ = v___x_754_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_k_756_);
lean_ctor_set(v_reuseFailAlloc_766_, 2, v_v_757_);
lean_ctor_set(v_reuseFailAlloc_766_, 3, v_tree_681_);
lean_ctor_set(v_reuseFailAlloc_766_, 4, v_l_673_);
v___x_762_ = v_reuseFailAlloc_766_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_764_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 4, v_r_674_);
lean_ctor_set(v___x_678_, 3, v___x_762_);
lean_ctor_set(v___x_678_, 2, v_v_672_);
lean_ctor_set(v___x_678_, 1, v_k_671_);
lean_ctor_set(v___x_678_, 0, v___x_759_);
v___x_764_ = v___x_678_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_k_671_);
lean_ctor_set(v_reuseFailAlloc_765_, 2, v_v_672_);
lean_ctor_set(v_reuseFailAlloc_765_, 3, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_765_, 4, v_r_674_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
else
{
lean_object* v_k_767_; lean_object* v_v_768_; lean_object* v_k_769_; lean_object* v_v_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_784_; 
lean_dec(v_size_670_);
v_k_767_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_k_767_);
v_v_768_ = lean_ctor_get(v___x_680_, 1);
lean_inc(v_v_768_);
lean_dec_ref(v___x_680_);
v_k_769_ = lean_ctor_get(v_l_673_, 1);
v_v_770_ = lean_ctor_get(v_l_673_, 2);
v_isSharedCheck_784_ = !lean_is_exclusive(v_l_673_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; lean_object* v_unused_786_; lean_object* v_unused_787_; 
v_unused_785_ = lean_ctor_get(v_l_673_, 4);
lean_dec(v_unused_785_);
v_unused_786_ = lean_ctor_get(v_l_673_, 3);
lean_dec(v_unused_786_);
v_unused_787_ = lean_ctor_get(v_l_673_, 0);
lean_dec(v_unused_787_);
v___x_772_ = v_l_673_;
v_isShared_773_ = v_isSharedCheck_784_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_v_770_);
lean_inc(v_k_769_);
lean_dec(v_l_673_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_784_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_774_ = lean_unsigned_to_nat(3u);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 4, v_r_674_);
lean_ctor_set(v___x_772_, 3, v_r_674_);
lean_ctor_set(v___x_772_, 2, v_v_768_);
lean_ctor_set(v___x_772_, 1, v_k_767_);
lean_ctor_set(v___x_772_, 0, v___x_675_);
v___x_776_ = v___x_772_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_k_767_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_v_768_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v_r_674_);
lean_ctor_set(v_reuseFailAlloc_783_, 4, v_r_674_);
v___x_776_ = v_reuseFailAlloc_783_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_778_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 3, v_r_674_);
lean_ctor_set(v___x_754_, 0, v___x_675_);
v___x_778_ = v___x_754_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_k_671_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_v_672_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v_r_674_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v_r_674_);
v___x_778_ = v_reuseFailAlloc_782_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_780_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 4, v___x_778_);
lean_ctor_set(v___x_678_, 3, v___x_776_);
lean_ctor_set(v___x_678_, 2, v_v_770_);
lean_ctor_set(v___x_678_, 1, v_k_769_);
lean_ctor_set(v___x_678_, 0, v___x_774_);
v___x_780_ = v___x_678_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_k_769_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_v_770_);
lean_ctor_set(v_reuseFailAlloc_781_, 3, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_781_, 4, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_674_) == 0)
{
lean_object* v_k_788_; lean_object* v_v_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
lean_dec(v_size_670_);
v_k_788_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_k_788_);
v_v_789_ = lean_ctor_get(v___x_680_, 1);
lean_inc(v_v_789_);
lean_dec_ref(v___x_680_);
v___x_790_ = lean_unsigned_to_nat(3u);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 4, v_l_673_);
lean_ctor_set(v___x_754_, 2, v_v_789_);
lean_ctor_set(v___x_754_, 1, v_k_788_);
lean_ctor_set(v___x_754_, 0, v___x_675_);
v___x_792_ = v___x_754_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_k_788_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v_v_789_);
lean_ctor_set(v_reuseFailAlloc_796_, 3, v_l_673_);
lean_ctor_set(v_reuseFailAlloc_796_, 4, v_l_673_);
v___x_792_ = v_reuseFailAlloc_796_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_794_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 4, v_r_674_);
lean_ctor_set(v___x_678_, 3, v___x_792_);
lean_ctor_set(v___x_678_, 2, v_v_672_);
lean_ctor_set(v___x_678_, 1, v_k_671_);
lean_ctor_set(v___x_678_, 0, v___x_790_);
v___x_794_ = v___x_678_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_k_671_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_v_672_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v_r_674_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v_k_797_; lean_object* v_v_798_; lean_object* v___x_800_; 
v_k_797_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_k_797_);
v_v_798_ = lean_ctor_get(v___x_680_, 1);
lean_inc(v_v_798_);
lean_dec_ref(v___x_680_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 3, v_r_674_);
v___x_800_ = v___x_754_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_size_670_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_k_671_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_v_672_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v_r_674_);
lean_ctor_set(v_reuseFailAlloc_805_, 4, v_r_674_);
v___x_800_ = v_reuseFailAlloc_805_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_801_ = lean_unsigned_to_nat(2u);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 4, v___x_800_);
lean_ctor_set(v___x_678_, 3, v_r_674_);
lean_ctor_set(v___x_678_, 2, v_v_798_);
lean_ctor_set(v___x_678_, 1, v_k_797_);
lean_ctor_set(v___x_678_, 0, v___x_801_);
v___x_803_ = v___x_678_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_k_797_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v_v_798_);
lean_ctor_set(v_reuseFailAlloc_804_, 3, v_r_674_);
lean_ctor_set(v_reuseFailAlloc_804_, 4, v___x_800_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
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
lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_970_; 
lean_inc(v_r_674_);
lean_inc(v_v_672_);
lean_inc(v_k_671_);
v_isSharedCheck_970_ = !lean_is_exclusive(v_r_486_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; lean_object* v_unused_972_; lean_object* v_unused_973_; lean_object* v_unused_974_; lean_object* v_unused_975_; 
v_unused_971_ = lean_ctor_get(v_r_486_, 4);
lean_dec(v_unused_971_);
v_unused_972_ = lean_ctor_get(v_r_486_, 3);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v_r_486_, 2);
lean_dec(v_unused_973_);
v_unused_974_ = lean_ctor_get(v_r_486_, 1);
lean_dec(v_unused_974_);
v_unused_975_ = lean_ctor_get(v_r_486_, 0);
lean_dec(v_unused_975_);
v___x_819_ = v_r_486_;
v_isShared_820_ = v_isSharedCheck_970_;
goto v_resetjp_818_;
}
else
{
lean_dec(v_r_486_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_970_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v_tree_822_; 
v___x_821_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_671_, v_v_672_, v_l_673_, v_r_674_);
v_tree_822_ = lean_ctor_get(v___x_821_, 2);
lean_inc(v_tree_822_);
if (lean_obj_tag(v_tree_822_) == 0)
{
lean_object* v_k_823_; lean_object* v_v_824_; lean_object* v_size_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v_k_823_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_k_823_);
v_v_824_ = lean_ctor_get(v___x_821_, 1);
lean_inc(v_v_824_);
lean_dec_ref(v___x_821_);
v_size_825_ = lean_ctor_get(v_tree_822_, 0);
v___x_826_ = lean_unsigned_to_nat(3u);
v___x_827_ = lean_nat_mul(v___x_826_, v_size_825_);
v___x_828_ = lean_nat_dec_lt(v___x_827_, v_size_665_);
lean_dec(v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
lean_dec(v_r_669_);
v___x_829_ = lean_nat_add(v___x_675_, v_size_665_);
v___x_830_ = lean_nat_add(v___x_829_, v_size_825_);
lean_dec(v___x_829_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 4, v_tree_822_);
lean_ctor_set(v___x_819_, 3, v_l_485_);
lean_ctor_set(v___x_819_, 2, v_v_824_);
lean_ctor_set(v___x_819_, 1, v_k_823_);
lean_ctor_set(v___x_819_, 0, v___x_830_);
v___x_832_ = v___x_819_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_k_823_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v_v_824_);
lean_ctor_set(v_reuseFailAlloc_833_, 3, v_l_485_);
lean_ctor_set(v_reuseFailAlloc_833_, 4, v_tree_822_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
else
{
lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_899_; 
lean_inc(v_l_668_);
lean_inc(v_v_667_);
lean_inc(v_k_666_);
lean_inc(v_size_665_);
v_isSharedCheck_899_ = !lean_is_exclusive(v_l_485_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; lean_object* v_unused_901_; lean_object* v_unused_902_; lean_object* v_unused_903_; lean_object* v_unused_904_; 
v_unused_900_ = lean_ctor_get(v_l_485_, 4);
lean_dec(v_unused_900_);
v_unused_901_ = lean_ctor_get(v_l_485_, 3);
lean_dec(v_unused_901_);
v_unused_902_ = lean_ctor_get(v_l_485_, 2);
lean_dec(v_unused_902_);
v_unused_903_ = lean_ctor_get(v_l_485_, 1);
lean_dec(v_unused_903_);
v_unused_904_ = lean_ctor_get(v_l_485_, 0);
lean_dec(v_unused_904_);
v___x_835_ = v_l_485_;
v_isShared_836_ = v_isSharedCheck_899_;
goto v_resetjp_834_;
}
else
{
lean_dec(v_l_485_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_899_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v_size_837_; lean_object* v_size_838_; lean_object* v_k_839_; lean_object* v_v_840_; lean_object* v_l_841_; lean_object* v_r_842_; lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v_size_837_ = lean_ctor_get(v_l_668_, 0);
v_size_838_ = lean_ctor_get(v_r_669_, 0);
v_k_839_ = lean_ctor_get(v_r_669_, 1);
v_v_840_ = lean_ctor_get(v_r_669_, 2);
v_l_841_ = lean_ctor_get(v_r_669_, 3);
v_r_842_ = lean_ctor_get(v_r_669_, 4);
v___x_843_ = lean_unsigned_to_nat(2u);
v___x_844_ = lean_nat_mul(v___x_843_, v_size_837_);
v___x_845_ = lean_nat_dec_lt(v_size_838_, v___x_844_);
lean_dec(v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_883_; 
lean_inc(v_r_842_);
lean_inc(v_l_841_);
lean_inc(v_v_840_);
lean_inc(v_k_839_);
lean_del_object(v___x_835_);
v_isSharedCheck_883_ = !lean_is_exclusive(v_r_669_);
if (v_isSharedCheck_883_ == 0)
{
lean_object* v_unused_884_; lean_object* v_unused_885_; lean_object* v_unused_886_; lean_object* v_unused_887_; lean_object* v_unused_888_; 
v_unused_884_ = lean_ctor_get(v_r_669_, 4);
lean_dec(v_unused_884_);
v_unused_885_ = lean_ctor_get(v_r_669_, 3);
lean_dec(v_unused_885_);
v_unused_886_ = lean_ctor_get(v_r_669_, 2);
lean_dec(v_unused_886_);
v_unused_887_ = lean_ctor_get(v_r_669_, 1);
lean_dec(v_unused_887_);
v_unused_888_ = lean_ctor_get(v_r_669_, 0);
lean_dec(v_unused_888_);
v___x_847_ = v_r_669_;
v_isShared_848_ = v_isSharedCheck_883_;
goto v_resetjp_846_;
}
else
{
lean_dec(v_r_669_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_883_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___x_871_; lean_object* v___y_873_; 
v___x_849_ = lean_nat_add(v___x_675_, v_size_665_);
lean_dec(v_size_665_);
v___x_850_ = lean_nat_add(v___x_849_, v_size_825_);
lean_dec(v___x_849_);
v___x_871_ = lean_nat_add(v___x_675_, v_size_837_);
if (lean_obj_tag(v_l_841_) == 0)
{
lean_object* v_size_881_; 
v_size_881_ = lean_ctor_get(v_l_841_, 0);
lean_inc(v_size_881_);
v___y_873_ = v_size_881_;
goto v___jp_872_;
}
else
{
lean_object* v___x_882_; 
v___x_882_ = lean_unsigned_to_nat(0u);
v___y_873_ = v___x_882_;
goto v___jp_872_;
}
v___jp_851_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = lean_nat_add(v___y_852_, v___y_854_);
lean_dec(v___y_854_);
lean_dec(v___y_852_);
lean_inc_ref(v_tree_822_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 4, v_tree_822_);
lean_ctor_set(v___x_847_, 3, v_r_842_);
lean_ctor_set(v___x_847_, 2, v_v_824_);
lean_ctor_set(v___x_847_, 1, v_k_823_);
lean_ctor_set(v___x_847_, 0, v___x_855_);
v___x_857_ = v___x_847_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_k_823_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_v_824_);
lean_ctor_set(v_reuseFailAlloc_870_, 3, v_r_842_);
lean_ctor_set(v_reuseFailAlloc_870_, 4, v_tree_822_);
v___x_857_ = v_reuseFailAlloc_870_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
v_isSharedCheck_864_ = !lean_is_exclusive(v_tree_822_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; lean_object* v_unused_866_; lean_object* v_unused_867_; lean_object* v_unused_868_; lean_object* v_unused_869_; 
v_unused_865_ = lean_ctor_get(v_tree_822_, 4);
lean_dec(v_unused_865_);
v_unused_866_ = lean_ctor_get(v_tree_822_, 3);
lean_dec(v_unused_866_);
v_unused_867_ = lean_ctor_get(v_tree_822_, 2);
lean_dec(v_unused_867_);
v_unused_868_ = lean_ctor_get(v_tree_822_, 1);
lean_dec(v_unused_868_);
v_unused_869_ = lean_ctor_get(v_tree_822_, 0);
lean_dec(v_unused_869_);
v___x_859_ = v_tree_822_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_dec(v_tree_822_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 4, v___x_857_);
lean_ctor_set(v___x_859_, 3, v___y_853_);
lean_ctor_set(v___x_859_, 2, v_v_840_);
lean_ctor_set(v___x_859_, 1, v_k_839_);
lean_ctor_set(v___x_859_, 0, v___x_850_);
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_k_839_);
lean_ctor_set(v_reuseFailAlloc_863_, 2, v_v_840_);
lean_ctor_set(v_reuseFailAlloc_863_, 3, v___y_853_);
lean_ctor_set(v_reuseFailAlloc_863_, 4, v___x_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
v___jp_872_:
{
lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_874_ = lean_nat_add(v___x_871_, v___y_873_);
lean_dec(v___y_873_);
lean_dec(v___x_871_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 4, v_l_841_);
lean_ctor_set(v___x_819_, 3, v_l_668_);
lean_ctor_set(v___x_819_, 2, v_v_667_);
lean_ctor_set(v___x_819_, 1, v_k_666_);
lean_ctor_set(v___x_819_, 0, v___x_874_);
v___x_876_ = v___x_819_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_k_666_);
lean_ctor_set(v_reuseFailAlloc_880_, 2, v_v_667_);
lean_ctor_set(v_reuseFailAlloc_880_, 3, v_l_668_);
lean_ctor_set(v_reuseFailAlloc_880_, 4, v_l_841_);
v___x_876_ = v_reuseFailAlloc_880_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; 
v___x_877_ = lean_nat_add(v___x_675_, v_size_825_);
if (lean_obj_tag(v_r_842_) == 0)
{
lean_object* v_size_878_; 
v_size_878_ = lean_ctor_get(v_r_842_, 0);
lean_inc(v_size_878_);
v___y_852_ = v___x_877_;
v___y_853_ = v___x_876_;
v___y_854_ = v_size_878_;
goto v___jp_851_;
}
else
{
lean_object* v___x_879_; 
v___x_879_ = lean_unsigned_to_nat(0u);
v___y_852_ = v___x_877_;
v___y_853_ = v___x_876_;
v___y_854_ = v___x_879_;
goto v___jp_851_;
}
}
}
}
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_889_ = lean_nat_add(v___x_675_, v_size_665_);
lean_dec(v_size_665_);
v___x_890_ = lean_nat_add(v___x_889_, v_size_825_);
lean_dec(v___x_889_);
v___x_891_ = lean_nat_add(v___x_675_, v_size_825_);
v___x_892_ = lean_nat_add(v___x_891_, v_size_838_);
lean_dec(v___x_891_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 4, v_tree_822_);
lean_ctor_set(v___x_819_, 3, v_r_669_);
lean_ctor_set(v___x_819_, 2, v_v_824_);
lean_ctor_set(v___x_819_, 1, v_k_823_);
lean_ctor_set(v___x_819_, 0, v___x_892_);
v___x_894_ = v___x_819_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_k_823_);
lean_ctor_set(v_reuseFailAlloc_898_, 2, v_v_824_);
lean_ctor_set(v_reuseFailAlloc_898_, 3, v_r_669_);
lean_ctor_set(v_reuseFailAlloc_898_, 4, v_tree_822_);
v___x_894_ = v_reuseFailAlloc_898_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_896_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 4, v___x_894_);
lean_ctor_set(v___x_835_, 0, v___x_890_);
v___x_896_ = v___x_835_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_k_666_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_v_667_);
lean_ctor_set(v_reuseFailAlloc_897_, 3, v_l_668_);
lean_ctor_set(v_reuseFailAlloc_897_, 4, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_668_) == 0)
{
lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_928_; 
lean_inc_ref(v_l_668_);
lean_inc(v_v_667_);
lean_inc(v_k_666_);
lean_inc(v_size_665_);
v_isSharedCheck_928_ = !lean_is_exclusive(v_l_485_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; lean_object* v_unused_930_; lean_object* v_unused_931_; lean_object* v_unused_932_; lean_object* v_unused_933_; 
v_unused_929_ = lean_ctor_get(v_l_485_, 4);
lean_dec(v_unused_929_);
v_unused_930_ = lean_ctor_get(v_l_485_, 3);
lean_dec(v_unused_930_);
v_unused_931_ = lean_ctor_get(v_l_485_, 2);
lean_dec(v_unused_931_);
v_unused_932_ = lean_ctor_get(v_l_485_, 1);
lean_dec(v_unused_932_);
v_unused_933_ = lean_ctor_get(v_l_485_, 0);
lean_dec(v_unused_933_);
v___x_906_ = v_l_485_;
v_isShared_907_ = v_isSharedCheck_928_;
goto v_resetjp_905_;
}
else
{
lean_dec(v_l_485_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_928_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
if (lean_obj_tag(v_r_669_) == 0)
{
lean_object* v_k_908_; lean_object* v_v_909_; lean_object* v_size_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
v_k_908_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_k_908_);
v_v_909_ = lean_ctor_get(v___x_821_, 1);
lean_inc(v_v_909_);
lean_dec_ref(v___x_821_);
v_size_910_ = lean_ctor_get(v_r_669_, 0);
v___x_911_ = lean_nat_add(v___x_675_, v_size_665_);
lean_dec(v_size_665_);
v___x_912_ = lean_nat_add(v___x_675_, v_size_910_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 4, v_tree_822_);
lean_ctor_set(v___x_819_, 3, v_r_669_);
lean_ctor_set(v___x_819_, 2, v_v_909_);
lean_ctor_set(v___x_819_, 1, v_k_908_);
lean_ctor_set(v___x_819_, 0, v___x_912_);
v___x_914_ = v___x_819_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_k_908_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v_v_909_);
lean_ctor_set(v_reuseFailAlloc_918_, 3, v_r_669_);
lean_ctor_set(v_reuseFailAlloc_918_, 4, v_tree_822_);
v___x_914_ = v_reuseFailAlloc_918_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_916_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 4, v___x_914_);
lean_ctor_set(v___x_906_, 0, v___x_911_);
v___x_916_ = v___x_906_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_k_666_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_v_667_);
lean_ctor_set(v_reuseFailAlloc_917_, 3, v_l_668_);
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
else
{
lean_object* v_k_919_; lean_object* v_v_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
lean_dec(v_size_665_);
v_k_919_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_k_919_);
v_v_920_ = lean_ctor_get(v___x_821_, 1);
lean_inc(v_v_920_);
lean_dec_ref(v___x_821_);
v___x_921_ = lean_unsigned_to_nat(3u);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 4, v_r_669_);
lean_ctor_set(v___x_819_, 3, v_r_669_);
lean_ctor_set(v___x_819_, 2, v_v_920_);
lean_ctor_set(v___x_819_, 1, v_k_919_);
lean_ctor_set(v___x_819_, 0, v___x_675_);
v___x_923_ = v___x_819_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_k_919_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_v_920_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v_r_669_);
lean_ctor_set(v_reuseFailAlloc_927_, 4, v_r_669_);
v___x_923_ = v_reuseFailAlloc_927_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_925_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 4, v___x_923_);
lean_ctor_set(v___x_906_, 0, v___x_921_);
v___x_925_ = v___x_906_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_k_666_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v_v_667_);
lean_ctor_set(v_reuseFailAlloc_926_, 3, v_l_668_);
lean_ctor_set(v_reuseFailAlloc_926_, 4, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_669_) == 0)
{
lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_958_; 
lean_inc(v_l_668_);
lean_inc(v_v_667_);
lean_inc(v_k_666_);
v_isSharedCheck_958_ = !lean_is_exclusive(v_l_485_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; lean_object* v_unused_960_; lean_object* v_unused_961_; lean_object* v_unused_962_; lean_object* v_unused_963_; 
v_unused_959_ = lean_ctor_get(v_l_485_, 4);
lean_dec(v_unused_959_);
v_unused_960_ = lean_ctor_get(v_l_485_, 3);
lean_dec(v_unused_960_);
v_unused_961_ = lean_ctor_get(v_l_485_, 2);
lean_dec(v_unused_961_);
v_unused_962_ = lean_ctor_get(v_l_485_, 1);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_l_485_, 0);
lean_dec(v_unused_963_);
v___x_935_ = v_l_485_;
v_isShared_936_ = v_isSharedCheck_958_;
goto v_resetjp_934_;
}
else
{
lean_dec(v_l_485_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_958_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v_k_937_; lean_object* v_v_938_; lean_object* v_k_939_; lean_object* v_v_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_954_; 
v_k_937_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_k_937_);
v_v_938_ = lean_ctor_get(v___x_821_, 1);
lean_inc(v_v_938_);
lean_dec_ref(v___x_821_);
v_k_939_ = lean_ctor_get(v_r_669_, 1);
v_v_940_ = lean_ctor_get(v_r_669_, 2);
v_isSharedCheck_954_ = !lean_is_exclusive(v_r_669_);
if (v_isSharedCheck_954_ == 0)
{
lean_object* v_unused_955_; lean_object* v_unused_956_; lean_object* v_unused_957_; 
v_unused_955_ = lean_ctor_get(v_r_669_, 4);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_r_669_, 3);
lean_dec(v_unused_956_);
v_unused_957_ = lean_ctor_get(v_r_669_, 0);
lean_dec(v_unused_957_);
v___x_942_ = v_r_669_;
v_isShared_943_ = v_isSharedCheck_954_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_v_940_);
lean_inc(v_k_939_);
lean_dec(v_r_669_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_954_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_944_ = lean_unsigned_to_nat(3u);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 4, v_l_668_);
lean_ctor_set(v___x_942_, 3, v_l_668_);
lean_ctor_set(v___x_942_, 2, v_v_667_);
lean_ctor_set(v___x_942_, 1, v_k_666_);
lean_ctor_set(v___x_942_, 0, v___x_675_);
v___x_946_ = v___x_942_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_k_666_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v_v_667_);
lean_ctor_set(v_reuseFailAlloc_953_, 3, v_l_668_);
lean_ctor_set(v_reuseFailAlloc_953_, 4, v_l_668_);
v___x_946_ = v_reuseFailAlloc_953_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 4, v_l_668_);
lean_ctor_set(v___x_819_, 3, v_l_668_);
lean_ctor_set(v___x_819_, 2, v_v_938_);
lean_ctor_set(v___x_819_, 1, v_k_937_);
lean_ctor_set(v___x_819_, 0, v___x_675_);
v___x_948_ = v___x_819_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_675_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_k_937_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_v_938_);
lean_ctor_set(v_reuseFailAlloc_952_, 3, v_l_668_);
lean_ctor_set(v_reuseFailAlloc_952_, 4, v_l_668_);
v___x_948_ = v_reuseFailAlloc_952_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_950_; 
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 4, v___x_948_);
lean_ctor_set(v___x_935_, 3, v___x_946_);
lean_ctor_set(v___x_935_, 2, v_v_940_);
lean_ctor_set(v___x_935_, 1, v_k_939_);
lean_ctor_set(v___x_935_, 0, v___x_944_);
v___x_950_ = v___x_935_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_k_939_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_v_940_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
}
else
{
lean_object* v_k_964_; lean_object* v_v_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
v_k_964_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_k_964_);
v_v_965_ = lean_ctor_get(v___x_821_, 1);
lean_inc(v_v_965_);
lean_dec_ref(v___x_821_);
v___x_966_ = lean_unsigned_to_nat(2u);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 4, v_r_669_);
lean_ctor_set(v___x_819_, 3, v_l_485_);
lean_ctor_set(v___x_819_, 2, v_v_965_);
lean_ctor_set(v___x_819_, 1, v_k_964_);
lean_ctor_set(v___x_819_, 0, v___x_966_);
v___x_968_ = v___x_819_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_k_964_);
lean_ctor_set(v_reuseFailAlloc_969_, 2, v_v_965_);
lean_ctor_set(v_reuseFailAlloc_969_, 3, v_l_485_);
lean_ctor_set(v_reuseFailAlloc_969_, 4, v_r_669_);
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
}
else
{
return v_l_485_;
}
}
else
{
return v_r_486_;
}
}
default: 
{
lean_object* v_impl_976_; lean_object* v___x_977_; 
v_impl_976_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_481_, v_r_486_);
v___x_977_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_976_) == 0)
{
if (lean_obj_tag(v_l_485_) == 0)
{
lean_object* v_size_978_; lean_object* v_size_979_; lean_object* v_k_980_; lean_object* v_v_981_; lean_object* v_l_982_; lean_object* v_r_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v_size_978_ = lean_ctor_get(v_impl_976_, 0);
v_size_979_ = lean_ctor_get(v_l_485_, 0);
v_k_980_ = lean_ctor_get(v_l_485_, 1);
v_v_981_ = lean_ctor_get(v_l_485_, 2);
v_l_982_ = lean_ctor_get(v_l_485_, 3);
v_r_983_ = lean_ctor_get(v_l_485_, 4);
lean_inc(v_r_983_);
v___x_984_ = lean_unsigned_to_nat(3u);
v___x_985_ = lean_nat_mul(v___x_984_, v_size_978_);
v___x_986_ = lean_nat_dec_lt(v___x_985_, v_size_979_);
lean_dec(v___x_985_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
lean_dec(v_r_983_);
v___x_987_ = lean_nat_add(v___x_977_, v_size_979_);
v___x_988_ = lean_nat_add(v___x_987_, v_size_978_);
lean_dec(v___x_987_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v_impl_976_);
lean_ctor_set(v___x_488_, 0, v___x_988_);
v___x_990_ = v___x_488_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_991_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_991_, 3, v_l_485_);
lean_ctor_set(v_reuseFailAlloc_991_, 4, v_impl_976_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
else
{
lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1057_; 
lean_inc(v_l_982_);
lean_inc(v_v_981_);
lean_inc(v_k_980_);
lean_inc(v_size_979_);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_l_485_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; lean_object* v_unused_1059_; lean_object* v_unused_1060_; lean_object* v_unused_1061_; lean_object* v_unused_1062_; 
v_unused_1058_ = lean_ctor_get(v_l_485_, 4);
lean_dec(v_unused_1058_);
v_unused_1059_ = lean_ctor_get(v_l_485_, 3);
lean_dec(v_unused_1059_);
v_unused_1060_ = lean_ctor_get(v_l_485_, 2);
lean_dec(v_unused_1060_);
v_unused_1061_ = lean_ctor_get(v_l_485_, 1);
lean_dec(v_unused_1061_);
v_unused_1062_ = lean_ctor_get(v_l_485_, 0);
lean_dec(v_unused_1062_);
v___x_993_ = v_l_485_;
v_isShared_994_ = v_isSharedCheck_1057_;
goto v_resetjp_992_;
}
else
{
lean_dec(v_l_485_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1057_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v_size_995_; lean_object* v_size_996_; lean_object* v_k_997_; lean_object* v_v_998_; lean_object* v_l_999_; lean_object* v_r_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v_size_995_ = lean_ctor_get(v_l_982_, 0);
v_size_996_ = lean_ctor_get(v_r_983_, 0);
v_k_997_ = lean_ctor_get(v_r_983_, 1);
v_v_998_ = lean_ctor_get(v_r_983_, 2);
v_l_999_ = lean_ctor_get(v_r_983_, 3);
v_r_1000_ = lean_ctor_get(v_r_983_, 4);
v___x_1001_ = lean_unsigned_to_nat(2u);
v___x_1002_ = lean_nat_mul(v___x_1001_, v_size_995_);
v___x_1003_ = lean_nat_dec_lt(v_size_996_, v___x_1002_);
lean_dec(v___x_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1032_; 
lean_inc(v_r_1000_);
lean_inc(v_l_999_);
lean_inc(v_v_998_);
lean_inc(v_k_997_);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_r_983_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; lean_object* v_unused_1034_; lean_object* v_unused_1035_; lean_object* v_unused_1036_; lean_object* v_unused_1037_; 
v_unused_1033_ = lean_ctor_get(v_r_983_, 4);
lean_dec(v_unused_1033_);
v_unused_1034_ = lean_ctor_get(v_r_983_, 3);
lean_dec(v_unused_1034_);
v_unused_1035_ = lean_ctor_get(v_r_983_, 2);
lean_dec(v_unused_1035_);
v_unused_1036_ = lean_ctor_get(v_r_983_, 1);
lean_dec(v_unused_1036_);
v_unused_1037_ = lean_ctor_get(v_r_983_, 0);
lean_dec(v_unused_1037_);
v___x_1005_ = v_r_983_;
v_isShared_1006_ = v_isSharedCheck_1032_;
goto v_resetjp_1004_;
}
else
{
lean_dec(v_r_983_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1032_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___x_1020_; lean_object* v___y_1022_; 
v___x_1007_ = lean_nat_add(v___x_977_, v_size_979_);
lean_dec(v_size_979_);
v___x_1008_ = lean_nat_add(v___x_1007_, v_size_978_);
lean_dec(v___x_1007_);
v___x_1020_ = lean_nat_add(v___x_977_, v_size_995_);
if (lean_obj_tag(v_l_999_) == 0)
{
lean_object* v_size_1030_; 
v_size_1030_ = lean_ctor_get(v_l_999_, 0);
lean_inc(v_size_1030_);
v___y_1022_ = v_size_1030_;
goto v___jp_1021_;
}
else
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_unsigned_to_nat(0u);
v___y_1022_ = v___x_1031_;
goto v___jp_1021_;
}
v___jp_1009_:
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = lean_nat_add(v___y_1010_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec(v___y_1010_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 4, v_impl_976_);
lean_ctor_set(v___x_1005_, 3, v_r_1000_);
lean_ctor_set(v___x_1005_, 2, v_v_484_);
lean_ctor_set(v___x_1005_, 1, v_k_483_);
lean_ctor_set(v___x_1005_, 0, v___x_1013_);
v___x_1015_ = v___x_1005_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v_r_1000_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v_impl_976_);
v___x_1015_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1017_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 4, v___x_1015_);
lean_ctor_set(v___x_993_, 3, v___y_1011_);
lean_ctor_set(v___x_993_, 2, v_v_998_);
lean_ctor_set(v___x_993_, 1, v_k_997_);
lean_ctor_set(v___x_993_, 0, v___x_1008_);
v___x_1017_ = v___x_993_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_k_997_);
lean_ctor_set(v_reuseFailAlloc_1018_, 2, v_v_998_);
lean_ctor_set(v_reuseFailAlloc_1018_, 3, v___y_1011_);
lean_ctor_set(v_reuseFailAlloc_1018_, 4, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
v___jp_1021_:
{
lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___x_1023_ = lean_nat_add(v___x_1020_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec(v___x_1020_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v_l_999_);
lean_ctor_set(v___x_488_, 3, v_l_982_);
lean_ctor_set(v___x_488_, 2, v_v_981_);
lean_ctor_set(v___x_488_, 1, v_k_980_);
lean_ctor_set(v___x_488_, 0, v___x_1023_);
v___x_1025_ = v___x_488_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_k_980_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v_v_981_);
lean_ctor_set(v_reuseFailAlloc_1029_, 3, v_l_982_);
lean_ctor_set(v_reuseFailAlloc_1029_, 4, v_l_999_);
v___x_1025_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_nat_add(v___x_977_, v_size_978_);
if (lean_obj_tag(v_r_1000_) == 0)
{
lean_object* v_size_1027_; 
v_size_1027_ = lean_ctor_get(v_r_1000_, 0);
lean_inc(v_size_1027_);
v___y_1010_ = v___x_1026_;
v___y_1011_ = v___x_1025_;
v___y_1012_ = v_size_1027_;
goto v___jp_1009_;
}
else
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_unsigned_to_nat(0u);
v___y_1010_ = v___x_1026_;
v___y_1011_ = v___x_1025_;
v___y_1012_ = v___x_1028_;
goto v___jp_1009_;
}
}
}
}
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
lean_del_object(v___x_488_);
v___x_1038_ = lean_nat_add(v___x_977_, v_size_979_);
lean_dec(v_size_979_);
v___x_1039_ = lean_nat_add(v___x_1038_, v_size_978_);
lean_dec(v___x_1038_);
v___x_1040_ = lean_nat_add(v___x_977_, v_size_978_);
v___x_1041_ = lean_nat_add(v___x_1040_, v_size_996_);
lean_dec(v___x_1040_);
lean_inc_ref(v_impl_976_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 4, v_impl_976_);
lean_ctor_set(v___x_993_, 3, v_r_983_);
lean_ctor_set(v___x_993_, 2, v_v_484_);
lean_ctor_set(v___x_993_, 1, v_k_483_);
lean_ctor_set(v___x_993_, 0, v___x_1041_);
v___x_1043_ = v___x_993_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_1056_, 3, v_r_983_);
lean_ctor_set(v_reuseFailAlloc_1056_, 4, v_impl_976_);
v___x_1043_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
v_isSharedCheck_1050_ = !lean_is_exclusive(v_impl_976_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; lean_object* v_unused_1052_; lean_object* v_unused_1053_; lean_object* v_unused_1054_; lean_object* v_unused_1055_; 
v_unused_1051_ = lean_ctor_get(v_impl_976_, 4);
lean_dec(v_unused_1051_);
v_unused_1052_ = lean_ctor_get(v_impl_976_, 3);
lean_dec(v_unused_1052_);
v_unused_1053_ = lean_ctor_get(v_impl_976_, 2);
lean_dec(v_unused_1053_);
v_unused_1054_ = lean_ctor_get(v_impl_976_, 1);
lean_dec(v_unused_1054_);
v_unused_1055_ = lean_ctor_get(v_impl_976_, 0);
lean_dec(v_unused_1055_);
v___x_1045_ = v_impl_976_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_dec(v_impl_976_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 4, v___x_1043_);
lean_ctor_set(v___x_1045_, 3, v_l_982_);
lean_ctor_set(v___x_1045_, 2, v_v_981_);
lean_ctor_set(v___x_1045_, 1, v_k_980_);
lean_ctor_set(v___x_1045_, 0, v___x_1039_);
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_k_980_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_v_981_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v_l_982_);
lean_ctor_set(v_reuseFailAlloc_1049_, 4, v___x_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
v_size_1063_ = lean_ctor_get(v_impl_976_, 0);
v___x_1064_ = lean_nat_add(v___x_977_, v_size_1063_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v_impl_976_);
lean_ctor_set(v___x_488_, 0, v___x_1064_);
v___x_1066_ = v___x_488_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_1067_, 3, v_l_485_);
lean_ctor_set(v_reuseFailAlloc_1067_, 4, v_impl_976_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
else
{
if (lean_obj_tag(v_l_485_) == 0)
{
lean_object* v_l_1068_; 
v_l_1068_ = lean_ctor_get(v_l_485_, 3);
if (lean_obj_tag(v_l_1068_) == 0)
{
lean_object* v_r_1069_; 
lean_inc_ref(v_l_1068_);
v_r_1069_ = lean_ctor_get(v_l_485_, 4);
lean_inc(v_r_1069_);
if (lean_obj_tag(v_r_1069_) == 0)
{
lean_object* v_size_1070_; lean_object* v_k_1071_; lean_object* v_v_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1085_; 
v_size_1070_ = lean_ctor_get(v_l_485_, 0);
v_k_1071_ = lean_ctor_get(v_l_485_, 1);
v_v_1072_ = lean_ctor_get(v_l_485_, 2);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_l_485_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; lean_object* v_unused_1087_; 
v_unused_1086_ = lean_ctor_get(v_l_485_, 4);
lean_dec(v_unused_1086_);
v_unused_1087_ = lean_ctor_get(v_l_485_, 3);
lean_dec(v_unused_1087_);
v___x_1074_ = v_l_485_;
v_isShared_1075_ = v_isSharedCheck_1085_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_v_1072_);
lean_inc(v_k_1071_);
lean_inc(v_size_1070_);
lean_dec(v_l_485_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1085_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v_size_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v_size_1076_ = lean_ctor_get(v_r_1069_, 0);
v___x_1077_ = lean_nat_add(v___x_977_, v_size_1070_);
lean_dec(v_size_1070_);
v___x_1078_ = lean_nat_add(v___x_977_, v_size_1076_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 4, v_impl_976_);
lean_ctor_set(v___x_1074_, 3, v_r_1069_);
lean_ctor_set(v___x_1074_, 2, v_v_484_);
lean_ctor_set(v___x_1074_, 1, v_k_483_);
lean_ctor_set(v___x_1074_, 0, v___x_1078_);
v___x_1080_ = v___x_1074_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_1084_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_1084_, 3, v_r_1069_);
lean_ctor_set(v_reuseFailAlloc_1084_, 4, v_impl_976_);
v___x_1080_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1082_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v___x_1080_);
lean_ctor_set(v___x_488_, 3, v_l_1068_);
lean_ctor_set(v___x_488_, 2, v_v_1072_);
lean_ctor_set(v___x_488_, 1, v_k_1071_);
lean_ctor_set(v___x_488_, 0, v___x_1077_);
v___x_1082_ = v___x_488_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_k_1071_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_v_1072_);
lean_ctor_set(v_reuseFailAlloc_1083_, 3, v_l_1068_);
lean_ctor_set(v_reuseFailAlloc_1083_, 4, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
else
{
lean_object* v_k_1088_; lean_object* v_v_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1100_; 
v_k_1088_ = lean_ctor_get(v_l_485_, 1);
v_v_1089_ = lean_ctor_get(v_l_485_, 2);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_l_485_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; lean_object* v_unused_1102_; lean_object* v_unused_1103_; 
v_unused_1101_ = lean_ctor_get(v_l_485_, 4);
lean_dec(v_unused_1101_);
v_unused_1102_ = lean_ctor_get(v_l_485_, 3);
lean_dec(v_unused_1102_);
v_unused_1103_ = lean_ctor_get(v_l_485_, 0);
lean_dec(v_unused_1103_);
v___x_1091_ = v_l_485_;
v_isShared_1092_ = v_isSharedCheck_1100_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_v_1089_);
lean_inc(v_k_1088_);
lean_dec(v_l_485_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1100_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1093_ = lean_unsigned_to_nat(3u);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 3, v_r_1069_);
lean_ctor_set(v___x_1091_, 2, v_v_484_);
lean_ctor_set(v___x_1091_, 1, v_k_483_);
lean_ctor_set(v___x_1091_, 0, v___x_977_);
v___x_1095_ = v___x_1091_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_1099_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_1099_, 3, v_r_1069_);
lean_ctor_set(v_reuseFailAlloc_1099_, 4, v_r_1069_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1097_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v___x_1095_);
lean_ctor_set(v___x_488_, 3, v_l_1068_);
lean_ctor_set(v___x_488_, 2, v_v_1089_);
lean_ctor_set(v___x_488_, 1, v_k_1088_);
lean_ctor_set(v___x_488_, 0, v___x_1093_);
v___x_1097_ = v___x_488_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_k_1088_);
lean_ctor_set(v_reuseFailAlloc_1098_, 2, v_v_1089_);
lean_ctor_set(v_reuseFailAlloc_1098_, 3, v_l_1068_);
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
}
else
{
lean_object* v_r_1104_; 
v_r_1104_ = lean_ctor_get(v_l_485_, 4);
lean_inc(v_r_1104_);
if (lean_obj_tag(v_r_1104_) == 0)
{
lean_object* v_k_1105_; lean_object* v_v_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1129_; 
lean_inc(v_l_1068_);
v_k_1105_ = lean_ctor_get(v_l_485_, 1);
v_v_1106_ = lean_ctor_get(v_l_485_, 2);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_l_485_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; lean_object* v_unused_1131_; lean_object* v_unused_1132_; 
v_unused_1130_ = lean_ctor_get(v_l_485_, 4);
lean_dec(v_unused_1130_);
v_unused_1131_ = lean_ctor_get(v_l_485_, 3);
lean_dec(v_unused_1131_);
v_unused_1132_ = lean_ctor_get(v_l_485_, 0);
lean_dec(v_unused_1132_);
v___x_1108_ = v_l_485_;
v_isShared_1109_ = v_isSharedCheck_1129_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_v_1106_);
lean_inc(v_k_1105_);
lean_dec(v_l_485_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1129_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_k_1110_; lean_object* v_v_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1125_; 
v_k_1110_ = lean_ctor_get(v_r_1104_, 1);
v_v_1111_ = lean_ctor_get(v_r_1104_, 2);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_r_1104_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; lean_object* v_unused_1127_; lean_object* v_unused_1128_; 
v_unused_1126_ = lean_ctor_get(v_r_1104_, 4);
lean_dec(v_unused_1126_);
v_unused_1127_ = lean_ctor_get(v_r_1104_, 3);
lean_dec(v_unused_1127_);
v_unused_1128_ = lean_ctor_get(v_r_1104_, 0);
lean_dec(v_unused_1128_);
v___x_1113_ = v_r_1104_;
v_isShared_1114_ = v_isSharedCheck_1125_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_v_1111_);
lean_inc(v_k_1110_);
lean_dec(v_r_1104_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1125_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1115_ = lean_unsigned_to_nat(3u);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 4, v_l_1068_);
lean_ctor_set(v___x_1113_, 3, v_l_1068_);
lean_ctor_set(v___x_1113_, 2, v_v_1106_);
lean_ctor_set(v___x_1113_, 1, v_k_1105_);
lean_ctor_set(v___x_1113_, 0, v___x_977_);
v___x_1117_ = v___x_1113_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_k_1105_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v_v_1106_);
lean_ctor_set(v_reuseFailAlloc_1124_, 3, v_l_1068_);
lean_ctor_set(v_reuseFailAlloc_1124_, 4, v_l_1068_);
v___x_1117_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1119_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v_l_1068_);
lean_ctor_set(v___x_1108_, 2, v_v_484_);
lean_ctor_set(v___x_1108_, 1, v_k_483_);
lean_ctor_set(v___x_1108_, 0, v___x_977_);
v___x_1119_ = v___x_1108_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_1123_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_1123_, 3, v_l_1068_);
lean_ctor_set(v_reuseFailAlloc_1123_, 4, v_l_1068_);
v___x_1119_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1121_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v___x_1119_);
lean_ctor_set(v___x_488_, 3, v___x_1117_);
lean_ctor_set(v___x_488_, 2, v_v_1111_);
lean_ctor_set(v___x_488_, 1, v_k_1110_);
lean_ctor_set(v___x_488_, 0, v___x_1115_);
v___x_1121_ = v___x_488_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_k_1110_);
lean_ctor_set(v_reuseFailAlloc_1122_, 2, v_v_1111_);
lean_ctor_set(v_reuseFailAlloc_1122_, 3, v___x_1117_);
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
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = lean_unsigned_to_nat(2u);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v_r_1104_);
lean_ctor_set(v___x_488_, 0, v___x_1133_);
v___x_1135_ = v___x_488_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_1136_, 3, v_l_485_);
lean_ctor_set(v_reuseFailAlloc_1136_, 4, v_r_1104_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
else
{
lean_object* v___x_1138_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 4, v_l_485_);
lean_ctor_set(v___x_488_, 0, v___x_977_);
v___x_1138_ = v___x_488_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_k_483_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_v_484_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v_l_485_);
lean_ctor_set(v_reuseFailAlloc_1139_, 4, v_l_485_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
}
}
else
{
return v_t_482_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg___boxed(lean_object* v_k_1142_, lean_object* v_t_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_1142_, v_t_1143_);
lean_dec(v_k_1142_);
return v_res_1144_;
}
}
lean_object* l_Lean_removeBuiltinDocString(lean_object* v_declName_1145_){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1147_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1148_ = lean_st_ref_take(v___x_1147_);
v___x_1149_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_declName_1145_, v___x_1148_);
v___x_1150_ = lean_st_ref_put(v___x_1147_, v___x_1149_);
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT void l_Lean_removeBuiltinDocString_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1145_ = stack[0].m_obj;
lean_object* v_res_1152_;
v_res_1152_ = l_Lean_removeBuiltinDocString(v_declName_1145_);
stack->m_obj
 = v_res_1152_;
}
LEAN_EXPORT lean_object* l_Lean_removeBuiltinDocString___boxed(lean_object* v_declName_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_removeBuiltinDocString(v_declName_1153_);
lean_dec(v_declName_1153_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(lean_object* v_00_u03b2_1156_, lean_object* v_k_1157_, lean_object* v_t_1158_, lean_object* v_h_1159_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___redArg(v_k_1157_, v_t_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0___boxed(lean_object* v_00_u03b2_1161_, lean_object* v_k_1162_, lean_object* v_t_1163_, lean_object* v_h_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeBuiltinDocString_spec__0(v_00_u03b2_1161_, v_k_1162_, v_t_1163_, v_h_1164_);
lean_dec(v_k_1162_);
return v_res_1165_;
}
}
lean_object* l_Lean_getBuiltinVersoDocStrings(){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1168_ = lean_st_ref_get(v___x_1167_);
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT void l_Lean_getBuiltinVersoDocStrings_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1170_;
v_res_1170_ = l_Lean_getBuiltinVersoDocStrings();
stack->m_obj
 = v_res_1170_;
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinVersoDocStrings___boxed(lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_getBuiltinVersoDocStrings();
return v_res_1172_;
}
}
static lean_object* _init_l_Lean_throwIfHasDocString___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = ((lean_object*)(l_Lean_throwIfHasDocString___redArg___lam__0___closed__0));
v___x_1175_ = l_Lean_stringToMessageData(v___x_1174_);
return v___x_1175_;
}
}
static lean_object* _init_l_Lean_throwIfHasDocString___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = ((lean_object*)(l_Lean_throwIfHasDocString___redArg___lam__0___closed__2));
v___x_1178_ = l_Lean_stringToMessageData(v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwIfHasDocString___redArg___lam__0(lean_object* v_toPure_1179_, lean_object* v_declName_1180_, lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v___x_1183_, lean_object* v___x_1184_, lean_object* v_env_1185_){
_start:
{
uint8_t v___y_1187_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1197_ = l_Lean_docStringExt;
v___x_1198_ = lean_box(1);
lean_inc(v_declName_1180_);
lean_inc_ref(v_env_1185_);
v___x_1199_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_1183_, v___x_1197_, v_env_1185_, v_declName_1180_, v___x_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_1180_);
v___x_1201_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_1184_, v___x_1200_, v_env_1185_, v_declName_1180_, v___x_1198_);
v___y_1187_ = v___x_1201_;
goto v___jp_1186_;
}
else
{
lean_dec_ref(v_env_1185_);
lean_dec_ref(v___x_1184_);
v___y_1187_ = v___x_1199_;
goto v___jp_1186_;
}
v___jp_1186_:
{
if (v___y_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec_ref(v_inst_1182_);
lean_dec_ref(v_inst_1181_);
lean_dec(v_declName_1180_);
v___x_1188_ = lean_box(0);
v___x_1189_ = lean_apply_2(v_toPure_1179_, lean_box(0), v___x_1188_);
return v___x_1189_;
}
else
{
lean_object* v___x_1190_; uint8_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec(v_toPure_1179_);
v___x_1190_ = lean_obj_once(&l_Lean_throwIfHasDocString___redArg___lam__0___closed__1, &l_Lean_throwIfHasDocString___redArg___lam__0___closed__1_once, _init_l_Lean_throwIfHasDocString___redArg___lam__0___closed__1);
v___x_1191_ = 0;
v___x_1192_ = l_Lean_MessageData_ofConstName(v_declName_1180_, v___x_1191_);
v___x_1193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1190_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = lean_obj_once(&l_Lean_throwIfHasDocString___redArg___lam__0___closed__3, &l_Lean_throwIfHasDocString___redArg___lam__0___closed__3_once, _init_l_Lean_throwIfHasDocString___redArg___lam__0___closed__3);
v___x_1195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = l_Lean_throwError___redArg(v_inst_1181_, v_inst_1182_, v___x_1195_);
return v___x_1196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwIfHasDocString___redArg(lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_declName_1206_){
_start:
{
lean_object* v_toApplicative_1207_; lean_object* v_toBind_1208_; lean_object* v_getEnv_1209_; lean_object* v_toPure_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___f_1213_; lean_object* v___x_1214_; 
v_toApplicative_1207_ = lean_ctor_get(v_inst_1203_, 0);
v_toBind_1208_ = lean_ctor_get(v_inst_1203_, 1);
lean_inc(v_toBind_1208_);
v_getEnv_1209_ = lean_ctor_get(v_inst_1205_, 0);
lean_inc(v_getEnv_1209_);
lean_dec_ref(v_inst_1205_);
v_toPure_1210_ = lean_ctor_get(v_toApplicative_1207_, 1);
lean_inc(v_toPure_1210_);
v___x_1211_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default));
v___x_1212_ = ((lean_object*)(l_Lean_throwIfHasDocString___redArg___closed__0));
v___f_1213_ = lean_alloc_closure((void*)(l_Lean_throwIfHasDocString___redArg___lam__0), 7, 6);
lean_closure_set(v___f_1213_, 0, v_toPure_1210_);
lean_closure_set(v___f_1213_, 1, v_declName_1206_);
lean_closure_set(v___f_1213_, 2, v_inst_1203_);
lean_closure_set(v___f_1213_, 3, v_inst_1204_);
lean_closure_set(v___f_1213_, 4, v___x_1212_);
lean_closure_set(v___f_1213_, 5, v___x_1211_);
v___x_1214_ = lean_apply_4(v_toBind_1208_, lean_box(0), lean_box(0), v_getEnv_1209_, v___f_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwIfHasDocString(lean_object* v_m_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_declName_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_throwIfHasDocString___redArg(v_inst_1216_, v_inst_1217_, v_inst_1218_, v_declName_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__0(lean_object* v_docString_1221_, lean_object* v_declName_1222_, lean_object* v_env_1223_){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; lean_object* v___x_1227_; 
v___x_1224_ = l_Lean_docStringExt;
v___x_1225_ = l_String_removeLeadingSpaces(v_docString_1221_);
v___x_1226_ = 1;
v___x_1227_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1224_, v_env_1223_, v_declName_1222_, v___x_1225_, v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__1(lean_object* v_modifyEnv_1228_, lean_object* v___f_1229_, lean_object* v_____r_1230_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = lean_apply_1(v_modifyEnv_1228_, v___f_1229_);
return v___x_1231_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = ((lean_object*)(l_Lean_addDocStringCore___redArg___lam__2___closed__0));
v___x_1234_ = l_Lean_stringToMessageData(v___x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2(lean_object* v_declName_1235_, lean_object* v_modifyEnv_1236_, lean_object* v___f_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_toBind_1240_, lean_object* v___f_1241_, lean_object* v_____do__lift_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1242_, v_declName_1235_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v___x_1244_; 
lean_dec(v___f_1241_);
lean_dec(v_toBind_1240_);
lean_dec_ref(v_inst_1239_);
lean_dec_ref(v_inst_1238_);
lean_dec(v_declName_1235_);
v___x_1244_ = lean_apply_1(v_modifyEnv_1236_, v___f_1237_);
return v___x_1244_;
}
else
{
uint8_t v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_dec_ref_known(v___x_1243_, 1);
lean_dec_ref(v___f_1237_);
lean_dec(v_modifyEnv_1236_);
v___x_1245_ = 0;
v___x_1246_ = lean_obj_once(&l_Lean_throwIfHasDocString___redArg___lam__0___closed__1, &l_Lean_throwIfHasDocString___redArg___lam__0___closed__1_once, _init_l_Lean_throwIfHasDocString___redArg___lam__0___closed__1);
v___x_1247_ = l_Lean_MessageData_ofConstName(v_declName_1235_, v___x_1245_);
v___x_1248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1246_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__1, &l_Lean_addDocStringCore___redArg___lam__2___closed__1_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1);
v___x_1250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = l_Lean_throwError___redArg(v_inst_1238_, v_inst_1239_, v___x_1250_);
v___x_1252_ = lean_apply_4(v_toBind_1240_, lean_box(0), lean_box(0), v___x_1251_, v___f_1241_);
return v___x_1252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_1253_, lean_object* v_modifyEnv_1254_, lean_object* v___f_1255_, lean_object* v_inst_1256_, lean_object* v_inst_1257_, lean_object* v_toBind_1258_, lean_object* v___f_1259_, lean_object* v_____do__lift_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_addDocStringCore___redArg___lam__2(v_declName_1253_, v_modifyEnv_1254_, v___f_1255_, v_inst_1256_, v_inst_1257_, v_toBind_1258_, v___f_1259_, v_____do__lift_1260_);
lean_dec_ref(v_____do__lift_1260_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg(lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_declName_1265_, lean_object* v_docString_1266_){
_start:
{
lean_object* v_toBind_1267_; lean_object* v_getEnv_1268_; lean_object* v_modifyEnv_1269_; lean_object* v___f_1270_; lean_object* v___f_1271_; lean_object* v___f_1272_; lean_object* v___x_1273_; 
v_toBind_1267_ = lean_ctor_get(v_inst_1262_, 1);
lean_inc_n(v_toBind_1267_, 2);
v_getEnv_1268_ = lean_ctor_get(v_inst_1264_, 0);
lean_inc(v_getEnv_1268_);
v_modifyEnv_1269_ = lean_ctor_get(v_inst_1264_, 1);
lean_inc_n(v_modifyEnv_1269_, 2);
lean_dec_ref(v_inst_1264_);
lean_inc(v_declName_1265_);
v___f_1270_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1270_, 0, v_docString_1266_);
lean_closure_set(v___f_1270_, 1, v_declName_1265_);
lean_inc_ref(v___f_1270_);
v___f_1271_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1271_, 0, v_modifyEnv_1269_);
lean_closure_set(v___f_1271_, 1, v___f_1270_);
v___f_1272_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1272_, 0, v_declName_1265_);
lean_closure_set(v___f_1272_, 1, v_modifyEnv_1269_);
lean_closure_set(v___f_1272_, 2, v___f_1270_);
lean_closure_set(v___f_1272_, 3, v_inst_1262_);
lean_closure_set(v___f_1272_, 4, v_inst_1263_);
lean_closure_set(v___f_1272_, 5, v_toBind_1267_);
lean_closure_set(v___f_1272_, 6, v___f_1271_);
v___x_1273_ = lean_apply_4(v_toBind_1267_, lean_box(0), lean_box(0), v_getEnv_1268_, v___f_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore(lean_object* v_m_1274_, lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_declName_1279_, lean_object* v_docString_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_addDocStringCore___redArg(v_inst_1275_, v_inst_1276_, v_inst_1277_, v_declName_1279_, v_docString_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___boxed(lean_object* v_m_1282_, lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_declName_1287_, lean_object* v_docString_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_addDocStringCore(v_m_1282_, v_inst_1283_, v_inst_1284_, v_inst_1285_, v_inst_1286_, v_declName_1287_, v_docString_1288_);
lean_dec(v_inst_1286_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__0(lean_object* v_declName_1291_, lean_object* v_ps_1292_){
_start:
{
lean_object* v_importedEntries_1293_; lean_object* v_state_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1303_; 
v_importedEntries_1293_ = lean_ctor_get(v_ps_1292_, 0);
v_state_1294_ = lean_ctor_get(v_ps_1292_, 1);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_ps_1292_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1296_ = v_ps_1292_;
v_isShared_1297_ = v_isSharedCheck_1303_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_state_1294_);
lean_inc(v_importedEntries_1293_);
lean_dec(v_ps_1292_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1303_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1298_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__0___closed__0));
v___x_1299_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_1298_, v_declName_1291_, v_state_1294_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 1, v___x_1299_);
v___x_1301_ = v___x_1296_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_importedEntries_1293_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__1(lean_object* v___f_1304_, lean_object* v_env_1305_){
_start:
{
lean_object* v___x_1306_; lean_object* v_toEnvExtension_1307_; uint8_t v_logWrites_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1306_ = l_Lean_docStringExt;
v_toEnvExtension_1307_ = lean_ctor_get(v___x_1306_, 0);
v_logWrites_1308_ = lean_ctor_get_uint8(v_toEnvExtension_1307_, sizeof(void*)*6);
v___x_1309_ = lean_box(2);
v___x_1310_ = lean_box(0);
v___x_1311_ = 1;
if (v_logWrites_1308_ == 0)
{
lean_object* v___x_1312_; 
lean_inc_ref(v_toEnvExtension_1307_);
v___x_1312_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1307_, v_env_1305_, v___f_1304_, v___x_1309_, v___x_1310_, v___x_1311_);
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
lean_inc_ref_n(v_toEnvExtension_1307_, 2);
v___x_1313_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1307_, v_env_1305_);
lean_dec_ref(v_env_1305_);
v___x_1314_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1307_, v___x_1313_, v___f_1304_, v___x_1309_, v___x_1310_, v___x_1311_);
return v___x_1314_;
}
}
}
static lean_object* _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__3___closed__0));
v___x_1317_ = l_Lean_stringToMessageData(v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3(lean_object* v_declName_1318_, lean_object* v_modifyEnv_1319_, lean_object* v___f_1320_, lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_toBind_1323_, lean_object* v___f_1324_, lean_object* v_____do__lift_1325_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1325_, v_declName_1318_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v___x_1327_; 
lean_dec(v___f_1324_);
lean_dec(v_toBind_1323_);
lean_dec_ref(v_inst_1322_);
lean_dec_ref(v_inst_1321_);
lean_dec(v_declName_1318_);
v___x_1327_ = lean_apply_1(v_modifyEnv_1319_, v___f_1320_);
return v___x_1327_;
}
else
{
uint8_t v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
lean_dec_ref_known(v___x_1326_, 1);
lean_dec_ref(v___f_1320_);
lean_dec(v_modifyEnv_1319_);
v___x_1328_ = 0;
v___x_1329_ = lean_obj_once(&l_Lean_removeDocStringCore___redArg___lam__3___closed__1, &l_Lean_removeDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1);
v___x_1330_ = l_Lean_MessageData_ofConstName(v_declName_1318_, v___x_1328_);
v___x_1331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1329_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__1, &l_Lean_addDocStringCore___redArg___lam__2___closed__1_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1);
v___x_1333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = l_Lean_throwError___redArg(v_inst_1321_, v_inst_1322_, v___x_1333_);
v___x_1335_ = lean_apply_4(v_toBind_1323_, lean_box(0), lean_box(0), v___x_1334_, v___f_1324_);
return v___x_1335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_1336_, lean_object* v_modifyEnv_1337_, lean_object* v___f_1338_, lean_object* v_inst_1339_, lean_object* v_inst_1340_, lean_object* v_toBind_1341_, lean_object* v___f_1342_, lean_object* v_____do__lift_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_removeDocStringCore___redArg___lam__3(v_declName_1336_, v_modifyEnv_1337_, v___f_1338_, v_inst_1339_, v_inst_1340_, v_toBind_1341_, v___f_1342_, v_____do__lift_1343_);
lean_dec_ref(v_____do__lift_1343_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg(lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_declName_1348_){
_start:
{
lean_object* v_toBind_1349_; lean_object* v_getEnv_1350_; lean_object* v_modifyEnv_1351_; lean_object* v___f_1352_; lean_object* v___f_1353_; lean_object* v___f_1354_; lean_object* v___f_1355_; lean_object* v___x_1356_; 
v_toBind_1349_ = lean_ctor_get(v_inst_1345_, 1);
lean_inc_n(v_toBind_1349_, 2);
v_getEnv_1350_ = lean_ctor_get(v_inst_1347_, 0);
lean_inc(v_getEnv_1350_);
v_modifyEnv_1351_ = lean_ctor_get(v_inst_1347_, 1);
lean_inc_n(v_modifyEnv_1351_, 2);
lean_dec_ref(v_inst_1347_);
lean_inc(v_declName_1348_);
v___f_1352_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1352_, 0, v_declName_1348_);
v___f_1353_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1353_, 0, v___f_1352_);
lean_inc_ref(v___f_1353_);
v___f_1354_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1354_, 0, v_modifyEnv_1351_);
lean_closure_set(v___f_1354_, 1, v___f_1353_);
v___f_1355_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1355_, 0, v_declName_1348_);
lean_closure_set(v___f_1355_, 1, v_modifyEnv_1351_);
lean_closure_set(v___f_1355_, 2, v___f_1353_);
lean_closure_set(v___f_1355_, 3, v_inst_1345_);
lean_closure_set(v___f_1355_, 4, v_inst_1346_);
lean_closure_set(v___f_1355_, 5, v_toBind_1349_);
lean_closure_set(v___f_1355_, 6, v___f_1354_);
v___x_1356_ = lean_apply_4(v_toBind_1349_, lean_box(0), lean_box(0), v_getEnv_1350_, v___f_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore(lean_object* v_m_1357_, lean_object* v_inst_1358_, lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_inst_1361_, lean_object* v_declName_1362_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_removeDocStringCore___redArg(v_inst_1358_, v_inst_1359_, v_inst_1360_, v_declName_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___boxed(lean_object* v_m_1364_, lean_object* v_inst_1365_, lean_object* v_inst_1366_, lean_object* v_inst_1367_, lean_object* v_inst_1368_, lean_object* v_declName_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_removeDocStringCore(v_m_1364_, v_inst_1365_, v_inst_1366_, v_inst_1367_, v_inst_1368_, v_declName_1369_);
lean_dec(v_inst_1368_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___redArg(lean_object* v_inst_1371_, lean_object* v_inst_1372_, lean_object* v_inst_1373_, lean_object* v_declName_1374_, lean_object* v_docString_x3f_1375_){
_start:
{
if (lean_obj_tag(v_docString_x3f_1375_) == 0)
{
lean_object* v_toApplicative_1376_; lean_object* v_toPure_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v_toApplicative_1376_ = lean_ctor_get(v_inst_1371_, 0);
lean_inc_ref(v_toApplicative_1376_);
lean_dec(v_declName_1374_);
lean_dec_ref(v_inst_1373_);
lean_dec_ref(v_inst_1372_);
lean_dec_ref(v_inst_1371_);
v_toPure_1377_ = lean_ctor_get(v_toApplicative_1376_, 1);
lean_inc(v_toPure_1377_);
lean_dec_ref(v_toApplicative_1376_);
v___x_1378_ = lean_box(0);
v___x_1379_ = lean_apply_2(v_toPure_1377_, lean_box(0), v___x_1378_);
return v___x_1379_;
}
else
{
lean_object* v_val_1380_; lean_object* v___x_1381_; 
v_val_1380_ = lean_ctor_get(v_docString_x3f_1375_, 0);
lean_inc(v_val_1380_);
lean_dec_ref_known(v_docString_x3f_1375_, 1);
v___x_1381_ = l_Lean_addDocStringCore___redArg(v_inst_1371_, v_inst_1372_, v_inst_1373_, v_declName_1374_, v_val_1380_);
return v___x_1381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27(lean_object* v_m_1382_, lean_object* v_inst_1383_, lean_object* v_inst_1384_, lean_object* v_inst_1385_, lean_object* v_inst_1386_, lean_object* v_declName_1387_, lean_object* v_docString_x3f_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_addDocStringCore_x27___redArg(v_inst_1383_, v_inst_1384_, v_inst_1385_, v_declName_1387_, v_docString_x3f_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___boxed(lean_object* v_m_1390_, lean_object* v_inst_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_inst_1394_, lean_object* v_declName_1395_, lean_object* v_docString_x3f_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_addDocStringCore_x27(v_m_1390_, v_inst_1391_, v_inst_1392_, v_inst_1393_, v_inst_1394_, v_declName_1395_, v_docString_x3f_1396_);
lean_dec(v_inst_1394_);
return v_res_1397_;
}
}
lean_object* l_Lean_findInternalDocString_x3f(lean_object* v_env_1398_, lean_object* v_declName_1399_, uint8_t v_includeBuiltin_1400_){
_start:
{
lean_object* v_md_1403_; lean_object* v_v_1408_; lean_object* v___x_1415_; lean_object* v_toEnvExtension_1416_; lean_object* v_asyncMode_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; 
v___x_1415_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1416_ = lean_ctor_get(v___x_1415_, 0);
v_asyncMode_1417_ = lean_ctor_get(v_toEnvExtension_1416_, 2);
v___x_1418_ = lean_box(0);
v___x_1419_ = 1;
lean_inc(v_declName_1399_);
lean_inc_ref(v_env_1398_);
v___x_1420_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1418_, v___x_1415_, v_env_1398_, v_declName_1399_, v_asyncMode_1417_, v___x_1419_);
if (lean_obj_tag(v___x_1420_) == 1)
{
lean_object* v_val_1421_; 
lean_dec(v_declName_1399_);
v_val_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_val_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v_declName_1399_ = v_val_1421_;
goto _start;
}
else
{
lean_object* v___x_1423_; lean_object* v_toEnvExtension_1424_; lean_object* v_asyncMode_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec(v___x_1420_);
v___x_1423_ = l_Lean_docStringExt;
v_toEnvExtension_1424_ = lean_ctor_get(v___x_1423_, 0);
v_asyncMode_1425_ = lean_ctor_get(v_toEnvExtension_1424_, 2);
v___x_1426_ = ((lean_object*)(l_Lean_throwIfHasDocString___redArg___closed__0));
lean_inc(v_declName_1399_);
lean_inc_ref(v_env_1398_);
v___x_1427_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1426_, v___x_1423_, v_env_1398_, v_declName_1399_, v_asyncMode_1425_, v___x_1419_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v___x_1428_; lean_object* v_toEnvExtension_1429_; lean_object* v_asyncMode_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1428_ = l_Lean_versoDocStringExt;
v_toEnvExtension_1429_ = lean_ctor_get(v___x_1428_, 0);
v_asyncMode_1430_ = lean_ctor_get(v_toEnvExtension_1429_, 2);
v___x_1431_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default));
lean_inc(v_declName_1399_);
v___x_1432_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1431_, v___x_1428_, v_env_1398_, v_declName_1399_, v_asyncMode_1430_, v___x_1419_);
if (lean_obj_tag(v___x_1432_) == 0)
{
if (v_includeBuiltin_1400_ == 0)
{
lean_dec(v_declName_1399_);
goto v___jp_1412_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1434_ = lean_st_ref_get(v___x_1433_);
v___x_1435_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1434_, v_declName_1399_);
lean_dec(v___x_1434_);
if (lean_obj_tag(v___x_1435_) == 1)
{
lean_object* v_val_1436_; 
lean_dec(v_declName_1399_);
v_val_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_val_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v_md_1403_ = v_val_1436_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_dec(v___x_1435_);
v___x_1437_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1438_ = lean_st_ref_get(v___x_1437_);
v___x_1439_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1438_, v_declName_1399_);
lean_dec(v_declName_1399_);
lean_dec(v___x_1438_);
if (lean_obj_tag(v___x_1439_) == 1)
{
lean_object* v_val_1440_; 
v_val_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_val_1440_);
lean_dec_ref_known(v___x_1439_, 1);
v_v_1408_ = v_val_1440_;
goto v___jp_1407_;
}
else
{
lean_dec(v___x_1439_);
goto v___jp_1412_;
}
}
}
}
else
{
lean_object* v_val_1441_; 
lean_dec(v_declName_1399_);
v_val_1441_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_val_1441_);
lean_dec_ref_known(v___x_1432_, 1);
v_v_1408_ = v_val_1441_;
goto v___jp_1407_;
}
}
else
{
lean_object* v_val_1442_; 
lean_dec(v_declName_1399_);
lean_dec_ref(v_env_1398_);
v_val_1442_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_val_1442_);
lean_dec_ref_known(v___x_1427_, 1);
v_md_1403_ = v_val_1442_;
goto v___jp_1402_;
}
}
v___jp_1402_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1404_, 0, v_md_1403_);
v___x_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
return v___x_1406_;
}
v___jp_1407_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1409_, 0, v_v_1408_);
v___x_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
return v___x_1411_;
}
v___jp_1412_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_box(0);
v___x_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
return v___x_1414_;
}
}
}
LEAN_EXPORT void l_Lean_findInternalDocString_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1398_ = stack[0].m_obj;
lean_object* v_declName_1399_ = stack[1].m_obj;
uint8_t v_includeBuiltin_1400_ = stack[2].m_num;
lean_object* v_res_1443_;
v_res_1443_ = l_Lean_findInternalDocString_x3f(v_env_1398_, v_declName_1399_, v_includeBuiltin_1400_);
stack->m_obj
 = v_res_1443_;
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f___boxed(lean_object* v_env_1444_, lean_object* v_declName_1445_, lean_object* v_includeBuiltin_1446_, lean_object* v_a_1447_){
_start:
{
uint8_t v_includeBuiltin_boxed_1448_; lean_object* v_res_1449_; 
v_includeBuiltin_boxed_1448_ = lean_unbox(v_includeBuiltin_1446_);
v_res_1449_ = l_Lean_findInternalDocString_x3f(v_env_1444_, v_declName_1445_, v_includeBuiltin_boxed_1448_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__0(lean_object* v_declName_1450_, lean_object* v_target_1451_, lean_object* v_x_1452_){
_start:
{
lean_object* v___x_1453_; uint8_t v___x_1454_; lean_object* v___x_1455_; 
v___x_1453_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v___x_1454_ = 0;
v___x_1455_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1453_, v_x_1452_, v_declName_1450_, v_target_1451_, v___x_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__1(lean_object* v_declName_1456_, lean_object* v_val_1457_, lean_object* v_x_1458_){
_start:
{
lean_object* v___x_1459_; uint8_t v___x_1460_; lean_object* v___x_1461_; 
v___x_1459_ = l_Lean_docStringExt;
v___x_1460_ = 0;
v___x_1461_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1459_, v_x_1458_, v_declName_1456_, v_val_1457_, v___x_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__2(lean_object* v_declName_1462_, lean_object* v_val_1463_, lean_object* v_x_1464_){
_start:
{
lean_object* v___x_1465_; uint8_t v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = l_Lean_versoDocStringExt;
v___x_1466_ = 0;
v___x_1467_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1465_, v_x_1464_, v_declName_1462_, v_val_1463_, v___x_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__3(lean_object* v_modifyEnv_1468_, lean_object* v___f_1469_, lean_object* v_declName_1470_, lean_object* v_____do__lift_1471_){
_start:
{
if (lean_obj_tag(v_____do__lift_1471_) == 0)
{
lean_object* v___x_1472_; 
lean_dec(v_declName_1470_);
v___x_1472_ = lean_apply_1(v_modifyEnv_1468_, v___f_1469_);
return v___x_1472_;
}
else
{
lean_object* v_val_1473_; 
lean_dec_ref(v___f_1469_);
v_val_1473_ = lean_ctor_get(v_____do__lift_1471_, 0);
lean_inc(v_val_1473_);
lean_dec_ref_known(v_____do__lift_1471_, 1);
if (lean_obj_tag(v_val_1473_) == 0)
{
lean_object* v_val_1474_; lean_object* v___f_1475_; lean_object* v___x_1476_; 
v_val_1474_ = lean_ctor_get(v_val_1473_, 0);
lean_inc(v_val_1474_);
lean_dec_ref_known(v_val_1473_, 1);
v___f_1475_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1475_, 0, v_declName_1470_);
lean_closure_set(v___f_1475_, 1, v_val_1474_);
v___x_1476_ = lean_apply_1(v_modifyEnv_1468_, v___f_1475_);
return v___x_1476_;
}
else
{
lean_object* v_val_1477_; lean_object* v___f_1478_; lean_object* v___x_1479_; 
v_val_1477_ = lean_ctor_get(v_val_1473_, 0);
lean_inc(v_val_1477_);
lean_dec_ref_known(v_val_1473_, 1);
v___f_1478_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1478_, 0, v_declName_1470_);
lean_closure_set(v___f_1478_, 1, v_val_1477_);
v___x_1479_ = lean_apply_1(v_modifyEnv_1468_, v___f_1478_);
return v___x_1479_;
}
}
}
}
lean_object* l_Lean_addInheritedDocString___redArg___lam__4(lean_object* v_declName_1480_, lean_object* v_target_1481_, uint8_t v___y_1482_, lean_object* v_x_1483_){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v___x_1485_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1484_, v_x_1483_, v_declName_1480_, v_target_1481_, v___y_1482_);
return v___x_1485_;
}
}
LEAN_EXPORT void l_Lean_addInheritedDocString___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1480_ = stack[0].m_obj;
lean_object* v_target_1481_ = stack[1].m_obj;
uint8_t v___y_1482_ = stack[2].m_num;
lean_object* v_x_1483_ = stack[3].m_obj;
lean_object* v_res_1486_;
v_res_1486_ = l_Lean_addInheritedDocString___redArg___lam__4(v_declName_1480_, v_target_1481_, v___y_1482_, v_x_1483_);
stack->m_obj
 = v_res_1486_;
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__4___boxed(lean_object* v_declName_1487_, lean_object* v_target_1488_, lean_object* v___y_1489_, lean_object* v_x_1490_){
_start:
{
uint8_t v___y_646__boxed_1491_; lean_object* v_res_1492_; 
v___y_646__boxed_1491_ = lean_unbox(v___y_1489_);
v_res_1492_ = l_Lean_addInheritedDocString___redArg___lam__4(v_declName_1487_, v_target_1488_, v___y_646__boxed_1491_, v_x_1490_);
return v_res_1492_;
}
}
lean_object* l_Lean_addInheritedDocString___redArg___lam__5(lean_object* v_target_1493_, uint8_t v___x_1494_, lean_object* v_inst_1495_, lean_object* v_toBind_1496_, lean_object* v___f_1497_, lean_object* v_____do__lift_1498_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1499_ = lean_box(v___x_1494_);
v___x_1500_ = lean_alloc_closure((void*)(l_Lean_findInternalDocString_x3f___boxed), 4, 3);
lean_closure_set(v___x_1500_, 0, v_____do__lift_1498_);
lean_closure_set(v___x_1500_, 1, v_target_1493_);
lean_closure_set(v___x_1500_, 2, v___x_1499_);
v___x_1501_ = lean_apply_2(v_inst_1495_, lean_box(0), v___x_1500_);
v___x_1502_ = lean_apply_4(v_toBind_1496_, lean_box(0), lean_box(0), v___x_1501_, v___f_1497_);
return v___x_1502_;
}
}
LEAN_EXPORT void l_Lean_addInheritedDocString___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_target_1493_ = stack[0].m_obj;
uint8_t v___x_1494_ = stack[1].m_num;
lean_object* v_inst_1495_ = stack[2].m_obj;
lean_object* v_toBind_1496_ = stack[3].m_obj;
lean_object* v___f_1497_ = stack[4].m_obj;
lean_object* v_____do__lift_1498_ = stack[5].m_obj;
lean_object* v_res_1503_;
v_res_1503_ = l_Lean_addInheritedDocString___redArg___lam__5(v_target_1493_, v___x_1494_, v_inst_1495_, v_toBind_1496_, v___f_1497_, v_____do__lift_1498_);
stack->m_obj
 = v_res_1503_;
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5___boxed(lean_object* v_target_1504_, lean_object* v___x_1505_, lean_object* v_inst_1506_, lean_object* v_toBind_1507_, lean_object* v___f_1508_, lean_object* v_____do__lift_1509_){
_start:
{
uint8_t v___x_662__boxed_1510_; lean_object* v_res_1511_; 
v___x_662__boxed_1510_ = lean_unbox(v___x_1505_);
v_res_1511_ = l_Lean_addInheritedDocString___redArg___lam__5(v_target_1504_, v___x_662__boxed_1510_, v_inst_1506_, v_toBind_1507_, v___f_1508_, v_____do__lift_1509_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__6(lean_object* v_declName_1512_, lean_object* v_target_1513_, lean_object* v_modifyEnv_1514_, lean_object* v_inst_1515_, lean_object* v_toBind_1516_, lean_object* v___f_1517_, lean_object* v_getEnv_1518_, lean_object* v_____r_1519_){
_start:
{
uint8_t v___y_1521_; uint8_t v___x_1525_; 
v___x_1525_ = l_Lean_isPrivateName(v_declName_1512_);
if (v___x_1525_ == 0)
{
uint8_t v___x_1526_; 
v___x_1526_ = l_Lean_isPrivateName(v_target_1513_);
if (v___x_1526_ == 0)
{
lean_dec(v_getEnv_1518_);
lean_dec(v___f_1517_);
lean_dec(v_toBind_1516_);
lean_dec(v_inst_1515_);
v___y_1521_ = v___x_1526_;
goto v___jp_1520_;
}
else
{
lean_object* v___x_1527_; lean_object* v___f_1528_; lean_object* v___x_1529_; 
lean_dec(v_modifyEnv_1514_);
lean_dec(v_declName_1512_);
v___x_1527_ = lean_box(v___x_1526_);
lean_inc(v_toBind_1516_);
v___f_1528_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_1528_, 0, v_target_1513_);
lean_closure_set(v___f_1528_, 1, v___x_1527_);
lean_closure_set(v___f_1528_, 2, v_inst_1515_);
lean_closure_set(v___f_1528_, 3, v_toBind_1516_);
lean_closure_set(v___f_1528_, 4, v___f_1517_);
v___x_1529_ = lean_apply_4(v_toBind_1516_, lean_box(0), lean_box(0), v_getEnv_1518_, v___f_1528_);
return v___x_1529_;
}
}
else
{
uint8_t v___x_1530_; 
lean_dec(v_getEnv_1518_);
lean_dec(v___f_1517_);
lean_dec(v_toBind_1516_);
lean_dec(v_inst_1515_);
v___x_1530_ = 0;
v___y_1521_ = v___x_1530_;
goto v___jp_1520_;
}
v___jp_1520_:
{
lean_object* v___x_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; 
v___x_1522_ = lean_box(v___y_1521_);
v___f_1523_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_1523_, 0, v_declName_1512_);
lean_closure_set(v___f_1523_, 1, v_target_1513_);
lean_closure_set(v___f_1523_, 2, v___x_1522_);
v___x_1524_ = lean_apply_1(v_modifyEnv_1514_, v___f_1523_);
return v___x_1524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__7(lean_object* v___f_1531_, lean_object* v_____r_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_apply_1(v___f_1531_, v_____r_1532_);
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__8___closed__1(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__8___closed__0));
v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__8(lean_object* v___x_1537_, lean_object* v_target_1538_, lean_object* v_declName_1539_, lean_object* v___x_1540_, lean_object* v___f_1541_, lean_object* v_inst_1542_, lean_object* v_inst_1543_, lean_object* v_toBind_1544_, lean_object* v___f_1545_, lean_object* v_____do__lift_1546_){
_start:
{
lean_object* v___x_1547_; lean_object* v_toEnvExtension_1548_; lean_object* v_asyncMode_1549_; uint8_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1547_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1548_ = lean_ctor_get(v___x_1547_, 0);
v_asyncMode_1549_ = lean_ctor_get(v_toEnvExtension_1548_, 2);
v___x_1550_ = 1;
v___x_1551_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1537_, v___x_1547_, v_____do__lift_1546_, v_target_1538_, v_asyncMode_1549_, v___x_1550_);
v___x_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1552_, 0, v_declName_1539_);
v___x_1553_ = l_instBEqOption_beq___redArg(v___x_1540_, v___x_1551_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
lean_dec(v___f_1545_);
lean_dec(v_toBind_1544_);
lean_dec_ref(v_inst_1543_);
lean_dec_ref(v_inst_1542_);
v___x_1554_ = lean_box(0);
v___x_1555_ = lean_apply_1(v___f_1541_, v___x_1554_);
return v___x_1555_;
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_dec(v___f_1541_);
v___x_1556_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__8___closed__1, &l_Lean_addInheritedDocString___redArg___lam__8___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__8___closed__1);
v___x_1557_ = l_Lean_throwError___redArg(v_inst_1542_, v_inst_1543_, v___x_1556_);
v___x_1558_ = lean_apply_4(v_toBind_1544_, lean_box(0), lean_box(0), v___x_1557_, v___f_1545_);
return v___x_1558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__9(lean_object* v_toBind_1559_, lean_object* v_getEnv_1560_, lean_object* v___f_1561_, lean_object* v_____r_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = lean_apply_4(v_toBind_1559_, lean_box(0), lean_box(0), v_getEnv_1560_, v___f_1561_);
return v___x_1563_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__10___closed__0));
v___x_1566_ = l_Lean_stringToMessageData(v___x_1565_);
return v___x_1566_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__10___closed__3(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__10___closed__2));
v___x_1569_ = l_Lean_stringToMessageData(v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__10(lean_object* v___x_1570_, lean_object* v_declName_1571_, lean_object* v_toBind_1572_, lean_object* v_getEnv_1573_, lean_object* v___f_1574_, lean_object* v_inst_1575_, lean_object* v_inst_1576_, lean_object* v___f_1577_, lean_object* v_____do__lift_1578_){
_start:
{
lean_object* v___x_1579_; lean_object* v_toEnvExtension_1580_; lean_object* v_asyncMode_1581_; uint8_t v___x_1582_; lean_object* v___x_1583_; 
v___x_1579_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1580_ = lean_ctor_get(v___x_1579_, 0);
v_asyncMode_1581_ = lean_ctor_get(v_toEnvExtension_1580_, 2);
v___x_1582_ = 1;
lean_inc(v_declName_1571_);
v___x_1583_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1570_, v___x_1579_, v_____do__lift_1578_, v_declName_1571_, v_asyncMode_1581_, v___x_1582_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v___x_1584_; 
lean_dec(v___f_1577_);
lean_dec_ref(v_inst_1576_);
lean_dec_ref(v_inst_1575_);
lean_dec(v_declName_1571_);
v___x_1584_ = lean_apply_4(v_toBind_1572_, lean_box(0), lean_box(0), v_getEnv_1573_, v___f_1574_);
return v___x_1584_;
}
else
{
lean_object* v___x_1585_; uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_dec_ref_known(v___x_1583_, 1);
lean_dec(v___f_1574_);
lean_dec(v_getEnv_1573_);
v___x_1585_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__10___closed__1, &l_Lean_addInheritedDocString___redArg___lam__10___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__10___closed__1);
v___x_1586_ = 0;
v___x_1587_ = l_Lean_MessageData_ofConstName(v_declName_1571_, v___x_1586_);
v___x_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1585_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__10___closed__3, &l_Lean_addInheritedDocString___redArg___lam__10___closed__3_once, _init_l_Lean_addInheritedDocString___redArg___lam__10___closed__3);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = l_Lean_throwError___redArg(v_inst_1575_, v_inst_1576_, v___x_1590_);
v___x_1592_ = lean_apply_4(v_toBind_1572_, lean_box(0), lean_box(0), v___x_1591_, v___f_1577_);
return v___x_1592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__12(lean_object* v_declName_1593_, lean_object* v_toBind_1594_, lean_object* v_getEnv_1595_, lean_object* v___f_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v___f_1599_, lean_object* v_____do__lift_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1600_, v_declName_1593_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v___x_1602_; 
lean_dec(v___f_1599_);
lean_dec_ref(v_inst_1598_);
lean_dec_ref(v_inst_1597_);
lean_dec(v_declName_1593_);
v___x_1602_ = lean_apply_4(v_toBind_1594_, lean_box(0), lean_box(0), v_getEnv_1595_, v___f_1596_);
return v___x_1602_;
}
else
{
uint8_t v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_dec_ref_known(v___x_1601_, 1);
lean_dec(v___f_1596_);
lean_dec(v_getEnv_1595_);
v___x_1603_ = 0;
v___x_1604_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__10___closed__1, &l_Lean_addInheritedDocString___redArg___lam__10___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__10___closed__1);
v___x_1605_ = l_Lean_MessageData_ofConstName(v_declName_1593_, v___x_1603_);
v___x_1606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1604_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__1, &l_Lean_addDocStringCore___redArg___lam__2___closed__1_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1);
v___x_1608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = l_Lean_throwError___redArg(v_inst_1597_, v_inst_1598_, v___x_1608_);
v___x_1610_ = lean_apply_4(v_toBind_1594_, lean_box(0), lean_box(0), v___x_1609_, v___f_1599_);
return v___x_1610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__12___boxed(lean_object* v_declName_1611_, lean_object* v_toBind_1612_, lean_object* v_getEnv_1613_, lean_object* v___f_1614_, lean_object* v_inst_1615_, lean_object* v_inst_1616_, lean_object* v___f_1617_, lean_object* v_____do__lift_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_addInheritedDocString___redArg___lam__12(v_declName_1611_, v_toBind_1612_, v_getEnv_1613_, v___f_1614_, v_inst_1615_, v_inst_1616_, v___f_1617_, v_____do__lift_1618_);
lean_dec_ref(v_____do__lift_1618_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg(lean_object* v_inst_1621_, lean_object* v_inst_1622_, lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_declName_1625_, lean_object* v_target_1626_){
_start:
{
lean_object* v_toBind_1627_; lean_object* v_getEnv_1628_; lean_object* v_modifyEnv_1629_; lean_object* v___f_1630_; lean_object* v___f_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___f_1634_; lean_object* v___f_1635_; lean_object* v___f_1636_; lean_object* v___f_1637_; lean_object* v___f_1638_; lean_object* v___f_1639_; lean_object* v___f_1640_; lean_object* v___x_1641_; 
v_toBind_1627_ = lean_ctor_get(v_inst_1621_, 1);
lean_inc_n(v_toBind_1627_, 7);
v_getEnv_1628_ = lean_ctor_get(v_inst_1623_, 0);
lean_inc_n(v_getEnv_1628_, 6);
v_modifyEnv_1629_ = lean_ctor_get(v_inst_1623_, 1);
lean_inc_n(v_modifyEnv_1629_, 2);
lean_dec_ref(v_inst_1623_);
lean_inc_n(v_target_1626_, 2);
lean_inc_n(v_declName_1625_, 5);
v___f_1630_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1630_, 0, v_declName_1625_);
lean_closure_set(v___f_1630_, 1, v_target_1626_);
v___f_1631_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1631_, 0, v_modifyEnv_1629_);
lean_closure_set(v___f_1631_, 1, v___f_1630_);
lean_closure_set(v___f_1631_, 2, v_declName_1625_);
v___x_1632_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___closed__0));
v___x_1633_ = lean_box(0);
v___f_1634_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__6), 8, 7);
lean_closure_set(v___f_1634_, 0, v_declName_1625_);
lean_closure_set(v___f_1634_, 1, v_target_1626_);
lean_closure_set(v___f_1634_, 2, v_modifyEnv_1629_);
lean_closure_set(v___f_1634_, 3, v_inst_1624_);
lean_closure_set(v___f_1634_, 4, v_toBind_1627_);
lean_closure_set(v___f_1634_, 5, v___f_1631_);
lean_closure_set(v___f_1634_, 6, v_getEnv_1628_);
lean_inc_ref(v___f_1634_);
v___f_1635_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__7), 2, 1);
lean_closure_set(v___f_1635_, 0, v___f_1634_);
lean_inc_ref_n(v_inst_1622_, 2);
lean_inc_ref_n(v_inst_1621_, 2);
v___f_1636_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__8), 10, 9);
lean_closure_set(v___f_1636_, 0, v___x_1633_);
lean_closure_set(v___f_1636_, 1, v_target_1626_);
lean_closure_set(v___f_1636_, 2, v_declName_1625_);
lean_closure_set(v___f_1636_, 3, v___x_1632_);
lean_closure_set(v___f_1636_, 4, v___f_1634_);
lean_closure_set(v___f_1636_, 5, v_inst_1621_);
lean_closure_set(v___f_1636_, 6, v_inst_1622_);
lean_closure_set(v___f_1636_, 7, v_toBind_1627_);
lean_closure_set(v___f_1636_, 8, v___f_1635_);
lean_inc_ref(v___f_1636_);
v___f_1637_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__9), 4, 3);
lean_closure_set(v___f_1637_, 0, v_toBind_1627_);
lean_closure_set(v___f_1637_, 1, v_getEnv_1628_);
lean_closure_set(v___f_1637_, 2, v___f_1636_);
v___f_1638_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__10), 9, 8);
lean_closure_set(v___f_1638_, 0, v___x_1633_);
lean_closure_set(v___f_1638_, 1, v_declName_1625_);
lean_closure_set(v___f_1638_, 2, v_toBind_1627_);
lean_closure_set(v___f_1638_, 3, v_getEnv_1628_);
lean_closure_set(v___f_1638_, 4, v___f_1636_);
lean_closure_set(v___f_1638_, 5, v_inst_1621_);
lean_closure_set(v___f_1638_, 6, v_inst_1622_);
lean_closure_set(v___f_1638_, 7, v___f_1637_);
lean_inc_ref(v___f_1638_);
v___f_1639_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__9), 4, 3);
lean_closure_set(v___f_1639_, 0, v_toBind_1627_);
lean_closure_set(v___f_1639_, 1, v_getEnv_1628_);
lean_closure_set(v___f_1639_, 2, v___f_1638_);
v___f_1640_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__12___boxed), 8, 7);
lean_closure_set(v___f_1640_, 0, v_declName_1625_);
lean_closure_set(v___f_1640_, 1, v_toBind_1627_);
lean_closure_set(v___f_1640_, 2, v_getEnv_1628_);
lean_closure_set(v___f_1640_, 3, v___f_1638_);
lean_closure_set(v___f_1640_, 4, v_inst_1621_);
lean_closure_set(v___f_1640_, 5, v_inst_1622_);
lean_closure_set(v___f_1640_, 6, v___f_1639_);
v___x_1641_ = lean_apply_4(v_toBind_1627_, lean_box(0), lean_box(0), v_getEnv_1628_, v___f_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString(lean_object* v_m_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_inst_1646_, lean_object* v_declName_1647_, lean_object* v_target_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_addInheritedDocString___redArg(v_inst_1643_, v_inst_1644_, v_inst_1645_, v_inst_1646_, v_declName_1647_, v_target_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v_es_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_array_mk(v_es_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v_x_1654_, lean_object* v_x_1655_, lean_object* v_es_1656_){
_start:
{
lean_object* v_ents_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v_ents_1657_ = lean_array_mk(v_es_1656_);
v___x_1658_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_));
lean_inc_ref(v_ents_1657_);
v___x_1659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_ctor_set(v___x_1659_, 1, v_ents_1657_);
lean_ctor_set(v___x_1659_, 2, v_ents_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v_x_1660_, lean_object* v_x_1661_, lean_object* v_es_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(v_x_1660_, v_x_1661_, v_es_1662_);
lean_dec_ref(v_x_1661_);
lean_dec_ref(v_x_1660_);
return v_res_1663_;
}
}
static lean_object* _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = lean_unsigned_to_nat(32u);
v___x_1665_ = lean_mk_empty_array_with_capacity(v___x_1664_);
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v___x_1667_, lean_object* v_x_1668_){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; size_t v___x_1672_; lean_object* v___x_1673_; 
v___x_1669_ = lean_unsigned_to_nat(32u);
v___x_1670_ = lean_mk_empty_array_with_capacity(v___x_1669_);
v___x_1671_ = lean_obj_once(&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_, &l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_);
v___x_1672_ = ((size_t)5ULL);
lean_inc(v___x_1667_);
v___x_1673_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v___x_1670_);
lean_ctor_set(v___x_1673_, 2, v___x_1667_);
lean_ctor_set(v___x_1673_, 3, v___x_1667_);
lean_ctor_set_usize(v___x_1673_, 4, v___x_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v___x_1674_, lean_object* v_x_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(v___x_1674_, v_x_1675_);
lean_dec_ref(v_x_1675_);
return v_res_1676_;
}
}
lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_));
v___x_1699_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1700_;
v_res_1700_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1700_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v_a_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_();
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMainModuleDoc___lam__0(lean_object* v___x_1703_, lean_object* v_doc_1704_, lean_object* v_s_1705_){
_start:
{
lean_object* v_addEntryFn_1706_; lean_object* v_importedEntries_1707_; lean_object* v_state_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1716_; 
v_addEntryFn_1706_ = lean_ctor_get(v___x_1703_, 3);
lean_inc(v_addEntryFn_1706_);
lean_dec_ref(v___x_1703_);
v_importedEntries_1707_ = lean_ctor_get(v_s_1705_, 0);
v_state_1708_ = lean_ctor_get(v_s_1705_, 1);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_s_1705_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1710_ = v_s_1705_;
v_isShared_1711_ = v_isSharedCheck_1716_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_state_1708_);
lean_inc(v_importedEntries_1707_);
lean_dec(v_s_1705_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1716_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v_state_1712_; lean_object* v___x_1714_; 
v_state_1712_ = lean_apply_2(v_addEntryFn_1706_, v_state_1708_, v_doc_1704_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 1, v_state_1712_);
v___x_1714_ = v___x_1710_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_importedEntries_1707_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_state_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMainModuleDoc(lean_object* v_env_1717_, lean_object* v_doc_1718_){
_start:
{
lean_object* v___x_1719_; lean_object* v_toEnvExtension_1720_; lean_object* v_asyncMode_1721_; uint8_t v_logWrites_1722_; lean_object* v___f_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v___x_1719_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_1720_ = lean_ctor_get(v___x_1719_, 0);
v_asyncMode_1721_ = lean_ctor_get(v_toEnvExtension_1720_, 2);
v_logWrites_1722_ = lean_ctor_get_uint8(v_toEnvExtension_1720_, sizeof(void*)*6);
v___f_1723_ = lean_alloc_closure((void*)(l_Lean_addMainModuleDoc___lam__0), 3, 2);
lean_closure_set(v___f_1723_, 0, v___x_1719_);
lean_closure_set(v___f_1723_, 1, v_doc_1718_);
v___x_1724_ = lean_box(0);
v___x_1725_ = 1;
if (v_logWrites_1722_ == 0)
{
lean_object* v___x_1726_; 
lean_inc_ref(v_toEnvExtension_1720_);
v___x_1726_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1720_, v_env_1717_, v___f_1723_, v_asyncMode_1721_, v___x_1724_, v___x_1725_);
return v___x_1726_;
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
lean_inc_ref_n(v_toEnvExtension_1720_, 2);
v___x_1727_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1720_, v_env_1717_);
lean_dec_ref(v_env_1717_);
v___x_1728_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1720_, v___x_1727_, v___f_1723_, v_asyncMode_1721_, v___x_1724_, v___x_1725_);
return v___x_1728_;
}
}
}
static lean_object* _init_l_Lean_getMainModuleDoc___closed__0(void){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModuleDoc(lean_object* v_env_1730_){
_start:
{
lean_object* v___x_1731_; lean_object* v_toEnvExtension_1732_; lean_object* v_asyncMode_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1731_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_1732_ = lean_ctor_get(v___x_1731_, 0);
v_asyncMode_1733_ = lean_ctor_get(v_toEnvExtension_1732_, 2);
v___x_1734_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_1735_ = lean_box(0);
v___x_1736_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1734_, v___x_1731_, v_env_1730_, v_asyncMode_1733_, v___x_1735_);
return v___x_1736_;
}
}
static lean_object* _init_l_Lean_getModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1737_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_1738_ = lean_box(0);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
lean_ctor_set(v___x_1739_, 1, v___x_1737_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f(lean_object* v_env_1740_, lean_object* v_moduleName_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_Environment_getModuleIdx_x3f(v_env_1740_, v_moduleName_1741_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v___x_1743_; 
v___x_1743_ = lean_box(0);
return v___x_1743_;
}
else
{
lean_object* v_val_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1755_; 
v_val_1744_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1746_ = v___x_1742_;
v_isShared_1747_ = v_isSharedCheck_1755_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_val_1744_);
lean_dec(v___x_1742_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1755_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1748_ = lean_obj_once(&l_Lean_getModuleDoc_x3f___closed__0, &l_Lean_getModuleDoc_x3f___closed__0_once, _init_l_Lean_getModuleDoc_x3f___closed__0);
v___x_1749_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v___x_1750_ = 1;
v___x_1751_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1748_, v___x_1749_, v_env_1740_, v_val_1744_, v___x_1750_);
lean_dec(v_val_1744_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1751_);
v___x_1753_ = v___x_1746_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f___boxed(lean_object* v_env_1756_, lean_object* v_moduleName_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_getModuleDoc_x3f(v_env_1756_, v_moduleName_1757_);
lean_dec(v_moduleName_1757_);
lean_dec_ref(v_env_1756_);
return v_res_1758_;
}
}
static lean_object* _init_l_Lean_getDocStringText___redArg___closed__1(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__0));
v___x_1761_ = l_Lean_stringToMessageData(v___x_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___redArg(lean_object* v_inst_1765_, lean_object* v_inst_1766_, lean_object* v_stx_1767_){
_start:
{
lean_object* v_toApplicative_1774_; lean_object* v_toPure_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_toApplicative_1774_ = lean_ctor_get(v_inst_1765_, 0);
v_toPure_1775_ = lean_ctor_get(v_toApplicative_1774_, 1);
v___x_1776_ = lean_unsigned_to_nat(1u);
v___x_1777_ = l_Lean_Syntax_getArg(v_stx_1767_, v___x_1776_);
if (lean_obj_tag(v___x_1777_) == 1)
{
lean_object* v_kind_1778_; 
v_kind_1778_ = lean_ctor_get(v___x_1777_, 1);
lean_inc(v_kind_1778_);
if (lean_obj_tag(v_kind_1778_) == 1)
{
lean_object* v_pre_1779_; 
v_pre_1779_ = lean_ctor_get(v_kind_1778_, 0);
lean_inc(v_pre_1779_);
if (lean_obj_tag(v_pre_1779_) == 1)
{
lean_object* v_pre_1780_; 
v_pre_1780_ = lean_ctor_get(v_pre_1779_, 0);
lean_inc(v_pre_1780_);
if (lean_obj_tag(v_pre_1780_) == 1)
{
lean_object* v_pre_1781_; 
v_pre_1781_ = lean_ctor_get(v_pre_1780_, 0);
lean_inc(v_pre_1781_);
if (lean_obj_tag(v_pre_1781_) == 1)
{
lean_object* v_pre_1782_; 
v_pre_1782_ = lean_ctor_get(v_pre_1781_, 0);
if (lean_obj_tag(v_pre_1782_) == 0)
{
lean_object* v_args_1783_; lean_object* v_str_1784_; lean_object* v_str_1785_; lean_object* v_str_1786_; lean_object* v_str_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v_args_1783_ = lean_ctor_get(v___x_1777_, 2);
lean_inc_ref(v_args_1783_);
lean_dec_ref_known(v___x_1777_, 3);
v_str_1784_ = lean_ctor_get(v_kind_1778_, 1);
lean_inc_ref(v_str_1784_);
lean_dec_ref_known(v_kind_1778_, 2);
v_str_1785_ = lean_ctor_get(v_pre_1779_, 1);
lean_inc_ref(v_str_1785_);
lean_dec_ref_known(v_pre_1779_, 2);
v_str_1786_ = lean_ctor_get(v_pre_1780_, 1);
lean_inc_ref(v_str_1786_);
lean_dec_ref_known(v_pre_1780_, 2);
v_str_1787_ = lean_ctor_get(v_pre_1781_, 1);
lean_inc_ref(v_str_1787_);
lean_dec_ref_known(v_pre_1781_, 2);
v___x_1788_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_1789_ = lean_string_dec_eq(v_str_1787_, v___x_1788_);
lean_dec_ref(v_str_1787_);
if (v___x_1789_ == 0)
{
lean_dec_ref(v_str_1786_);
lean_dec_ref(v_str_1785_);
lean_dec_ref(v_str_1784_);
lean_dec_ref(v_args_1783_);
goto v___jp_1768_;
}
else
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__2));
v___x_1791_ = lean_string_dec_eq(v_str_1786_, v___x_1790_);
lean_dec_ref(v_str_1786_);
if (v___x_1791_ == 0)
{
lean_dec_ref(v_str_1785_);
lean_dec_ref(v_str_1784_);
lean_dec_ref(v_args_1783_);
goto v___jp_1768_;
}
else
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__3));
v___x_1793_ = lean_string_dec_eq(v_str_1785_, v___x_1792_);
lean_dec_ref(v_str_1785_);
if (v___x_1793_ == 0)
{
lean_dec_ref(v_str_1784_);
lean_dec_ref(v_args_1783_);
goto v___jp_1768_;
}
else
{
lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1794_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__4));
v___x_1795_ = lean_string_dec_eq(v_str_1784_, v___x_1794_);
lean_dec_ref(v_str_1784_);
if (v___x_1795_ == 0)
{
lean_dec_ref(v_args_1783_);
goto v___jp_1768_;
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1796_ = lean_array_get_size(v_args_1783_);
v___x_1797_ = lean_unsigned_to_nat(2u);
v___x_1798_ = lean_nat_dec_eq(v___x_1796_, v___x_1797_);
if (v___x_1798_ == 0)
{
lean_dec_ref(v_args_1783_);
goto v___jp_1768_;
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = lean_unsigned_to_nat(0u);
v___x_1800_ = lean_array_fget(v_args_1783_, v___x_1799_);
lean_dec_ref(v_args_1783_);
if (lean_obj_tag(v___x_1800_) == 2)
{
lean_object* v_val_1801_; lean_object* v___x_1802_; 
lean_inc(v_toPure_1775_);
lean_dec(v_stx_1767_);
lean_dec_ref(v_inst_1766_);
lean_dec_ref(v_inst_1765_);
v_val_1801_ = lean_ctor_get(v___x_1800_, 1);
lean_inc_ref(v_val_1801_);
lean_dec_ref_known(v___x_1800_, 2);
v___x_1802_ = lean_apply_2(v_toPure_1775_, lean_box(0), v_val_1801_);
return v___x_1802_;
}
else
{
lean_dec(v___x_1800_);
goto v___jp_1768_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1781_, 2);
lean_dec_ref_known(v_pre_1780_, 2);
lean_dec_ref_known(v_pre_1779_, 2);
lean_dec_ref_known(v_kind_1778_, 2);
lean_dec_ref_known(v___x_1777_, 3);
goto v___jp_1768_;
}
}
else
{
lean_dec(v_pre_1781_);
lean_dec_ref_known(v_pre_1780_, 2);
lean_dec_ref_known(v_pre_1779_, 2);
lean_dec_ref_known(v_kind_1778_, 2);
lean_dec_ref_known(v___x_1777_, 3);
goto v___jp_1768_;
}
}
else
{
lean_dec(v_pre_1780_);
lean_dec_ref_known(v_pre_1779_, 2);
lean_dec_ref_known(v_kind_1778_, 2);
lean_dec_ref_known(v___x_1777_, 3);
goto v___jp_1768_;
}
}
else
{
lean_dec(v_pre_1779_);
lean_dec_ref_known(v_kind_1778_, 2);
lean_dec_ref_known(v___x_1777_, 3);
goto v___jp_1768_;
}
}
else
{
lean_dec_ref_known(v___x_1777_, 3);
lean_dec(v_kind_1778_);
goto v___jp_1768_;
}
}
else
{
lean_dec(v___x_1777_);
goto v___jp_1768_;
}
v___jp_1768_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1769_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_1767_);
v___x_1770_ = l_Lean_MessageData_ofSyntax(v_stx_1767_);
v___x_1771_ = l_Lean_indentD(v___x_1770_);
v___x_1772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1769_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = l_Lean_throwErrorAt___redArg(v_inst_1765_, v_inst_1766_, v_stx_1767_, v___x_1772_);
return v___x_1773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText(lean_object* v_m_1803_, lean_object* v_inst_1804_, lean_object* v_inst_1805_, lean_object* v_stx_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lean_getDocStringText___redArg(v_inst_1804_, v_inst_1805_, v_stx_1806_);
return v___x_1807_;
}
}
uint8_t l_Lean_isVersoDocComment(lean_object* v_stx_1814_){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1815_ = lean_unsigned_to_nat(1u);
v___x_1816_ = l_Lean_Syntax_getArg(v_stx_1814_, v___x_1815_);
v___x_1817_ = ((lean_object*)(l_Lean_isVersoDocComment___closed__1));
v___x_1818_ = l_Lean_Syntax_isOfKind(v___x_1816_, v___x_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT void l_Lean_isVersoDocComment_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1814_ = stack[0].m_obj;
uint8_t v_res_1819_;
v_res_1819_ = l_Lean_isVersoDocComment(v_stx_1814_);
stack->m_num = v_res_1819_;
}
LEAN_EXPORT lean_object* l_Lean_isVersoDocComment___boxed(lean_object* v_stx_1820_){
_start:
{
uint8_t v_res_1821_; lean_object* v_r_1822_; 
v_res_1821_ = l_Lean_isVersoDocComment(v_stx_1820_);
lean_dec(v_stx_1820_);
v_r_1822_ = lean_box(v_res_1821_);
return v_r_1822_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1(void){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = l_Lean_instInhabitedDeclarationRange_default;
v___x_1826_ = ((lean_object*)(l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0));
v___x_1827_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
lean_ctor_set(v___x_1827_, 2, v___x_1825_);
return v___x_1827_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default(void){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = lean_obj_once(&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1, &l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1_once, _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet(void){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_VersoModuleDocs_instInhabitedSnippet_default;
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__2(lean_object* v_a_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = lean_nat_to_int(v_a_1830_);
return v___x_1831_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lean_unsigned_to_nat(2u);
v___x_1839_ = lean_nat_to_int(v___x_1838_);
return v___x_1839_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = lean_unsigned_to_nat(1u);
v___x_1841_ = lean_nat_to_int(v___x_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(lean_object* v_x_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_){
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
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1864_ = lean_unsigned_to_nat(0u);
v___x_1865_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_1857_, v___x_1864_);
v___x_1866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1863_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v_x_1855_ = v___x_1866_;
v_x_1856_ = v_tail_1858_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(lean_object* v_x_1870_, lean_object* v_x_1871_, lean_object* v_x_1872_){
_start:
{
if (lean_obj_tag(v_x_1872_) == 0)
{
lean_dec(v_x_1870_);
return v_x_1871_;
}
else
{
lean_object* v_head_1873_; lean_object* v_tail_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1885_; 
v_head_1873_ = lean_ctor_get(v_x_1872_, 0);
v_tail_1874_ = lean_ctor_get(v_x_1872_, 1);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_x_1872_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1876_ = v_x_1872_;
v_isShared_1877_ = v_isSharedCheck_1885_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_tail_1874_);
lean_inc(v_head_1873_);
lean_dec(v_x_1872_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1885_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
lean_inc(v_x_1870_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set_tag(v___x_1876_, 5);
lean_ctor_set(v___x_1876_, 1, v_x_1870_);
lean_ctor_set(v___x_1876_, 0, v_x_1871_);
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_x_1871_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_x_1870_);
v___x_1879_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1880_ = lean_unsigned_to_nat(0u);
v___x_1881_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_1873_, v___x_1880_);
v___x_1882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1879_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(v_x_1870_, v___x_1882_, v_tail_1874_);
return v___x_1883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_1886_, lean_object* v_x_1887_){
_start:
{
if (lean_obj_tag(v_x_1886_) == 0)
{
lean_object* v___x_1888_; 
lean_dec(v_x_1887_);
v___x_1888_ = lean_box(0);
return v___x_1888_;
}
else
{
lean_object* v_tail_1889_; 
v_tail_1889_ = lean_ctor_get(v_x_1886_, 1);
if (lean_obj_tag(v_tail_1889_) == 0)
{
lean_object* v_head_1890_; lean_object* v___x_1891_; 
lean_dec(v_x_1887_);
v_head_1890_ = lean_ctor_get(v_x_1886_, 0);
lean_inc(v_head_1890_);
lean_dec_ref_known(v_x_1886_, 2);
v___x_1891_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_1890_);
return v___x_1891_;
}
else
{
lean_object* v_head_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
lean_inc(v_tail_1889_);
v_head_1892_ = lean_ctor_get(v_x_1886_, 0);
lean_inc(v_head_1892_);
lean_dec_ref_known(v_x_1886_, 2);
v___x_1893_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_1892_);
v___x_1894_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(v_x_1887_, v___x_1893_, v_tail_1889_);
return v___x_1894_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0));
v___x_1897_ = lean_string_length(v___x_1896_);
return v___x_1897_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_1899_ = lean_nat_to_int(v___x_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_xs_1908_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v___x_1909_ = lean_array_get_size(v_xs_1908_);
v___x_1910_ = lean_unsigned_to_nat(0u);
v___x_1911_ = lean_nat_dec_eq(v___x_1909_, v___x_1910_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1912_ = lean_array_to_list(v_xs_1908_);
v___x_1913_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_1914_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_1912_, v___x_1913_);
v___x_1915_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_1916_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_1917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
lean_ctor_set(v___x_1917_, 1, v___x_1914_);
v___x_1918_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_1919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1915_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = l_Std_Format_fill(v___x_1920_);
return v___x_1921_;
}
else
{
lean_object* v___x_1922_; 
lean_dec_ref(v_xs_1908_);
v___x_1922_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_1922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_1977_, lean_object* v_prec_1978_){
_start:
{
switch(lean_obj_tag(v_x_1977_))
{
case 0:
{
lean_object* v_string_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1999_; 
v_string_1979_ = lean_ctor_get(v_x_1977_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1981_ = v_x_1977_;
v_isShared_1982_ = v_isSharedCheck_1999_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_string_1979_);
lean_dec(v_x_1977_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1999_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___y_1984_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = lean_unsigned_to_nat(1024u);
v___x_1996_ = lean_nat_dec_le(v___x_1995_, v_prec_1978_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_1984_ = v___x_1997_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_1984_ = v___x_1998_;
goto v___jp_1983_;
}
v___jp_1983_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1985_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__2));
v___x_1986_ = l_String_quote(v_string_1979_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set_tag(v___x_1981_, 3);
lean_ctor_set(v___x_1981_, 0, v___x_1986_);
v___x_1988_ = v___x_1981_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1985_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
lean_inc(v___y_1984_);
v___x_1990_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___y_1984_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = 0;
v___x_1992_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set_uint8(v___x_1992_, sizeof(void*)*1, v___x_1991_);
v___x_1993_ = l_Repr_addAppParen(v___x_1992_, v_prec_1978_);
return v___x_1993_;
}
}
}
}
case 1:
{
lean_object* v_content_2000_; lean_object* v___y_2002_; lean_object* v___x_2010_; uint8_t v___x_2011_; 
v_content_2000_ = lean_ctor_get(v_x_1977_, 0);
lean_inc_ref(v_content_2000_);
lean_dec_ref_known(v_x_1977_, 1);
v___x_2010_ = lean_unsigned_to_nat(1024u);
v___x_2011_ = lean_nat_dec_le(v___x_2010_, v_prec_1978_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; 
v___x_2012_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2002_ = v___x_2012_;
goto v___jp_2001_;
}
else
{
lean_object* v___x_2013_; 
v___x_2013_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2002_ = v___x_2013_;
goto v___jp_2001_;
}
v___jp_2001_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2003_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__7));
v___x_2004_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2000_);
v___x_2005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2003_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
lean_inc(v___y_2002_);
v___x_2006_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___y_2002_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
v___x_2007_ = 0;
v___x_2008_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2008_, 0, v___x_2006_);
lean_ctor_set_uint8(v___x_2008_, sizeof(void*)*1, v___x_2007_);
v___x_2009_ = l_Repr_addAppParen(v___x_2008_, v_prec_1978_);
return v___x_2009_;
}
}
case 2:
{
lean_object* v_content_2014_; lean_object* v___y_2016_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v_content_2014_ = lean_ctor_get(v_x_1977_, 0);
lean_inc_ref(v_content_2014_);
lean_dec_ref_known(v_x_1977_, 1);
v___x_2024_ = lean_unsigned_to_nat(1024u);
v___x_2025_ = lean_nat_dec_le(v___x_2024_, v_prec_1978_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2016_ = v___x_2026_;
goto v___jp_2015_;
}
else
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2016_ = v___x_2027_;
goto v___jp_2015_;
}
v___jp_2015_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2017_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__10));
v___x_2018_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2014_);
v___x_2019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2017_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
lean_inc(v___y_2016_);
v___x_2020_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___y_2016_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v___x_2021_ = 0;
v___x_2022_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2022_, 0, v___x_2020_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*1, v___x_2021_);
v___x_2023_ = l_Repr_addAppParen(v___x_2022_, v_prec_1978_);
return v___x_2023_;
}
}
case 3:
{
lean_object* v_string_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2048_; 
v_string_2028_ = lean_ctor_get(v_x_1977_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2030_ = v_x_1977_;
v_isShared_2031_ = v_isSharedCheck_2048_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_string_2028_);
lean_dec(v_x_1977_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2048_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___y_2033_; lean_object* v___x_2044_; uint8_t v___x_2045_; 
v___x_2044_ = lean_unsigned_to_nat(1024u);
v___x_2045_ = lean_nat_dec_le(v___x_2044_, v_prec_1978_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2033_ = v___x_2046_;
goto v___jp_2032_;
}
else
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2033_ = v___x_2047_;
goto v___jp_2032_;
}
v___jp_2032_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2034_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__13));
v___x_2035_ = l_String_quote(v_string_2028_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2035_);
v___x_2037_ = v___x_2030_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2034_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
lean_inc(v___y_2033_);
v___x_2039_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___y_2033_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
v___x_2040_ = 0;
v___x_2041_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2041_, 0, v___x_2039_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*1, v___x_2040_);
v___x_2042_ = l_Repr_addAppParen(v___x_2041_, v_prec_1978_);
return v___x_2042_;
}
}
}
}
case 4:
{
uint8_t v_mode_2049_; lean_object* v_string_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2075_; 
v_mode_2049_ = lean_ctor_get_uint8(v_x_1977_, sizeof(void*)*1);
v_string_2050_ = lean_ctor_get(v_x_1977_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2052_ = v_x_1977_;
v_isShared_2053_ = v_isSharedCheck_2075_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_string_2050_);
lean_dec(v_x_1977_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2075_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___y_2055_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = lean_unsigned_to_nat(1024u);
v___x_2072_ = lean_nat_dec_le(v___x_2071_, v_prec_1978_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2055_ = v___x_2073_;
goto v___jp_2054_;
}
else
{
lean_object* v___x_2074_; 
v___x_2074_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2055_ = v___x_2074_;
goto v___jp_2054_;
}
v___jp_2054_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; lean_object* v___x_2068_; 
v___x_2056_ = lean_box(1);
v___x_2057_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__16));
v___x_2058_ = lean_unsigned_to_nat(1024u);
v___x_2059_ = l_Lean_Doc_instReprMathMode_repr(v_mode_2049_, v___x_2058_);
v___x_2060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2057_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
lean_ctor_set(v___x_2061_, 1, v___x_2056_);
v___x_2062_ = l_String_quote(v_string_2050_);
v___x_2063_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
v___x_2064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2061_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
lean_inc(v___y_2055_);
v___x_2065_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___y_2055_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = 0;
if (v_isShared_2053_ == 0)
{
lean_ctor_set_tag(v___x_2052_, 6);
lean_ctor_set(v___x_2052_, 0, v___x_2065_);
v___x_2068_ = v___x_2052_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2065_);
v___x_2068_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; 
lean_ctor_set_uint8(v___x_2068_, sizeof(void*)*1, v___x_2066_);
v___x_2069_ = l_Repr_addAppParen(v___x_2068_, v_prec_1978_);
return v___x_2069_;
}
}
}
}
case 5:
{
lean_object* v_string_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2096_; 
v_string_2076_ = lean_ctor_get(v_x_1977_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2078_ = v_x_1977_;
v_isShared_2079_ = v_isSharedCheck_2096_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_string_2076_);
lean_dec(v_x_1977_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2096_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___y_2081_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2092_ = lean_unsigned_to_nat(1024u);
v___x_2093_ = lean_nat_dec_le(v___x_2092_, v_prec_1978_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; 
v___x_2094_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2081_ = v___x_2094_;
goto v___jp_2080_;
}
else
{
lean_object* v___x_2095_; 
v___x_2095_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2081_ = v___x_2095_;
goto v___jp_2080_;
}
v___jp_2080_:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2082_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__19));
v___x_2083_ = l_String_quote(v_string_2076_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set_tag(v___x_2078_, 3);
lean_ctor_set(v___x_2078_, 0, v___x_2083_);
v___x_2085_ = v___x_2078_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2082_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
lean_inc(v___y_2081_);
v___x_2087_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___y_2081_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v___x_2088_ = 0;
v___x_2089_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2089_, 0, v___x_2087_);
lean_ctor_set_uint8(v___x_2089_, sizeof(void*)*1, v___x_2088_);
v___x_2090_ = l_Repr_addAppParen(v___x_2089_, v_prec_1978_);
return v___x_2090_;
}
}
}
}
case 6:
{
lean_object* v_content_2097_; lean_object* v_url_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2122_; 
v_content_2097_ = lean_ctor_get(v_x_1977_, 0);
v_url_2098_ = lean_ctor_get(v_x_1977_, 1);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2100_ = v_x_1977_;
v_isShared_2101_ = v_isSharedCheck_2122_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_url_2098_);
lean_inc(v_content_2097_);
lean_dec(v_x_1977_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2122_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___y_2103_; lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2118_ = lean_unsigned_to_nat(1024u);
v___x_2119_ = lean_nat_dec_le(v___x_2118_, v_prec_1978_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; 
v___x_2120_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2103_ = v___x_2120_;
goto v___jp_2102_;
}
else
{
lean_object* v___x_2121_; 
v___x_2121_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2103_ = v___x_2121_;
goto v___jp_2102_;
}
v___jp_2102_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2104_ = lean_box(1);
v___x_2105_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__22));
v___x_2106_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2097_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set_tag(v___x_2100_, 5);
lean_ctor_set(v___x_2100_, 1, v___x_2106_);
lean_ctor_set(v___x_2100_, 0, v___x_2105_);
v___x_2108_ = v___x_2100_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set(v___x_2109_, 1, v___x_2104_);
v___x_2110_ = l_String_quote(v_url_2098_);
v___x_2111_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2109_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
lean_inc(v___y_2103_);
v___x_2113_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___y_2103_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = 0;
v___x_2115_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2115_, 0, v___x_2113_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*1, v___x_2114_);
v___x_2116_ = l_Repr_addAppParen(v___x_2115_, v_prec_1978_);
return v___x_2116_;
}
}
}
}
case 7:
{
lean_object* v_name_2123_; lean_object* v_content_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2148_; 
v_name_2123_ = lean_ctor_get(v_x_1977_, 0);
v_content_2124_ = lean_ctor_get(v_x_1977_, 1);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2126_ = v_x_1977_;
v_isShared_2127_ = v_isSharedCheck_2148_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_content_2124_);
lean_inc(v_name_2123_);
lean_dec(v_x_1977_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2148_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___y_2129_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2144_ = lean_unsigned_to_nat(1024u);
v___x_2145_ = lean_nat_dec_le(v___x_2144_, v_prec_1978_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; 
v___x_2146_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2129_ = v___x_2146_;
goto v___jp_2128_;
}
else
{
lean_object* v___x_2147_; 
v___x_2147_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2129_ = v___x_2147_;
goto v___jp_2128_;
}
v___jp_2128_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2135_; 
v___x_2130_ = lean_box(1);
v___x_2131_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__25));
v___x_2132_ = l_String_quote(v_name_2123_);
v___x_2133_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set_tag(v___x_2126_, 5);
lean_ctor_set(v___x_2126_, 1, v___x_2133_);
lean_ctor_set(v___x_2126_, 0, v___x_2131_);
v___x_2135_ = v___x_2126_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set(v___x_2136_, 1, v___x_2130_);
v___x_2137_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2124_);
v___x_2138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2136_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
lean_inc(v___y_2129_);
v___x_2139_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___y_2129_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = 0;
v___x_2141_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set_uint8(v___x_2141_, sizeof(void*)*1, v___x_2140_);
v___x_2142_ = l_Repr_addAppParen(v___x_2141_, v_prec_1978_);
return v___x_2142_;
}
}
}
}
case 8:
{
lean_object* v_alt_2149_; lean_object* v_url_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2175_; 
v_alt_2149_ = lean_ctor_get(v_x_1977_, 0);
v_url_2150_ = lean_ctor_get(v_x_1977_, 1);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2152_ = v_x_1977_;
v_isShared_2153_ = v_isSharedCheck_2175_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_url_2150_);
lean_inc(v_alt_2149_);
lean_dec(v_x_1977_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2175_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___y_2155_; lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2171_ = lean_unsigned_to_nat(1024u);
v___x_2172_ = lean_nat_dec_le(v___x_2171_, v_prec_1978_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; 
v___x_2173_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2155_ = v___x_2173_;
goto v___jp_2154_;
}
else
{
lean_object* v___x_2174_; 
v___x_2174_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2155_ = v___x_2174_;
goto v___jp_2154_;
}
v___jp_2154_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2156_ = lean_box(1);
v___x_2157_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__28));
v___x_2158_ = l_String_quote(v_alt_2149_);
v___x_2159_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set_tag(v___x_2152_, 5);
lean_ctor_set(v___x_2152_, 1, v___x_2159_);
lean_ctor_set(v___x_2152_, 0, v___x_2157_);
v___x_2161_ = v___x_2152_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2157_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
lean_ctor_set(v___x_2162_, 1, v___x_2156_);
v___x_2163_ = l_String_quote(v_url_2150_);
v___x_2164_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
v___x_2165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2162_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
lean_inc(v___y_2155_);
v___x_2166_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___y_2155_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = 0;
v___x_2168_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*1, v___x_2167_);
v___x_2169_ = l_Repr_addAppParen(v___x_2168_, v_prec_1978_);
return v___x_2169_;
}
}
}
}
case 9:
{
lean_object* v_content_2176_; lean_object* v___y_2178_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
v_content_2176_ = lean_ctor_get(v_x_1977_, 0);
lean_inc_ref(v_content_2176_);
lean_dec_ref_known(v_x_1977_, 1);
v___x_2186_ = lean_unsigned_to_nat(1024u);
v___x_2187_ = lean_nat_dec_le(v___x_2186_, v_prec_1978_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; 
v___x_2188_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2178_ = v___x_2188_;
goto v___jp_2177_;
}
else
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2178_ = v___x_2189_;
goto v___jp_2177_;
}
v___jp_2177_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2179_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__31));
v___x_2180_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2176_);
v___x_2181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2179_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
lean_inc(v___y_2178_);
v___x_2182_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___y_2178_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
v___x_2183_ = 0;
v___x_2184_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2184_, 0, v___x_2182_);
lean_ctor_set_uint8(v___x_2184_, sizeof(void*)*1, v___x_2183_);
v___x_2185_ = l_Repr_addAppParen(v___x_2184_, v_prec_1978_);
return v___x_2185_;
}
}
default: 
{
lean_object* v_container_2190_; lean_object* v_content_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2241_; 
v_container_2190_ = lean_ctor_get(v_x_1977_, 0);
v_content_2191_ = lean_ctor_get(v_x_1977_, 1);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_x_1977_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2193_ = v_x_1977_;
v_isShared_2194_ = v_isSharedCheck_2241_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_content_2191_);
lean_inc(v_container_2190_);
lean_dec(v_x_1977_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2241_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2211_; lean_object* v___x_2237_; uint8_t v___x_2238_; 
v___x_2237_ = lean_unsigned_to_nat(1024u);
v___x_2238_ = lean_nat_dec_le(v___x_2237_, v_prec_1978_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; 
v___x_2239_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2211_ = v___x_2239_;
goto v___jp_2210_;
}
else
{
lean_object* v___x_2240_; 
v___x_2240_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2211_ = v___x_2240_;
goto v___jp_2210_;
}
v___jp_2195_:
{
lean_object* v___x_2201_; 
lean_inc(v___y_2197_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set_tag(v___x_2193_, 5);
lean_ctor_set(v___x_2193_, 1, v___y_2199_);
lean_ctor_set(v___x_2193_, 0, v___y_2197_);
v___x_2201_ = v___x_2193_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___y_2197_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v___y_2199_);
v___x_2201_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_inc(v___y_2198_);
v___x_2202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v___y_2198_);
v___x_2203_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2191_);
v___x_2204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
lean_inc(v___y_2196_);
v___x_2205_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___y_2196_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = 0;
v___x_2207_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set_uint8(v___x_2207_, sizeof(void*)*1, v___x_2206_);
v___x_2208_ = l_Repr_addAppParen(v___x_2207_, v_prec_1978_);
return v___x_2208_;
}
}
v___jp_2210_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = lean_box(1);
v___x_2213_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__34));
if (lean_obj_tag(v_container_2190_) == 0)
{
lean_object* v_val_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; lean_object* v___x_2223_; 
v_val_2214_ = lean_ctor_get(v_container_2190_, 0);
lean_inc(v_val_2214_);
lean_dec_ref_known(v_container_2190_, 1);
v___x_2215_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__5));
v___x_2216_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_2214_);
lean_dec(v_val_2214_);
v___x_2217_ = lean_unsigned_to_nat(0u);
v___x_2218_ = l_Lean_Name_reprPrec(v___x_2216_, v___x_2217_);
v___x_2219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2215_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
v___x_2220_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__7));
v___x_2221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2219_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = 0;
v___x_2223_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2223_, 0, v___x_2221_);
lean_ctor_set_uint8(v___x_2223_, sizeof(void*)*1, v___x_2222_);
v___y_2196_ = v___y_2211_;
v___y_2197_ = v___x_2213_;
v___y_2198_ = v___x_2212_;
v___y_2199_ = v___x_2223_;
goto v___jp_2195_;
}
else
{
lean_object* v_index_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2236_; 
v_index_2224_ = lean_ctor_get(v_container_2190_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_container_2190_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2226_ = v_container_2190_;
v_isShared_2227_ = v_isSharedCheck_2236_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_index_2224_);
lean_dec(v_container_2190_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2236_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2228_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_2229_ = l_Nat_reprFast(v_index_2224_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set_tag(v___x_2226_, 3);
lean_ctor_set(v___x_2226_, 0, v___x_2229_);
v___x_2231_ = v___x_2226_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2232_; uint8_t v___x_2233_; lean_object* v___x_2234_; 
v___x_2232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2228_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
v___x_2233_ = 0;
v___x_2234_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2234_, 0, v___x_2232_);
lean_ctor_set_uint8(v___x_2234_, sizeof(void*)*1, v___x_2233_);
v___y_2196_ = v___y_2211_;
v___y_2197_ = v___x_2213_;
v___y_2198_ = v___x_2212_;
v___y_2199_ = v___x_2234_;
goto v___jp_2195_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object* v___y_2242_){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = lean_unsigned_to_nat(0u);
v___x_2244_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v___y_2242_, v___x_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_2245_, lean_object* v_prec_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_x_2245_, v_prec_2246_);
lean_dec(v_prec_2246_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(lean_object* v_xs_2248_){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; 
v___x_2249_ = lean_array_get_size(v_xs_2248_);
v___x_2250_ = lean_unsigned_to_nat(0u);
v___x_2251_ = lean_nat_dec_eq(v___x_2249_, v___x_2250_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2252_ = lean_array_to_list(v_xs_2248_);
v___x_2253_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2254_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_2252_, v___x_2253_);
v___x_2255_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2256_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
lean_ctor_set(v___x_2257_, 1, v___x_2254_);
v___x_2258_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2257_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
v___x_2260_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2255_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = l_Std_Format_fill(v___x_2260_);
return v___x_2261_;
}
else
{
lean_object* v___x_2262_; 
lean_dec_ref(v_xs_2248_);
v___x_2262_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2262_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_unsigned_to_nat(12u);
v___x_2294_ = lean_nat_to_int(v___x_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(lean_object* v_x_2295_, lean_object* v_x_2296_, lean_object* v_x_2297_){
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
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_unsigned_to_nat(0u);
v___x_2306_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_2298_, v___x_2305_);
v___x_2307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2304_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v_x_2296_ = v___x_2307_;
v_x_2297_ = v_tail_2299_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(lean_object* v_x_2311_, lean_object* v_x_2312_, lean_object* v_x_2313_){
_start:
{
if (lean_obj_tag(v_x_2313_) == 0)
{
lean_dec(v_x_2311_);
return v_x_2312_;
}
else
{
lean_object* v_head_2314_; lean_object* v_tail_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2326_; 
v_head_2314_ = lean_ctor_get(v_x_2313_, 0);
v_tail_2315_ = lean_ctor_get(v_x_2313_, 1);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_x_2313_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2317_ = v_x_2313_;
v_isShared_2318_ = v_isSharedCheck_2326_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_tail_2315_);
lean_inc(v_head_2314_);
lean_dec(v_x_2313_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2326_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
lean_inc(v_x_2311_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set_tag(v___x_2317_, 5);
lean_ctor_set(v___x_2317_, 1, v_x_2311_);
lean_ctor_set(v___x_2317_, 0, v_x_2312_);
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_x_2312_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_x_2311_);
v___x_2320_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2321_ = lean_unsigned_to_nat(0u);
v___x_2322_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_2314_, v___x_2321_);
v___x_2323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2320_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
v___x_2324_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(v_x_2311_, v___x_2323_, v_tail_2315_);
return v___x_2324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(lean_object* v_x_2327_, lean_object* v_x_2328_){
_start:
{
if (lean_obj_tag(v_x_2327_) == 0)
{
lean_object* v___x_2329_; 
lean_dec(v_x_2328_);
v___x_2329_ = lean_box(0);
return v___x_2329_;
}
else
{
lean_object* v_tail_2330_; 
v_tail_2330_ = lean_ctor_get(v_x_2327_, 1);
if (lean_obj_tag(v_tail_2330_) == 0)
{
lean_object* v_head_2331_; lean_object* v___x_2332_; 
lean_dec(v_x_2328_);
v_head_2331_ = lean_ctor_get(v_x_2327_, 0);
lean_inc(v_head_2331_);
lean_dec_ref_known(v_x_2327_, 2);
v___x_2332_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_2331_);
return v___x_2332_;
}
else
{
lean_object* v_head_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
lean_inc(v_tail_2330_);
v_head_2333_ = lean_ctor_get(v_x_2327_, 0);
lean_inc(v_head_2333_);
lean_dec_ref_known(v_x_2327_, 2);
v___x_2334_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_2333_);
v___x_2335_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(v_x_2328_, v___x_2334_, v_tail_2330_);
return v___x_2335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(lean_object* v_xs_2336_){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v___x_2337_ = lean_array_get_size(v_xs_2336_);
v___x_2338_ = lean_unsigned_to_nat(0u);
v___x_2339_ = lean_nat_dec_eq(v___x_2337_, v___x_2338_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2340_ = lean_array_to_list(v_xs_2336_);
v___x_2341_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2342_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_2340_, v___x_2341_);
v___x_2343_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2344_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
lean_ctor_set(v___x_2345_, 1, v___x_2342_);
v___x_2346_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2343_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = l_Std_Format_fill(v___x_2348_);
return v___x_2349_;
}
else
{
lean_object* v___x_2350_; 
lean_dec_ref(v_xs_2336_);
v___x_2350_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2350_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0));
v___x_2353_ = lean_string_length(v___x_2352_);
return v___x_2353_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10(void){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9);
v___x_2355_ = lean_nat_to_int(v___x_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_x_2361_){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2362_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__6));
v___x_2363_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_2364_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_x_2361_);
v___x_2365_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2363_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
v___x_2366_ = 0;
v___x_2367_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2367_, 0, v___x_2365_);
lean_ctor_set_uint8(v___x_2367_, sizeof(void*)*1, v___x_2366_);
v___x_2368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2362_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
v___x_2369_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_2370_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_2371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
lean_ctor_set(v___x_2371_, 1, v___x_2368_);
v___x_2372_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_2373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2369_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
lean_ctor_set_uint8(v___x_2375_, sizeof(void*)*1, v___x_2366_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(lean_object* v_x_2376_, lean_object* v_x_2377_, lean_object* v_x_2378_){
_start:
{
if (lean_obj_tag(v_x_2378_) == 0)
{
lean_dec(v_x_2376_);
return v_x_2377_;
}
else
{
lean_object* v_head_2379_; lean_object* v_tail_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2390_; 
v_head_2379_ = lean_ctor_get(v_x_2378_, 0);
v_tail_2380_ = lean_ctor_get(v_x_2378_, 1);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_x_2378_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2382_ = v_x_2378_;
v_isShared_2383_ = v_isSharedCheck_2390_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_tail_2380_);
lean_inc(v_head_2379_);
lean_dec(v_x_2378_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2390_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
lean_inc(v_x_2376_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set_tag(v___x_2382_, 5);
lean_ctor_set(v___x_2382_, 1, v_x_2376_);
lean_ctor_set(v___x_2382_, 0, v_x_2377_);
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_x_2377_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_x_2376_);
v___x_2385_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2386_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_2379_);
v___x_2387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2385_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
v_x_2377_ = v___x_2387_;
v_x_2378_ = v_tail_2380_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(lean_object* v_x_2391_, lean_object* v_x_2392_, lean_object* v_x_2393_){
_start:
{
if (lean_obj_tag(v_x_2393_) == 0)
{
lean_dec(v_x_2391_);
return v_x_2392_;
}
else
{
lean_object* v_head_2394_; lean_object* v_tail_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2405_; 
v_head_2394_ = lean_ctor_get(v_x_2393_, 0);
v_tail_2395_ = lean_ctor_get(v_x_2393_, 1);
v_isSharedCheck_2405_ = !lean_is_exclusive(v_x_2393_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2397_ = v_x_2393_;
v_isShared_2398_ = v_isSharedCheck_2405_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_tail_2395_);
lean_inc(v_head_2394_);
lean_dec(v_x_2393_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2405_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
lean_inc(v_x_2391_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set_tag(v___x_2397_, 5);
lean_ctor_set(v___x_2397_, 1, v_x_2391_);
lean_ctor_set(v___x_2397_, 0, v_x_2392_);
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_x_2392_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v_x_2391_);
v___x_2400_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2401_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_2394_);
v___x_2402_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2400_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(v_x_2391_, v___x_2402_, v_tail_2395_);
return v___x_2403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(lean_object* v_x_2406_, lean_object* v_x_2407_){
_start:
{
if (lean_obj_tag(v_x_2406_) == 0)
{
lean_object* v___x_2408_; 
lean_dec(v_x_2407_);
v___x_2408_ = lean_box(0);
return v___x_2408_;
}
else
{
lean_object* v_tail_2409_; 
v_tail_2409_ = lean_ctor_get(v_x_2406_, 1);
if (lean_obj_tag(v_tail_2409_) == 0)
{
lean_object* v_head_2410_; lean_object* v___x_2411_; 
lean_dec(v_x_2407_);
v_head_2410_ = lean_ctor_get(v_x_2406_, 0);
lean_inc(v_head_2410_);
lean_dec_ref_known(v_x_2406_, 2);
v___x_2411_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_2410_);
return v___x_2411_;
}
else
{
lean_object* v_head_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
lean_inc(v_tail_2409_);
v_head_2412_ = lean_ctor_get(v_x_2406_, 0);
lean_inc(v_head_2412_);
lean_dec_ref_known(v_x_2406_, 2);
v___x_2413_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_2412_);
v___x_2414_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(v_x_2407_, v___x_2413_, v_tail_2409_);
return v___x_2414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(lean_object* v_xs_2415_){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; uint8_t v___x_2418_; 
v___x_2416_ = lean_array_get_size(v_xs_2415_);
v___x_2417_ = lean_unsigned_to_nat(0u);
v___x_2418_ = lean_nat_dec_eq(v___x_2416_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2419_ = lean_array_to_list(v_xs_2415_);
v___x_2420_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2421_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(v___x_2419_, v___x_2420_);
v___x_2422_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2423_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2424_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
lean_ctor_set(v___x_2424_, 1, v___x_2421_);
v___x_2425_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2426_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2424_);
lean_ctor_set(v___x_2426_, 1, v___x_2425_);
v___x_2427_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2422_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = l_Std_Format_fill(v___x_2427_);
return v___x_2428_;
}
else
{
lean_object* v___x_2429_; 
lean_dec_ref(v_xs_2415_);
v___x_2429_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2429_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = lean_unsigned_to_nat(0u);
v___x_2437_ = lean_nat_to_int(v___x_2436_);
return v___x_2437_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_unsigned_to_nat(8u);
v___x_2454_ = lean_nat_to_int(v___x_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_x_2458_){
_start:
{
lean_object* v_term_2459_; lean_object* v_desc_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2492_; 
v_term_2459_ = lean_ctor_get(v_x_2458_, 0);
v_desc_2460_ = lean_ctor_get(v_x_2458_, 1);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_x_2458_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2462_ = v_x_2458_;
v_isShared_2463_ = v_isSharedCheck_2492_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_desc_2460_);
lean_inc(v_term_2459_);
lean_dec(v_x_2458_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2492_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2464_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_2465_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__3));
v___x_2466_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_2467_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_term_2459_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set_tag(v___x_2462_, 4);
lean_ctor_set(v___x_2462_, 1, v___x_2467_);
lean_ctor_set(v___x_2462_, 0, v___x_2466_);
v___x_2469_ = v___x_2462_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
uint8_t v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2470_ = 0;
v___x_2471_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2471_, 0, v___x_2469_);
lean_ctor_set_uint8(v___x_2471_, sizeof(void*)*1, v___x_2470_);
v___x_2472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2465_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_2474_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2472_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___x_2475_ = lean_box(1);
v___x_2476_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2474_);
lean_ctor_set(v___x_2476_, 1, v___x_2475_);
v___x_2477_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__6));
v___x_2478_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
lean_ctor_set(v___x_2479_, 1, v___x_2464_);
v___x_2480_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_desc_2460_);
v___x_2481_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2466_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
lean_ctor_set_uint8(v___x_2482_, sizeof(void*)*1, v___x_2470_);
v___x_2483_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2479_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_2485_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_2486_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
lean_ctor_set(v___x_2486_, 1, v___x_2483_);
v___x_2487_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_2488_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2484_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
lean_ctor_set_uint8(v___x_2490_, sizeof(void*)*1, v___x_2470_);
return v___x_2490_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(lean_object* v_x_2493_, lean_object* v_x_2494_, lean_object* v_x_2495_){
_start:
{
if (lean_obj_tag(v_x_2495_) == 0)
{
lean_dec(v_x_2493_);
return v_x_2494_;
}
else
{
lean_object* v_head_2496_; lean_object* v_tail_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2507_; 
v_head_2496_ = lean_ctor_get(v_x_2495_, 0);
v_tail_2497_ = lean_ctor_get(v_x_2495_, 1);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_x_2495_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2499_ = v_x_2495_;
v_isShared_2500_ = v_isSharedCheck_2507_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_tail_2497_);
lean_inc(v_head_2496_);
lean_dec(v_x_2495_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2507_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
lean_inc(v_x_2493_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set_tag(v___x_2499_, 5);
lean_ctor_set(v___x_2499_, 1, v_x_2493_);
lean_ctor_set(v___x_2499_, 0, v_x_2494_);
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_x_2494_);
lean_ctor_set(v_reuseFailAlloc_2506_, 1, v_x_2493_);
v___x_2502_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_2496_);
v___x_2504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2502_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v_x_2494_ = v___x_2504_;
v_x_2495_ = v_tail_2497_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(lean_object* v_x_2508_, lean_object* v_x_2509_, lean_object* v_x_2510_){
_start:
{
if (lean_obj_tag(v_x_2510_) == 0)
{
lean_dec(v_x_2508_);
return v_x_2509_;
}
else
{
lean_object* v_head_2511_; lean_object* v_tail_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2522_; 
v_head_2511_ = lean_ctor_get(v_x_2510_, 0);
v_tail_2512_ = lean_ctor_get(v_x_2510_, 1);
v_isSharedCheck_2522_ = !lean_is_exclusive(v_x_2510_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2514_ = v_x_2510_;
v_isShared_2515_ = v_isSharedCheck_2522_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_tail_2512_);
lean_inc(v_head_2511_);
lean_dec(v_x_2510_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2522_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
lean_inc(v_x_2508_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set_tag(v___x_2514_, 5);
lean_ctor_set(v___x_2514_, 1, v_x_2508_);
lean_ctor_set(v___x_2514_, 0, v_x_2509_);
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_x_2509_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_x_2508_);
v___x_2517_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2518_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_2511_);
v___x_2519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2517_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
v___x_2520_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(v_x_2508_, v___x_2519_, v_tail_2512_);
return v___x_2520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(lean_object* v_x_2523_, lean_object* v_x_2524_){
_start:
{
if (lean_obj_tag(v_x_2523_) == 0)
{
lean_object* v___x_2525_; 
lean_dec(v_x_2524_);
v___x_2525_ = lean_box(0);
return v___x_2525_;
}
else
{
lean_object* v_tail_2526_; 
v_tail_2526_ = lean_ctor_get(v_x_2523_, 1);
if (lean_obj_tag(v_tail_2526_) == 0)
{
lean_object* v_head_2527_; lean_object* v___x_2528_; 
lean_dec(v_x_2524_);
v_head_2527_ = lean_ctor_get(v_x_2523_, 0);
lean_inc(v_head_2527_);
lean_dec_ref_known(v_x_2523_, 2);
v___x_2528_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_2527_);
return v___x_2528_;
}
else
{
lean_object* v_head_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
lean_inc(v_tail_2526_);
v_head_2529_ = lean_ctor_get(v_x_2523_, 0);
lean_inc(v_head_2529_);
lean_dec_ref_known(v_x_2523_, 2);
v___x_2530_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_2529_);
v___x_2531_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(v_x_2524_, v___x_2530_, v_tail_2526_);
return v___x_2531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(lean_object* v_xs_2532_){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2533_ = lean_array_get_size(v_xs_2532_);
v___x_2534_ = lean_unsigned_to_nat(0u);
v___x_2535_ = lean_nat_dec_eq(v___x_2533_, v___x_2534_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2536_ = lean_array_to_list(v_xs_2532_);
v___x_2537_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2538_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(v___x_2536_, v___x_2537_);
v___x_2539_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2540_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
lean_ctor_set(v___x_2541_, 1, v___x_2538_);
v___x_2542_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2541_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2539_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = l_Std_Format_fill(v___x_2544_);
return v___x_2545_;
}
else
{
lean_object* v___x_2546_; 
lean_dec_ref(v_xs_2532_);
v___x_2546_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(lean_object* v_x_2565_, lean_object* v_prec_2566_){
_start:
{
switch(lean_obj_tag(v_x_2565_))
{
case 0:
{
lean_object* v_contents_2567_; lean_object* v___y_2569_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v_contents_2567_ = lean_ctor_get(v_x_2565_, 0);
lean_inc_ref(v_contents_2567_);
lean_dec_ref_known(v_x_2565_, 1);
v___x_2577_ = lean_unsigned_to_nat(1024u);
v___x_2578_ = lean_nat_dec_le(v___x_2577_, v_prec_2566_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2569_ = v___x_2579_;
goto v___jp_2568_;
}
else
{
lean_object* v___x_2580_; 
v___x_2580_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2569_ = v___x_2580_;
goto v___jp_2568_;
}
v___jp_2568_:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2570_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__2));
v___x_2571_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_contents_2567_);
v___x_2572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2570_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
lean_inc(v___y_2569_);
v___x_2573_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___y_2569_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = 0;
v___x_2575_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set_uint8(v___x_2575_, sizeof(void*)*1, v___x_2574_);
v___x_2576_ = l_Repr_addAppParen(v___x_2575_, v_prec_2566_);
return v___x_2576_;
}
}
case 1:
{
lean_object* v_content_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2601_; 
v_content_2581_ = lean_ctor_get(v_x_2565_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v_x_2565_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2583_ = v_x_2565_;
v_isShared_2584_ = v_isSharedCheck_2601_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_content_2581_);
lean_dec(v_x_2565_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2601_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___y_2586_; lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___x_2597_ = lean_unsigned_to_nat(1024u);
v___x_2598_ = lean_nat_dec_le(v___x_2597_, v_prec_2566_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; 
v___x_2599_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2586_ = v___x_2599_;
goto v___jp_2585_;
}
else
{
lean_object* v___x_2600_; 
v___x_2600_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2586_ = v___x_2600_;
goto v___jp_2585_;
}
v___jp_2585_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2587_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__5));
v___x_2588_ = l_String_quote(v_content_2581_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set_tag(v___x_2583_, 3);
lean_ctor_set(v___x_2583_, 0, v___x_2588_);
v___x_2590_ = v___x_2583_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2587_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
lean_inc(v___y_2586_);
v___x_2592_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___y_2586_);
lean_ctor_set(v___x_2592_, 1, v___x_2591_);
v___x_2593_ = 0;
v___x_2594_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2594_, 0, v___x_2592_);
lean_ctor_set_uint8(v___x_2594_, sizeof(void*)*1, v___x_2593_);
v___x_2595_ = l_Repr_addAppParen(v___x_2594_, v_prec_2566_);
return v___x_2595_;
}
}
}
}
case 2:
{
lean_object* v_items_2602_; lean_object* v___y_2604_; lean_object* v___x_2612_; uint8_t v___x_2613_; 
v_items_2602_ = lean_ctor_get(v_x_2565_, 0);
lean_inc_ref(v_items_2602_);
lean_dec_ref_known(v_x_2565_, 1);
v___x_2612_ = lean_unsigned_to_nat(1024u);
v___x_2613_ = lean_nat_dec_le(v___x_2612_, v_prec_2566_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; 
v___x_2614_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2604_ = v___x_2614_;
goto v___jp_2603_;
}
else
{
lean_object* v___x_2615_; 
v___x_2615_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2604_ = v___x_2615_;
goto v___jp_2603_;
}
v___jp_2603_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2605_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__8));
v___x_2606_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_2602_);
v___x_2607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2605_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
lean_inc(v___y_2604_);
v___x_2608_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___y_2604_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = 0;
v___x_2610_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*1, v___x_2609_);
v___x_2611_ = l_Repr_addAppParen(v___x_2610_, v_prec_2566_);
return v___x_2611_;
}
}
case 3:
{
lean_object* v_start_2616_; lean_object* v_items_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2652_; 
v_start_2616_ = lean_ctor_get(v_x_2565_, 0);
v_items_2617_ = lean_ctor_get(v_x_2565_, 1);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_x_2565_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2619_ = v_x_2565_;
v_isShared_2620_ = v_isSharedCheck_2652_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_items_2617_);
lean_inc(v_start_2616_);
lean_dec(v_x_2565_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2652_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2637_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2648_ = lean_unsigned_to_nat(1024u);
v___x_2649_ = lean_nat_dec_le(v___x_2648_, v_prec_2566_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; 
v___x_2650_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2637_ = v___x_2650_;
goto v___jp_2636_;
}
else
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2637_ = v___x_2651_;
goto v___jp_2636_;
}
v___jp_2621_:
{
lean_object* v___x_2627_; 
lean_inc(v___y_2623_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set_tag(v___x_2619_, 5);
lean_ctor_set(v___x_2619_, 1, v___y_2625_);
lean_ctor_set(v___x_2619_, 0, v___y_2623_);
v___x_2627_ = v___x_2619_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___y_2623_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v___y_2625_);
v___x_2627_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
lean_inc(v___y_2624_);
v___x_2628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2627_);
lean_ctor_set(v___x_2628_, 1, v___y_2624_);
v___x_2629_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_2617_);
v___x_2630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2628_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
lean_inc(v___y_2622_);
v___x_2631_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___y_2622_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = 0;
v___x_2633_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2633_, 0, v___x_2631_);
lean_ctor_set_uint8(v___x_2633_, sizeof(void*)*1, v___x_2632_);
v___x_2634_ = l_Repr_addAppParen(v___x_2633_, v_prec_2566_);
return v___x_2634_;
}
}
v___jp_2636_:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; 
v___x_2638_ = lean_box(1);
v___x_2639_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__11));
v___x_2640_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12, &l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12);
v___x_2641_ = lean_int_dec_lt(v_start_2616_, v___x_2640_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = l_Int_repr(v_start_2616_);
lean_dec(v_start_2616_);
v___x_2643_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2642_);
v___y_2622_ = v___y_2637_;
v___y_2623_ = v___x_2639_;
v___y_2624_ = v___x_2638_;
v___y_2625_ = v___x_2643_;
goto v___jp_2621_;
}
else
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2644_ = lean_unsigned_to_nat(1024u);
v___x_2645_ = l_Int_repr(v_start_2616_);
lean_dec(v_start_2616_);
v___x_2646_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
v___x_2647_ = l_Repr_addAppParen(v___x_2646_, v___x_2644_);
v___y_2622_ = v___y_2637_;
v___y_2623_ = v___x_2639_;
v___y_2624_ = v___x_2638_;
v___y_2625_ = v___x_2647_;
goto v___jp_2621_;
}
}
}
}
case 4:
{
lean_object* v_items_2653_; lean_object* v___y_2655_; lean_object* v___x_2663_; uint8_t v___x_2664_; 
v_items_2653_ = lean_ctor_get(v_x_2565_, 0);
lean_inc_ref(v_items_2653_);
lean_dec_ref_known(v_x_2565_, 1);
v___x_2663_ = lean_unsigned_to_nat(1024u);
v___x_2664_ = lean_nat_dec_le(v___x_2663_, v_prec_2566_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; 
v___x_2665_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2655_ = v___x_2665_;
goto v___jp_2654_;
}
else
{
lean_object* v___x_2666_; 
v___x_2666_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2655_ = v___x_2666_;
goto v___jp_2654_;
}
v___jp_2654_:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2656_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__15));
v___x_2657_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(v_items_2653_);
v___x_2658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2656_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
lean_inc(v___y_2655_);
v___x_2659_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___y_2655_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
v___x_2660_ = 0;
v___x_2661_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2661_, 0, v___x_2659_);
lean_ctor_set_uint8(v___x_2661_, sizeof(void*)*1, v___x_2660_);
v___x_2662_ = l_Repr_addAppParen(v___x_2661_, v_prec_2566_);
return v___x_2662_;
}
}
case 5:
{
lean_object* v_items_2667_; lean_object* v___y_2669_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v_items_2667_ = lean_ctor_get(v_x_2565_, 0);
lean_inc_ref(v_items_2667_);
lean_dec_ref_known(v_x_2565_, 1);
v___x_2677_ = lean_unsigned_to_nat(1024u);
v___x_2678_ = lean_nat_dec_le(v___x_2677_, v_prec_2566_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; 
v___x_2679_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2669_ = v___x_2679_;
goto v___jp_2668_;
}
else
{
lean_object* v___x_2680_; 
v___x_2680_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2669_ = v___x_2680_;
goto v___jp_2668_;
}
v___jp_2668_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2670_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__18));
v___x_2671_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_items_2667_);
v___x_2672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2670_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
lean_inc(v___y_2669_);
v___x_2673_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___y_2669_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = 0;
v___x_2675_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2675_, 0, v___x_2673_);
lean_ctor_set_uint8(v___x_2675_, sizeof(void*)*1, v___x_2674_);
v___x_2676_ = l_Repr_addAppParen(v___x_2675_, v_prec_2566_);
return v___x_2676_;
}
}
case 6:
{
lean_object* v_content_2681_; lean_object* v___y_2683_; lean_object* v___x_2691_; uint8_t v___x_2692_; 
v_content_2681_ = lean_ctor_get(v_x_2565_, 0);
lean_inc_ref(v_content_2681_);
lean_dec_ref_known(v_x_2565_, 1);
v___x_2691_ = lean_unsigned_to_nat(1024u);
v___x_2692_ = lean_nat_dec_le(v___x_2691_, v_prec_2566_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; 
v___x_2693_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2683_ = v___x_2693_;
goto v___jp_2682_;
}
else
{
lean_object* v___x_2694_; 
v___x_2694_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2683_ = v___x_2694_;
goto v___jp_2682_;
}
v___jp_2682_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2684_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__21));
v___x_2685_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_2681_);
v___x_2686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2684_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
lean_inc(v___y_2683_);
v___x_2687_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___y_2683_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = 0;
v___x_2689_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2689_, 0, v___x_2687_);
lean_ctor_set_uint8(v___x_2689_, sizeof(void*)*1, v___x_2688_);
v___x_2690_ = l_Repr_addAppParen(v___x_2689_, v_prec_2566_);
return v___x_2690_;
}
}
default: 
{
lean_object* v_container_2695_; lean_object* v_content_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2746_; 
v_container_2695_ = lean_ctor_get(v_x_2565_, 0);
v_content_2696_ = lean_ctor_get(v_x_2565_, 1);
v_isSharedCheck_2746_ = !lean_is_exclusive(v_x_2565_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2698_ = v_x_2565_;
v_isShared_2699_ = v_isSharedCheck_2746_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_content_2696_);
lean_inc(v_container_2695_);
lean_dec(v_x_2565_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2746_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___y_2701_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2716_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2742_ = lean_unsigned_to_nat(1024u);
v___x_2743_ = lean_nat_dec_le(v___x_2742_, v_prec_2566_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; 
v___x_2744_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2716_ = v___x_2744_;
goto v___jp_2715_;
}
else
{
lean_object* v___x_2745_; 
v___x_2745_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2716_ = v___x_2745_;
goto v___jp_2715_;
}
v___jp_2700_:
{
lean_object* v___x_2706_; 
lean_inc(v___y_2701_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set_tag(v___x_2698_, 5);
lean_ctor_set(v___x_2698_, 1, v___y_2704_);
lean_ctor_set(v___x_2698_, 0, v___y_2701_);
v___x_2706_ = v___x_2698_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___y_2701_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v___y_2704_);
v___x_2706_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
lean_inc(v___y_2702_);
v___x_2707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
lean_ctor_set(v___x_2707_, 1, v___y_2702_);
v___x_2708_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_2696_);
v___x_2709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
lean_inc(v___y_2703_);
v___x_2710_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___y_2703_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = 0;
v___x_2712_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2712_, 0, v___x_2710_);
lean_ctor_set_uint8(v___x_2712_, sizeof(void*)*1, v___x_2711_);
v___x_2713_ = l_Repr_addAppParen(v___x_2712_, v_prec_2566_);
return v___x_2713_;
}
}
v___jp_2715_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = lean_box(1);
v___x_2718_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__24));
if (lean_obj_tag(v_container_2695_) == 0)
{
lean_object* v_val_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; uint8_t v___x_2727_; lean_object* v___x_2728_; 
v_val_2719_ = lean_ctor_get(v_container_2695_, 0);
lean_inc(v_val_2719_);
lean_dec_ref_known(v_container_2695_, 1);
v___x_2720_ = ((lean_object*)(l_Lean_instReprElabBlock___lam__0___closed__3));
v___x_2721_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_2719_);
lean_dec(v_val_2719_);
v___x_2722_ = lean_unsigned_to_nat(0u);
v___x_2723_ = l_Lean_Name_reprPrec(v___x_2721_, v___x_2722_);
v___x_2724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2720_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
v___x_2725_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__7));
v___x_2726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2724_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = 0;
v___x_2728_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2728_, 0, v___x_2726_);
lean_ctor_set_uint8(v___x_2728_, sizeof(void*)*1, v___x_2727_);
v___y_2701_ = v___x_2718_;
v___y_2702_ = v___x_2717_;
v___y_2703_ = v___y_2716_;
v___y_2704_ = v___x_2728_;
goto v___jp_2700_;
}
else
{
lean_object* v_index_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2741_; 
v_index_2729_ = lean_ctor_get(v_container_2695_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_container_2695_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2731_ = v_container_2695_;
v_isShared_2732_ = v_isSharedCheck_2741_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_index_2729_);
lean_dec(v_container_2695_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2741_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___x_2733_ = ((lean_object*)(l_Lean_instReprElabBlock___lam__0___closed__6));
v___x_2734_ = l_Nat_reprFast(v_index_2729_);
if (v_isShared_2732_ == 0)
{
lean_ctor_set_tag(v___x_2731_, 3);
lean_ctor_set(v___x_2731_, 0, v___x_2734_);
v___x_2736_ = v___x_2731_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2734_);
v___x_2736_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2737_; uint8_t v___x_2738_; lean_object* v___x_2739_; 
v___x_2737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2733_);
lean_ctor_set(v___x_2737_, 1, v___x_2736_);
v___x_2738_ = 0;
v___x_2739_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2739_, 0, v___x_2737_);
lean_ctor_set_uint8(v___x_2739_, sizeof(void*)*1, v___x_2738_);
v___y_2701_ = v___x_2718_;
v___y_2702_ = v___x_2717_;
v___y_2703_ = v___y_2716_;
v___y_2704_ = v___x_2739_;
goto v___jp_2700_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(lean_object* v___y_2747_){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = lean_unsigned_to_nat(0u);
v___x_2749_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v___y_2747_, v___x_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___boxed(lean_object* v_x_2750_, lean_object* v_prec_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_x_2750_, v_prec_2751_);
lean_dec(v_prec_2751_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(lean_object* v_xs_2753_){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; 
v___x_2754_ = lean_array_get_size(v_xs_2753_);
v___x_2755_ = lean_unsigned_to_nat(0u);
v___x_2756_ = lean_nat_dec_eq(v___x_2754_, v___x_2755_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2757_ = lean_array_to_list(v_xs_2753_);
v___x_2758_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2759_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_2757_, v___x_2758_);
v___x_2760_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2761_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
lean_ctor_set(v___x_2762_, 1, v___x_2759_);
v___x_2763_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2762_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2760_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
v___x_2766_ = l_Std_Format_fill(v___x_2765_);
return v___x_2766_;
}
else
{
lean_object* v___x_2767_; 
lean_dec_ref(v_xs_2753_);
v___x_2767_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2767_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(lean_object* v_x_2771_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = ((lean_object*)(l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__1));
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___boxed(lean_object* v_x_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_2773_);
lean_dec(v_x_2773_);
return v_res_2774_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_unsigned_to_nat(9u);
v___x_2785_ = lean_nat_to_int(v___x_2784_);
return v___x_2785_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = lean_unsigned_to_nat(15u);
v___x_2790_ = lean_nat_to_int(v___x_2789_);
return v___x_2790_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12(void){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = lean_unsigned_to_nat(11u);
v___x_2798_ = lean_nat_to_int(v___x_2797_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(lean_object* v_x_2802_, lean_object* v_x_2803_, lean_object* v_x_2804_){
_start:
{
if (lean_obj_tag(v_x_2804_) == 0)
{
lean_dec(v_x_2802_);
return v_x_2803_;
}
else
{
lean_object* v_head_2805_; lean_object* v_tail_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2816_; 
v_head_2805_ = lean_ctor_get(v_x_2804_, 0);
v_tail_2806_ = lean_ctor_get(v_x_2804_, 1);
v_isSharedCheck_2816_ = !lean_is_exclusive(v_x_2804_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2808_ = v_x_2804_;
v_isShared_2809_ = v_isSharedCheck_2816_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_tail_2806_);
lean_inc(v_head_2805_);
lean_dec(v_x_2804_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2816_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
lean_inc(v_x_2802_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set_tag(v___x_2808_, 5);
lean_ctor_set(v___x_2808_, 1, v_x_2802_);
lean_ctor_set(v___x_2808_, 0, v_x_2803_);
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_x_2803_);
lean_ctor_set(v_reuseFailAlloc_2815_, 1, v_x_2802_);
v___x_2811_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2812_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_2805_);
v___x_2813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2811_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
v___x_2814_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(v_x_2802_, v___x_2813_, v_tail_2806_);
return v___x_2814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(lean_object* v_x_2817_, lean_object* v_x_2818_){
_start:
{
if (lean_obj_tag(v_x_2817_) == 0)
{
lean_object* v___x_2819_; 
lean_dec(v_x_2818_);
v___x_2819_ = lean_box(0);
return v___x_2819_;
}
else
{
lean_object* v_tail_2820_; 
v_tail_2820_ = lean_ctor_get(v_x_2817_, 1);
if (lean_obj_tag(v_tail_2820_) == 0)
{
lean_object* v_head_2821_; lean_object* v___x_2822_; 
lean_dec(v_x_2818_);
v_head_2821_ = lean_ctor_get(v_x_2817_, 0);
lean_inc(v_head_2821_);
lean_dec_ref_known(v_x_2817_, 2);
v___x_2822_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_2821_);
return v___x_2822_;
}
else
{
lean_object* v_head_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_inc(v_tail_2820_);
v_head_2823_ = lean_ctor_get(v_x_2817_, 0);
lean_inc(v_head_2823_);
lean_dec_ref_known(v_x_2817_, 2);
v___x_2824_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_2823_);
v___x_2825_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(v_x_2818_, v___x_2824_, v_tail_2820_);
return v___x_2825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(lean_object* v_xs_2826_){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; uint8_t v___x_2829_; 
v___x_2827_ = lean_array_get_size(v_xs_2826_);
v___x_2828_ = lean_unsigned_to_nat(0u);
v___x_2829_ = lean_nat_dec_eq(v___x_2827_, v___x_2828_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2830_ = lean_array_to_list(v_xs_2826_);
v___x_2831_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2832_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(v___x_2830_, v___x_2831_);
v___x_2833_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2834_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2834_);
lean_ctor_set(v___x_2835_, 1, v___x_2832_);
v___x_2836_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2835_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2833_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = l_Std_Format_fill(v___x_2838_);
return v___x_2839_;
}
else
{
lean_object* v___x_2840_; 
lean_dec_ref(v_xs_2826_);
v___x_2840_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(lean_object* v_x_2841_){
_start:
{
lean_object* v_title_2842_; lean_object* v_titleString_2843_; lean_object* v_metadata_2844_; lean_object* v_content_2845_; lean_object* v_subParts_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v_title_2842_ = lean_ctor_get(v_x_2841_, 0);
lean_inc_ref(v_title_2842_);
v_titleString_2843_ = lean_ctor_get(v_x_2841_, 1);
lean_inc_ref(v_titleString_2843_);
v_metadata_2844_ = lean_ctor_get(v_x_2841_, 2);
lean_inc(v_metadata_2844_);
v_content_2845_ = lean_ctor_get(v_x_2841_, 3);
lean_inc_ref(v_content_2845_);
v_subParts_2846_ = lean_ctor_get(v_x_2841_, 4);
lean_inc_ref(v_subParts_2846_);
lean_dec_ref(v_x_2841_);
v___x_2847_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_2848_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__3));
v___x_2849_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4);
v___x_2850_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_title_2842_);
v___x_2851_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = 0;
v___x_2853_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2853_, 0, v___x_2851_);
lean_ctor_set_uint8(v___x_2853_, sizeof(void*)*1, v___x_2852_);
v___x_2854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2848_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_2856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2854_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = lean_box(1);
v___x_2858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2856_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__6));
v___x_2860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2858_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
v___x_2861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
lean_ctor_set(v___x_2861_, 1, v___x_2847_);
v___x_2862_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7);
v___x_2863_ = l_String_quote(v_titleString_2843_);
v___x_2864_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
v___x_2865_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2862_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
lean_ctor_set_uint8(v___x_2866_, sizeof(void*)*1, v___x_2852_);
v___x_2867_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2861_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
lean_ctor_set(v___x_2868_, 1, v___x_2855_);
v___x_2869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
lean_ctor_set(v___x_2869_, 1, v___x_2857_);
v___x_2870_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__9));
v___x_2871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2869_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
v___x_2872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
lean_ctor_set(v___x_2872_, 1, v___x_2847_);
v___x_2873_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_2874_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_metadata_2844_);
lean_dec(v_metadata_2844_);
v___x_2875_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2873_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
v___x_2876_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
lean_ctor_set_uint8(v___x_2876_, sizeof(void*)*1, v___x_2852_);
v___x_2877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2872_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
v___x_2878_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
lean_ctor_set(v___x_2878_, 1, v___x_2855_);
v___x_2879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
lean_ctor_set(v___x_2879_, 1, v___x_2857_);
v___x_2880_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__11));
v___x_2881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2879_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v___x_2847_);
v___x_2883_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12);
v___x_2884_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_content_2845_);
v___x_2885_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2883_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
v___x_2886_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*1, v___x_2852_);
v___x_2887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2882_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
v___x_2888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
lean_ctor_set(v___x_2888_, 1, v___x_2855_);
v___x_2889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
lean_ctor_set(v___x_2889_, 1, v___x_2857_);
v___x_2890_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__14));
v___x_2891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2889_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
v___x_2892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
lean_ctor_set(v___x_2892_, 1, v___x_2847_);
v___x_2893_ = l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(v_subParts_2846_);
v___x_2894_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2873_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
v___x_2895_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
lean_ctor_set_uint8(v___x_2895_, sizeof(void*)*1, v___x_2852_);
v___x_2896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2892_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
v___x_2897_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_2898_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_2899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
lean_ctor_set(v___x_2899_, 1, v___x_2896_);
v___x_2900_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_2901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
v___x_2902_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2897_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
v___x_2903_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
lean_ctor_set_uint8(v___x_2903_, sizeof(void*)*1, v___x_2852_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(lean_object* v_x_2904_, lean_object* v_x_2905_, lean_object* v_x_2906_){
_start:
{
if (lean_obj_tag(v_x_2906_) == 0)
{
lean_dec(v_x_2904_);
return v_x_2905_;
}
else
{
lean_object* v_head_2907_; lean_object* v_tail_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2918_; 
v_head_2907_ = lean_ctor_get(v_x_2906_, 0);
v_tail_2908_ = lean_ctor_get(v_x_2906_, 1);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_x_2906_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2910_ = v_x_2906_;
v_isShared_2911_ = v_isSharedCheck_2918_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_tail_2908_);
lean_inc(v_head_2907_);
lean_dec(v_x_2906_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2918_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
lean_inc(v_x_2904_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set_tag(v___x_2910_, 5);
lean_ctor_set(v___x_2910_, 1, v_x_2904_);
lean_ctor_set(v___x_2910_, 0, v_x_2905_);
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_x_2905_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_x_2904_);
v___x_2913_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_2907_);
v___x_2915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2913_);
lean_ctor_set(v___x_2915_, 1, v___x_2914_);
v_x_2905_ = v___x_2915_;
v_x_2906_ = v_tail_2908_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(lean_object* v_x_2919_, lean_object* v_x_2920_){
_start:
{
lean_object* v_fst_2921_; lean_object* v_snd_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2932_; 
v_fst_2921_ = lean_ctor_get(v_x_2919_, 0);
v_snd_2922_ = lean_ctor_get(v_x_2919_, 1);
v_isSharedCheck_2932_ = !lean_is_exclusive(v_x_2919_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2924_ = v_x_2919_;
v_isShared_2925_ = v_isSharedCheck_2932_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_snd_2922_);
lean_inc(v_fst_2921_);
lean_dec(v_x_2919_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2932_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2926_ = l_Lean_instReprDeclarationRange_repr___redArg(v_fst_2921_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set_tag(v___x_2924_, 1);
lean_ctor_set(v___x_2924_, 1, v_x_2920_);
lean_ctor_set(v___x_2924_, 0, v___x_2926_);
v___x_2928_ = v___x_2924_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2926_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_x_2920_);
v___x_2928_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_snd_2922_);
v___x_2930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
lean_ctor_set(v___x_2930_, 1, v___x_2928_);
return v___x_2930_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(lean_object* v_x_2933_, lean_object* v_x_2934_, lean_object* v_x_2935_){
_start:
{
if (lean_obj_tag(v_x_2935_) == 0)
{
lean_dec(v_x_2933_);
return v_x_2934_;
}
else
{
lean_object* v_head_2936_; lean_object* v_tail_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2946_; 
v_head_2936_ = lean_ctor_get(v_x_2935_, 0);
v_tail_2937_ = lean_ctor_get(v_x_2935_, 1);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_x_2935_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2939_ = v_x_2935_;
v_isShared_2940_ = v_isSharedCheck_2946_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_tail_2937_);
lean_inc(v_head_2936_);
lean_dec(v_x_2935_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2946_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
lean_inc(v_x_2933_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set_tag(v___x_2939_, 5);
lean_ctor_set(v___x_2939_, 1, v_x_2933_);
lean_ctor_set(v___x_2939_, 0, v_x_2934_);
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_x_2934_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_x_2933_);
v___x_2942_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
lean_object* v___x_2943_; 
v___x_2943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
lean_ctor_set(v___x_2943_, 1, v_head_2936_);
v_x_2934_ = v___x_2943_;
v_x_2935_ = v_tail_2937_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(lean_object* v_x_2947_, lean_object* v_x_2948_){
_start:
{
if (lean_obj_tag(v_x_2947_) == 0)
{
lean_object* v___x_2949_; 
lean_dec(v_x_2948_);
v___x_2949_ = lean_box(0);
return v___x_2949_;
}
else
{
lean_object* v_tail_2950_; 
v_tail_2950_ = lean_ctor_get(v_x_2947_, 1);
if (lean_obj_tag(v_tail_2950_) == 0)
{
lean_object* v_head_2951_; 
lean_dec(v_x_2948_);
v_head_2951_ = lean_ctor_get(v_x_2947_, 0);
lean_inc(v_head_2951_);
lean_dec_ref_known(v_x_2947_, 2);
return v_head_2951_;
}
else
{
lean_object* v_head_2952_; lean_object* v___x_2953_; 
lean_inc(v_tail_2950_);
v_head_2952_ = lean_ctor_get(v_x_2947_, 0);
lean_inc(v_head_2952_);
lean_dec_ref_known(v_x_2947_, 2);
v___x_2953_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(v_x_2948_, v_head_2952_, v_tail_2950_);
return v___x_2953_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0));
v___x_2957_ = lean_string_length(v___x_2956_);
return v___x_2957_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2);
v___x_2959_ = lean_nat_to_int(v___x_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(lean_object* v_x_2964_){
_start:
{
lean_object* v_fst_2965_; lean_object* v_snd_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2988_; 
v_fst_2965_ = lean_ctor_get(v_x_2964_, 0);
v_snd_2966_ = lean_ctor_get(v_x_2964_, 1);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_x_2964_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2968_ = v_x_2964_;
v_isShared_2969_ = v_isSharedCheck_2988_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_snd_2966_);
lean_inc(v_fst_2965_);
lean_dec(v_x_2964_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2988_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
v___x_2970_ = l_Nat_reprFast(v_fst_2965_);
v___x_2971_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2970_);
v___x_2972_ = lean_box(0);
if (v_isShared_2969_ == 0)
{
lean_ctor_set_tag(v___x_2968_, 1);
lean_ctor_set(v___x_2968_, 1, v___x_2972_);
lean_ctor_set(v___x_2968_, 0, v___x_2971_);
v___x_2974_ = v___x_2968_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; uint8_t v___x_2985_; lean_object* v___x_2986_; 
v___x_2975_ = l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(v_snd_2966_, v___x_2974_);
v___x_2976_ = l_List_reverse___redArg(v___x_2975_);
v___x_2977_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2978_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(v___x_2976_, v___x_2977_);
v___x_2979_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3);
v___x_2980_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4));
v___x_2981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
lean_ctor_set(v___x_2981_, 1, v___x_2978_);
v___x_2982_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__5));
v___x_2983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2981_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
v___x_2984_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2979_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = 0;
v___x_2986_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2986_, 0, v___x_2984_);
lean_ctor_set_uint8(v___x_2986_, sizeof(void*)*1, v___x_2985_);
return v___x_2986_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(lean_object* v_x_2989_, lean_object* v_x_2990_, lean_object* v_x_2991_){
_start:
{
if (lean_obj_tag(v_x_2991_) == 0)
{
lean_dec(v_x_2989_);
return v_x_2990_;
}
else
{
lean_object* v_head_2992_; lean_object* v_tail_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3003_; 
v_head_2992_ = lean_ctor_get(v_x_2991_, 0);
v_tail_2993_ = lean_ctor_get(v_x_2991_, 1);
v_isSharedCheck_3003_ = !lean_is_exclusive(v_x_2991_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2995_ = v_x_2991_;
v_isShared_2996_ = v_isSharedCheck_3003_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_tail_2993_);
lean_inc(v_head_2992_);
lean_dec(v_x_2991_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3003_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
lean_inc(v_x_2989_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set_tag(v___x_2995_, 5);
lean_ctor_set(v___x_2995_, 1, v_x_2989_);
lean_ctor_set(v___x_2995_, 0, v_x_2990_);
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_x_2990_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v_x_2989_);
v___x_2998_ = v_reuseFailAlloc_3002_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_2992_);
v___x_3000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2998_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
v_x_2990_ = v___x_3000_;
v_x_2991_ = v_tail_2993_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(lean_object* v_x_3004_, lean_object* v_x_3005_, lean_object* v_x_3006_){
_start:
{
if (lean_obj_tag(v_x_3006_) == 0)
{
lean_dec(v_x_3004_);
return v_x_3005_;
}
else
{
lean_object* v_head_3007_; lean_object* v_tail_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3018_; 
v_head_3007_ = lean_ctor_get(v_x_3006_, 0);
v_tail_3008_ = lean_ctor_get(v_x_3006_, 1);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_x_3006_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3010_ = v_x_3006_;
v_isShared_3011_ = v_isSharedCheck_3018_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_tail_3008_);
lean_inc(v_head_3007_);
lean_dec(v_x_3006_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3018_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
lean_inc(v_x_3004_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set_tag(v___x_3010_, 5);
lean_ctor_set(v___x_3010_, 1, v_x_3004_);
lean_ctor_set(v___x_3010_, 0, v_x_3005_);
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_x_3005_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v_x_3004_);
v___x_3013_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3014_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3007_);
v___x_3015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v___x_3016_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(v_x_3004_, v___x_3015_, v_tail_3008_);
return v___x_3016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(lean_object* v_x_3019_, lean_object* v_x_3020_){
_start:
{
if (lean_obj_tag(v_x_3019_) == 0)
{
lean_object* v___x_3021_; 
lean_dec(v_x_3020_);
v___x_3021_ = lean_box(0);
return v___x_3021_;
}
else
{
lean_object* v_tail_3022_; 
v_tail_3022_ = lean_ctor_get(v_x_3019_, 1);
if (lean_obj_tag(v_tail_3022_) == 0)
{
lean_object* v_head_3023_; lean_object* v___x_3024_; 
lean_dec(v_x_3020_);
v_head_3023_ = lean_ctor_get(v_x_3019_, 0);
lean_inc(v_head_3023_);
lean_dec_ref_known(v_x_3019_, 2);
v___x_3024_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3023_);
return v___x_3024_;
}
else
{
lean_object* v_head_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
lean_inc(v_tail_3022_);
v_head_3025_ = lean_ctor_get(v_x_3019_, 0);
lean_inc(v_head_3025_);
lean_dec_ref_known(v_x_3019_, 2);
v___x_3026_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3025_);
v___x_3027_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(v_x_3020_, v___x_3026_, v_tail_3022_);
return v___x_3027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(lean_object* v_xs_3028_){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3029_ = lean_array_get_size(v_xs_3028_);
v___x_3030_ = lean_unsigned_to_nat(0u);
v___x_3031_ = lean_nat_dec_eq(v___x_3029_, v___x_3030_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3032_ = lean_array_to_list(v_xs_3028_);
v___x_3033_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3034_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(v___x_3032_, v___x_3033_);
v___x_3035_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_3036_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v___x_3034_);
v___x_3038_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_3039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3037_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
v___x_3040_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3035_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
v___x_3041_ = l_Std_Format_fill(v___x_3040_);
return v___x_3041_;
}
else
{
lean_object* v___x_3042_; 
lean_dec_ref(v_xs_3028_);
v___x_3042_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_3042_;
}
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = lean_unsigned_to_nat(20u);
v___x_3059_ = lean_nat_to_int(v___x_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(lean_object* v_x_3060_){
_start:
{
lean_object* v_text_3061_; lean_object* v_sections_3062_; lean_object* v_declarationRange_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v_text_3061_ = lean_ctor_get(v_x_3060_, 0);
lean_inc_ref(v_text_3061_);
v_sections_3062_ = lean_ctor_get(v_x_3060_, 1);
lean_inc_ref(v_sections_3062_);
v_declarationRange_3063_ = lean_ctor_get(v_x_3060_, 2);
lean_inc_ref(v_declarationRange_3063_);
lean_dec_ref(v_x_3060_);
v___x_3064_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3065_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__3));
v___x_3066_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_3067_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_text_3061_);
v___x_3068_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3066_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v___x_3069_ = 0;
v___x_3070_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3070_, 0, v___x_3068_);
lean_ctor_set_uint8(v___x_3070_, sizeof(void*)*1, v___x_3069_);
v___x_3071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3065_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3071_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
v___x_3074_ = lean_box(1);
v___x_3075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__5));
v___x_3077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3075_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
lean_ctor_set(v___x_3078_, 1, v___x_3064_);
v___x_3079_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3080_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(v_sections_3062_);
v___x_3081_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3079_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___x_3082_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
lean_ctor_set_uint8(v___x_3082_, sizeof(void*)*1, v___x_3069_);
v___x_3083_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3078_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
lean_ctor_set(v___x_3084_, 1, v___x_3072_);
v___x_3085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
lean_ctor_set(v___x_3085_, 1, v___x_3074_);
v___x_3086_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__7));
v___x_3087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3085_);
lean_ctor_set(v___x_3087_, 1, v___x_3086_);
v___x_3088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
lean_ctor_set(v___x_3088_, 1, v___x_3064_);
v___x_3089_ = lean_obj_once(&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8, &l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8_once, _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8);
v___x_3090_ = l_Lean_instReprDeclarationRange_repr___redArg(v_declarationRange_3063_);
v___x_3091_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3089_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
v___x_3092_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
lean_ctor_set_uint8(v___x_3092_, sizeof(void*)*1, v___x_3069_);
v___x_3093_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3088_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3095_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
lean_ctor_set(v___x_3096_, 1, v___x_3093_);
v___x_3097_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3096_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3094_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3100_, 0, v___x_3099_);
lean_ctor_set_uint8(v___x_3100_, sizeof(void*)*1, v___x_3069_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr(lean_object* v_x_3101_, lean_object* v_prec_3102_){
_start:
{
lean_object* v___x_3103_; 
v___x_3103_ = l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(v_x_3101_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___boxed(lean_object* v_x_3104_, lean_object* v_prec_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Lean_VersoModuleDocs_instReprSnippet_repr(v_x_3104_, v_prec_3105_);
lean_dec(v_prec_3105_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(lean_object* v_x_3107_, lean_object* v_x_3108_){
_start:
{
lean_object* v___x_3109_; 
v___x_3109_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_x_3107_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___boxed(lean_object* v_x_3110_, lean_object* v_x_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(v_x_3110_, v_x_3111_);
lean_dec(v_x_3111_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_3113_, lean_object* v_prec_3114_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_x_3113_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_x_3116_, lean_object* v_prec_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(v_x_3116_, v_prec_3117_);
lean_dec(v_prec_3117_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(lean_object* v_x_3119_, lean_object* v_prec_3120_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_x_3119_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_x_3122_, lean_object* v_prec_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(v_x_3122_, v_prec_3123_);
lean_dec(v_prec_3123_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(lean_object* v_x_3125_, lean_object* v_x_3126_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_3125_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___boxed(lean_object* v_x_3128_, lean_object* v_x_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(v_x_3128_, v_x_3129_);
lean_dec(v_x_3129_);
lean_dec(v_x_3128_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(lean_object* v_x_3131_, lean_object* v_prec_3132_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_x_3131_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___boxed(lean_object* v_x_3134_, lean_object* v_prec_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(v_x_3134_, v_prec_3135_);
lean_dec(v_prec_3135_);
return v_res_3136_;
}
}
uint8_t l_Lean_VersoModuleDocs_Snippet_canNestIn(lean_object* v_level_3139_, lean_object* v_snippet_3140_){
_start:
{
lean_object* v_sections_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; 
v_sections_3141_ = lean_ctor_get(v_snippet_3140_, 1);
v___x_3142_ = lean_unsigned_to_nat(0u);
v___x_3143_ = lean_array_get_size(v_sections_3141_);
v___x_3144_ = lean_nat_dec_lt(v___x_3142_, v___x_3143_);
if (v___x_3144_ == 0)
{
uint8_t v___x_3145_; 
v___x_3145_ = 1;
return v___x_3145_;
}
else
{
lean_object* v___x_3146_; lean_object* v_fst_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; uint8_t v___x_3150_; 
v___x_3146_ = lean_array_fget_borrowed(v_sections_3141_, v___x_3142_);
v_fst_3147_ = lean_ctor_get(v___x_3146_, 0);
v___x_3148_ = lean_unsigned_to_nat(1u);
v___x_3149_ = lean_nat_add(v_level_3139_, v___x_3148_);
v___x_3150_ = lean_nat_dec_le(v_fst_3147_, v___x_3149_);
lean_dec(v___x_3149_);
return v___x_3150_;
}
}
}
LEAN_EXPORT void l_Lean_VersoModuleDocs_Snippet_canNestIn_0interp(lean_interpreter_value* stack)
{
lean_object* v_level_3139_ = stack[0].m_obj;
lean_object* v_snippet_3140_ = stack[1].m_obj;
uint8_t v_res_3151_;
v_res_3151_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_level_3139_, v_snippet_3140_);
stack->m_num = v_res_3151_;
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_canNestIn___boxed(lean_object* v_level_3152_, lean_object* v_snippet_3153_){
_start:
{
uint8_t v_res_3154_; lean_object* v_r_3155_; 
v_res_3154_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_level_3152_, v_snippet_3153_);
lean_dec_ref(v_snippet_3153_);
lean_dec(v_level_3152_);
v_r_3155_ = lean_box(v_res_3154_);
return v_r_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting(lean_object* v_snippet_3156_){
_start:
{
lean_object* v_sections_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; uint8_t v___x_3161_; 
v_sections_3157_ = lean_ctor_get(v_snippet_3156_, 1);
v___x_3158_ = lean_array_get_size(v_sections_3157_);
v___x_3159_ = lean_unsigned_to_nat(1u);
v___x_3160_ = lean_nat_sub(v___x_3158_, v___x_3159_);
v___x_3161_ = lean_nat_dec_lt(v___x_3160_, v___x_3158_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; 
lean_dec(v___x_3160_);
v___x_3162_ = lean_box(0);
return v___x_3162_;
}
else
{
lean_object* v___x_3163_; lean_object* v_fst_3164_; lean_object* v___x_3165_; 
v___x_3163_ = lean_array_fget_borrowed(v_sections_3157_, v___x_3160_);
lean_dec(v___x_3160_);
v_fst_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_fst_3164_);
v___x_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3165_, 0, v_fst_3164_);
return v___x_3165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting___boxed(lean_object* v_snippet_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_3166_);
lean_dec_ref(v_snippet_3166_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addBlock(lean_object* v_snippet_3168_, lean_object* v_block_3169_){
_start:
{
lean_object* v_text_3170_; lean_object* v_sections_3171_; lean_object* v_declarationRange_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; uint8_t v___x_3175_; 
v_text_3170_ = lean_ctor_get(v_snippet_3168_, 0);
v_sections_3171_ = lean_ctor_get(v_snippet_3168_, 1);
v_declarationRange_3172_ = lean_ctor_get(v_snippet_3168_, 2);
v___x_3173_ = lean_array_get_size(v_sections_3171_);
v___x_3174_ = lean_unsigned_to_nat(0u);
v___x_3175_ = lean_nat_dec_eq(v___x_3173_, v___x_3174_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; lean_object* v___x_3177_; uint8_t v___x_3178_; 
v___x_3176_ = lean_unsigned_to_nat(1u);
v___x_3177_ = lean_nat_sub(v___x_3173_, v___x_3176_);
v___x_3178_ = lean_nat_dec_lt(v___x_3177_, v___x_3173_);
if (v___x_3178_ == 0)
{
lean_dec(v___x_3177_);
lean_dec_ref(v_block_3169_);
return v_snippet_3168_;
}
else
{
lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3222_; 
lean_inc_ref(v_declarationRange_3172_);
lean_inc_ref(v_sections_3171_);
lean_inc_ref(v_text_3170_);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_snippet_3168_);
if (v_isSharedCheck_3222_ == 0)
{
lean_object* v_unused_3223_; lean_object* v_unused_3224_; lean_object* v_unused_3225_; 
v_unused_3223_ = lean_ctor_get(v_snippet_3168_, 2);
lean_dec(v_unused_3223_);
v_unused_3224_ = lean_ctor_get(v_snippet_3168_, 1);
lean_dec(v_unused_3224_);
v_unused_3225_ = lean_ctor_get(v_snippet_3168_, 0);
lean_dec(v_unused_3225_);
v___x_3180_ = v_snippet_3168_;
v_isShared_3181_ = v_isSharedCheck_3222_;
goto v_resetjp_3179_;
}
else
{
lean_dec(v_snippet_3168_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3222_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v_v_3182_; lean_object* v_snd_3183_; lean_object* v_snd_3184_; lean_object* v_fst_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3220_; 
v_v_3182_ = lean_array_fget(v_sections_3171_, v___x_3177_);
v_snd_3183_ = lean_ctor_get(v_v_3182_, 1);
lean_inc(v_snd_3183_);
v_snd_3184_ = lean_ctor_get(v_snd_3183_, 1);
lean_inc(v_snd_3184_);
v_fst_3185_ = lean_ctor_get(v_v_3182_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v_v_3182_);
if (v_isSharedCheck_3220_ == 0)
{
lean_object* v_unused_3221_; 
v_unused_3221_ = lean_ctor_get(v_v_3182_, 1);
lean_dec(v_unused_3221_);
v___x_3187_ = v_v_3182_;
v_isShared_3188_ = v_isSharedCheck_3220_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_fst_3185_);
lean_dec(v_v_3182_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3220_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v_fst_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3218_; 
v_fst_3189_ = lean_ctor_get(v_snd_3183_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v_snd_3183_);
if (v_isSharedCheck_3218_ == 0)
{
lean_object* v_unused_3219_; 
v_unused_3219_ = lean_ctor_get(v_snd_3183_, 1);
lean_dec(v_unused_3219_);
v___x_3191_ = v_snd_3183_;
v_isShared_3192_ = v_isSharedCheck_3218_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_fst_3189_);
lean_dec(v_snd_3183_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3218_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v_title_3193_; lean_object* v_titleString_3194_; lean_object* v_metadata_3195_; lean_object* v_content_3196_; lean_object* v_subParts_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3217_; 
v_title_3193_ = lean_ctor_get(v_snd_3184_, 0);
v_titleString_3194_ = lean_ctor_get(v_snd_3184_, 1);
v_metadata_3195_ = lean_ctor_get(v_snd_3184_, 2);
v_content_3196_ = lean_ctor_get(v_snd_3184_, 3);
v_subParts_3197_ = lean_ctor_get(v_snd_3184_, 4);
v_isSharedCheck_3217_ = !lean_is_exclusive(v_snd_3184_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3199_ = v_snd_3184_;
v_isShared_3200_ = v_isSharedCheck_3217_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_subParts_3197_);
lean_inc(v_content_3196_);
lean_inc(v_metadata_3195_);
lean_inc(v_titleString_3194_);
lean_inc(v_title_3193_);
lean_dec(v_snd_3184_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3217_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3201_; lean_object* v_xs_x27_3202_; lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3201_ = lean_box(0);
v_xs_x27_3202_ = lean_array_fset(v_sections_3171_, v___x_3177_, v___x_3201_);
v___x_3203_ = lean_array_push(v_content_3196_, v_block_3169_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 3, v___x_3203_);
v___x_3205_ = v___x_3199_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_title_3193_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v_titleString_3194_);
lean_ctor_set(v_reuseFailAlloc_3216_, 2, v_metadata_3195_);
lean_ctor_set(v_reuseFailAlloc_3216_, 3, v___x_3203_);
lean_ctor_set(v_reuseFailAlloc_3216_, 4, v_subParts_3197_);
v___x_3205_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3207_; 
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v___x_3205_);
v___x_3207_ = v___x_3191_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_fst_3189_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v___x_3205_);
v___x_3207_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3209_; 
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 1, v___x_3207_);
v___x_3209_ = v___x_3187_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_fst_3185_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v___x_3207_);
v___x_3209_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
lean_object* v___x_3210_; lean_object* v___x_3212_; 
v___x_3210_ = lean_array_fset(v_xs_x27_3202_, v___x_3177_, v___x_3209_);
lean_dec(v___x_3177_);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 1, v___x_3210_);
v___x_3212_ = v___x_3180_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_text_3170_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v___x_3210_);
lean_ctor_set(v_reuseFailAlloc_3213_, 2, v_declarationRange_3172_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
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
lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3233_; 
lean_inc_ref(v_declarationRange_3172_);
lean_inc_ref(v_sections_3171_);
lean_inc_ref(v_text_3170_);
v_isSharedCheck_3233_ = !lean_is_exclusive(v_snippet_3168_);
if (v_isSharedCheck_3233_ == 0)
{
lean_object* v_unused_3234_; lean_object* v_unused_3235_; lean_object* v_unused_3236_; 
v_unused_3234_ = lean_ctor_get(v_snippet_3168_, 2);
lean_dec(v_unused_3234_);
v_unused_3235_ = lean_ctor_get(v_snippet_3168_, 1);
lean_dec(v_unused_3235_);
v_unused_3236_ = lean_ctor_get(v_snippet_3168_, 0);
lean_dec(v_unused_3236_);
v___x_3227_ = v_snippet_3168_;
v_isShared_3228_ = v_isSharedCheck_3233_;
goto v_resetjp_3226_;
}
else
{
lean_dec(v_snippet_3168_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3233_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3229_; lean_object* v___x_3231_; 
v___x_3229_ = lean_array_push(v_text_3170_, v_block_3169_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v___x_3229_);
v___x_3231_ = v___x_3227_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3229_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v_sections_3171_);
lean_ctor_set(v_reuseFailAlloc_3232_, 2, v_declarationRange_3172_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addPart(lean_object* v_snippet_3237_, lean_object* v_level_3238_, lean_object* v_range_3239_, lean_object* v_part_3240_){
_start:
{
lean_object* v_text_3241_; lean_object* v_sections_3242_; lean_object* v_declarationRange_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3253_; 
v_text_3241_ = lean_ctor_get(v_snippet_3237_, 0);
v_sections_3242_ = lean_ctor_get(v_snippet_3237_, 1);
v_declarationRange_3243_ = lean_ctor_get(v_snippet_3237_, 2);
v_isSharedCheck_3253_ = !lean_is_exclusive(v_snippet_3237_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3245_ = v_snippet_3237_;
v_isShared_3246_ = v_isSharedCheck_3253_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_declarationRange_3243_);
lean_inc(v_sections_3242_);
lean_inc(v_text_3241_);
lean_dec(v_snippet_3237_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3253_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3251_; 
v___x_3247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3247_, 0, v_range_3239_);
lean_ctor_set(v___x_3247_, 1, v_part_3240_);
v___x_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3248_, 0, v_level_3238_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = lean_array_push(v_sections_3242_, v___x_3248_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 1, v___x_3249_);
v___x_3251_ = v___x_3245_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_text_3241_);
lean_ctor_set(v_reuseFailAlloc_3252_, 1, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3252_, 2, v_declarationRange_3243_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0(void){
_start:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3254_ = lean_unsigned_to_nat(32u);
v___x_3255_ = lean_mk_empty_array_with_capacity(v___x_3254_);
v___x_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
return v___x_3256_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1(void){
_start:
{
size_t v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3257_ = ((size_t)5ULL);
v___x_3258_ = lean_unsigned_to_nat(0u);
v___x_3259_ = lean_unsigned_to_nat(32u);
v___x_3260_ = lean_mk_empty_array_with_capacity(v___x_3259_);
v___x_3261_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_3262_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
lean_ctor_set(v___x_3262_, 1, v___x_3260_);
lean_ctor_set(v___x_3262_, 2, v___x_3258_);
lean_ctor_set(v___x_3262_, 3, v___x_3258_);
lean_ctor_set_usize(v___x_3262_, 4, v___x_3257_);
return v___x_3262_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default(void){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__1, &l_Lean_instInhabitedVersoModuleDocs_default___closed__1_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1);
return v___x_3263_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs(void){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_instInhabitedVersoModuleDocs_default;
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(lean_object* v_as_3265_, lean_object* v_i_3266_){
_start:
{
lean_object* v_zero_3267_; uint8_t v_isZero_3268_; 
v_zero_3267_ = lean_unsigned_to_nat(0u);
v_isZero_3268_ = lean_nat_dec_eq(v_i_3266_, v_zero_3267_);
if (v_isZero_3268_ == 1)
{
lean_object* v___x_3269_; 
lean_dec(v_i_3266_);
v___x_3269_ = lean_box(0);
return v___x_3269_;
}
else
{
lean_object* v_one_3270_; lean_object* v_n_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v_one_3270_ = lean_unsigned_to_nat(1u);
v_n_3271_ = lean_nat_sub(v_i_3266_, v_one_3270_);
lean_dec(v_i_3266_);
v___x_3272_ = lean_array_fget_borrowed(v_as_3265_, v_n_3271_);
v___x_3273_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v___x_3272_);
if (lean_obj_tag(v___x_3273_) == 0)
{
v_i_3266_ = v_n_3271_;
goto _start;
}
else
{
lean_dec(v_n_3271_);
return v___x_3273_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg___boxed(lean_object* v_as_3275_, lean_object* v_i_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_as_3275_, v_i_3276_);
lean_dec_ref(v_as_3275_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(lean_object* v_as_3278_, lean_object* v_i_3279_){
_start:
{
lean_object* v_zero_3280_; uint8_t v_isZero_3281_; 
v_zero_3280_ = lean_unsigned_to_nat(0u);
v_isZero_3281_ = lean_nat_dec_eq(v_i_3279_, v_zero_3280_);
if (v_isZero_3281_ == 1)
{
lean_object* v___x_3282_; 
lean_dec(v_i_3279_);
v___x_3282_ = lean_box(0);
return v___x_3282_;
}
else
{
lean_object* v_one_3283_; lean_object* v_n_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v_one_3283_ = lean_unsigned_to_nat(1u);
v_n_3284_ = lean_nat_sub(v_i_3279_, v_one_3283_);
lean_dec(v_i_3279_);
v___x_3285_ = lean_array_fget_borrowed(v_as_3278_, v_n_3284_);
v___x_3286_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v___x_3285_);
if (lean_obj_tag(v___x_3286_) == 0)
{
v_i_3279_ = v_n_3284_;
goto _start;
}
else
{
lean_dec(v_n_3284_);
return v___x_3286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(lean_object* v_x_3288_){
_start:
{
if (lean_obj_tag(v_x_3288_) == 0)
{
lean_object* v_cs_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v_cs_3289_ = lean_ctor_get(v_x_3288_, 0);
v___x_3290_ = lean_array_get_size(v_cs_3289_);
v___x_3291_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_cs_3289_, v___x_3290_);
return v___x_3291_;
}
else
{
lean_object* v_vs_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v_vs_3292_ = lean_ctor_get(v_x_3288_, 0);
v___x_3293_ = lean_array_get_size(v_vs_3292_);
v___x_3294_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_vs_3292_, v___x_3293_);
return v___x_3294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1___boxed(lean_object* v_x_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v_x_3295_);
lean_dec_ref(v_x_3295_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_as_3297_, lean_object* v_i_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_as_3297_, v_i_3298_);
lean_dec_ref(v_as_3297_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(lean_object* v_t_3300_){
_start:
{
lean_object* v_root_3301_; lean_object* v_tail_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v_root_3301_ = lean_ctor_get(v_t_3300_, 0);
v_tail_3302_ = lean_ctor_get(v_t_3300_, 1);
v___x_3303_ = lean_array_get_size(v_tail_3302_);
v___x_3304_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_tail_3302_, v___x_3303_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v_root_3301_);
return v___x_3305_;
}
else
{
return v___x_3304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0___boxed(lean_object* v_t_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_t_3306_);
lean_dec_ref(v_t_3306_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_terminalNesting(lean_object* v_x_3308_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_x_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_terminalNesting___boxed(lean_object* v_x_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_Lean_VersoModuleDocs_terminalNesting(v_x_3310_);
lean_dec_ref(v_x_3310_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0(lean_object* v_as_3312_, lean_object* v_i_3313_, lean_object* v_a_3314_){
_start:
{
lean_object* v___x_3315_; 
v___x_3315_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_as_3312_, v_i_3313_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___boxed(lean_object* v_as_3316_, lean_object* v_i_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0(v_as_3316_, v_i_3317_, v_a_3318_);
lean_dec_ref(v_as_3316_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2(lean_object* v_as_3320_, lean_object* v_i_3321_, lean_object* v_a_3322_){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_as_3320_, v_i_3321_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___boxed(lean_object* v_as_3324_, lean_object* v_i_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2(v_as_3324_, v_i_3325_, v_a_3326_);
lean_dec_ref(v_as_3324_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0(lean_object* v___x_3334_, lean_object* v_v_3335_, lean_object* v_x_3336_){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3337_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___x_3338_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3339_ = lean_box(1);
v___x_3340_ = ((lean_object*)(l_Lean_instReprVersoModuleDocs___lam__0___closed__2));
v___x_3341_ = l_Lean_PersistentArray_toArray___redArg(v_v_3335_);
v___x_3342_ = l_Array_repr___redArg(v___x_3334_, v___x_3341_);
v___x_3343_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3340_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
v___x_3344_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3337_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = 0;
v___x_3346_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3346_, 0, v___x_3344_);
lean_ctor_set_uint8(v___x_3346_, sizeof(void*)*1, v___x_3345_);
lean_inc_ref(v___x_3346_);
v___x_3347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3338_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
v___x_3348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
lean_ctor_set(v___x_3348_, 1, v___x_3339_);
v___x_3349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
lean_ctor_set(v___x_3349_, 1, v___x_3346_);
v___x_3350_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3349_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
v___x_3352_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3337_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
v___x_3353_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
lean_ctor_set_uint8(v___x_3353_, sizeof(void*)*1, v___x_3345_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0___boxed(lean_object* v___x_3354_, lean_object* v_v_3355_, lean_object* v_x_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l_Lean_instReprVersoModuleDocs___lam__0(v___x_3354_, v_v_3355_, v_x_3356_);
lean_dec(v_x_3356_);
lean_dec_ref(v_v_3355_);
return v_res_3357_;
}
}
uint8_t l_Lean_VersoModuleDocs_isEmpty(lean_object* v_docs_3361_){
_start:
{
uint8_t v___x_3362_; 
v___x_3362_ = l_Lean_PersistentArray_isEmpty___redArg(v_docs_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT void l_Lean_VersoModuleDocs_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_docs_3361_ = stack[0].m_obj;
uint8_t v_res_3363_;
v_res_3363_ = l_Lean_VersoModuleDocs_isEmpty(v_docs_3361_);
stack->m_num = v_res_3363_;
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_isEmpty___boxed(lean_object* v_docs_3364_){
_start:
{
uint8_t v_res_3365_; lean_object* v_r_3366_; 
v_res_3365_ = l_Lean_VersoModuleDocs_isEmpty(v_docs_3364_);
lean_dec_ref(v_docs_3364_);
v_r_3366_ = lean_box(v_res_3365_);
return v_r_3366_;
}
}
uint8_t l_Lean_VersoModuleDocs_canAdd(lean_object* v_docs_3367_, lean_object* v_snippet_3368_){
_start:
{
lean_object* v___x_3369_; 
v___x_3369_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_3367_);
if (lean_obj_tag(v___x_3369_) == 1)
{
lean_object* v_val_3370_; uint8_t v___x_3371_; 
v_val_3370_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_val_3370_);
lean_dec_ref_known(v___x_3369_, 1);
v___x_3371_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_3370_, v_snippet_3368_);
lean_dec(v_val_3370_);
return v___x_3371_;
}
else
{
uint8_t v___x_3372_; 
lean_dec(v___x_3369_);
v___x_3372_ = 1;
return v___x_3372_;
}
}
}
LEAN_EXPORT void l_Lean_VersoModuleDocs_canAdd_0interp(lean_interpreter_value* stack)
{
lean_object* v_docs_3367_ = stack[0].m_obj;
lean_object* v_snippet_3368_ = stack[1].m_obj;
uint8_t v_res_3373_;
v_res_3373_ = l_Lean_VersoModuleDocs_canAdd(v_docs_3367_, v_snippet_3368_);
stack->m_num = v_res_3373_;
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_canAdd___boxed(lean_object* v_docs_3374_, lean_object* v_snippet_3375_){
_start:
{
uint8_t v_res_3376_; lean_object* v_r_3377_; 
v_res_3376_ = l_Lean_VersoModuleDocs_canAdd(v_docs_3374_, v_snippet_3375_);
lean_dec_ref(v_snippet_3375_);
lean_dec_ref(v_docs_3374_);
v_r_3377_ = lean_box(v_res_3376_);
return v_r_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add(lean_object* v_docs_3381_, lean_object* v_snippet_3382_){
_start:
{
uint8_t v___x_3383_; 
v___x_3383_ = l_Lean_VersoModuleDocs_canAdd(v_docs_3381_, v_snippet_3382_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; 
lean_dec_ref(v_snippet_3382_);
lean_dec_ref(v_docs_3381_);
v___x_3384_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__1));
return v___x_3384_;
}
else
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3385_ = l_Lean_PersistentArray_push___redArg(v_docs_3381_, v_snippet_3382_);
v___x_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
return v___x_3386_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(lean_object* v_msg_3387_){
_start:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3388_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_3389_ = lean_panic_fn_borrowed(v___x_3388_, v_msg_3387_);
return v___x_3389_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_add_x21___closed__2(void){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3392_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__0));
v___x_3393_ = lean_unsigned_to_nat(4u);
v___x_3394_ = lean_unsigned_to_nat(367u);
v___x_3395_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__1));
v___x_3396_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__0));
v___x_3397_ = l_mkPanicMessageWithDecl(v___x_3396_, v___x_3395_, v___x_3394_, v___x_3393_, v___x_3392_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add_x21(lean_object* v_docs_3398_, lean_object* v_snippet_3399_){
_start:
{
lean_object* v___x_3400_; 
v___x_3400_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_3398_);
if (lean_obj_tag(v___x_3400_) == 1)
{
lean_object* v_val_3401_; uint8_t v___x_3402_; 
v_val_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_val_3401_);
lean_dec_ref_known(v___x_3400_, 1);
v___x_3402_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_3401_, v_snippet_3399_);
lean_dec(v_val_3401_);
if (v___x_3402_ == 0)
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
lean_dec_ref(v_snippet_3399_);
lean_dec_ref(v_docs_3398_);
v___x_3403_ = lean_obj_once(&l_Lean_VersoModuleDocs_add_x21___closed__2, &l_Lean_VersoModuleDocs_add_x21___closed__2_once, _init_l_Lean_VersoModuleDocs_add_x21___closed__2);
v___x_3404_ = l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(v___x_3403_);
return v___x_3404_;
}
else
{
lean_object* v___x_3405_; 
v___x_3405_ = l_Lean_PersistentArray_push___redArg(v_docs_3398_, v_snippet_3399_);
return v___x_3405_;
}
}
else
{
lean_object* v___x_3406_; 
lean_dec(v___x_3400_);
v___x_3406_ = l_Lean_PersistentArray_push___redArg(v_docs_3398_, v_snippet_3399_);
return v___x_3406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(lean_object* v_ctx_3407_){
_start:
{
lean_object* v_context_3408_; lean_object* v___x_3409_; 
v_context_3408_ = lean_ctor_get(v_ctx_3407_, 2);
v___x_3409_ = lean_array_get_size(v_context_3408_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level___boxed(lean_object* v_ctx_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_3410_);
lean_dec_ref(v_ctx_3410_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(lean_object* v_ctx_3415_){
_start:
{
lean_object* v_content_3416_; lean_object* v_priorParts_3417_; lean_object* v_context_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3441_; 
v_content_3416_ = lean_ctor_get(v_ctx_3415_, 0);
v_priorParts_3417_ = lean_ctor_get(v_ctx_3415_, 1);
v_context_3418_ = lean_ctor_get(v_ctx_3415_, 2);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_ctx_3415_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3420_ = v_ctx_3415_;
v_isShared_3421_ = v_isSharedCheck_3441_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_context_3418_);
lean_inc(v_priorParts_3417_);
lean_inc(v_content_3416_);
lean_dec(v_ctx_3415_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3441_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; uint8_t v___x_3424_; 
v___x_3422_ = lean_array_get_size(v_context_3418_);
v___x_3423_ = lean_unsigned_to_nat(0u);
v___x_3424_ = lean_nat_dec_eq(v___x_3422_, v___x_3423_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v_last_3427_; lean_object* v_content_3428_; lean_object* v_priorParts_3429_; lean_object* v_titleString_3430_; lean_object* v_title_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3437_; 
v___x_3425_ = lean_unsigned_to_nat(1u);
v___x_3426_ = lean_nat_sub(v___x_3422_, v___x_3425_);
v_last_3427_ = lean_array_fget_borrowed(v_context_3418_, v___x_3426_);
lean_dec(v___x_3426_);
v_content_3428_ = lean_ctor_get(v_last_3427_, 0);
lean_inc_ref(v_content_3428_);
v_priorParts_3429_ = lean_ctor_get(v_last_3427_, 1);
v_titleString_3430_ = lean_ctor_get(v_last_3427_, 2);
v_title_3431_ = lean_ctor_get(v_last_3427_, 3);
v___x_3432_ = lean_box(0);
lean_inc_ref(v_titleString_3430_);
lean_inc_ref(v_title_3431_);
v___x_3433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3433_, 0, v_title_3431_);
lean_ctor_set(v___x_3433_, 1, v_titleString_3430_);
lean_ctor_set(v___x_3433_, 2, v___x_3432_);
lean_ctor_set(v___x_3433_, 3, v_content_3416_);
lean_ctor_set(v___x_3433_, 4, v_priorParts_3417_);
lean_inc_ref(v_priorParts_3429_);
v___x_3434_ = lean_array_push(v_priorParts_3429_, v___x_3433_);
v___x_3435_ = lean_array_pop(v_context_3418_);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 2, v___x_3435_);
lean_ctor_set(v___x_3420_, 1, v___x_3434_);
lean_ctor_set(v___x_3420_, 0, v_content_3428_);
v___x_3437_ = v___x_3420_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_content_3428_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v___x_3434_);
lean_ctor_set(v_reuseFailAlloc_3439_, 2, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
lean_object* v___x_3438_; 
v___x_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
return v___x_3438_;
}
}
else
{
lean_object* v___x_3440_; 
lean_del_object(v___x_3420_);
lean_dec_ref(v_context_3418_);
lean_dec_ref(v_priorParts_3417_);
lean_dec_ref(v_content_3416_);
v___x_3440_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__1));
return v___x_3440_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(lean_object* v_ctx_3442_){
_start:
{
lean_object* v_context_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; 
v_context_3443_ = lean_ctor_get(v_ctx_3442_, 2);
v___x_3444_ = lean_array_get_size(v_context_3443_);
v___x_3445_ = lean_unsigned_to_nat(0u);
v___x_3446_ = lean_nat_dec_eq(v___x_3444_, v___x_3445_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; 
v___x_3447_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_3442_);
if (lean_obj_tag(v___x_3447_) == 0)
{
return v___x_3447_;
}
else
{
lean_object* v_a_3448_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3448_);
lean_dec_ref_known(v___x_3447_, 1);
v_ctx_3442_ = v_a_3448_;
goto _start;
}
}
else
{
lean_object* v___x_3450_; 
v___x_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3450_, 0, v_ctx_3442_);
return v___x_3450_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(lean_object* v_ctx_3453_, lean_object* v_partLevel_3454_, lean_object* v_part_3455_){
_start:
{
lean_object* v___x_3456_; uint8_t v___x_3457_; 
v___x_3456_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_3453_);
v___x_3457_ = lean_nat_dec_lt(v___x_3456_, v_partLevel_3454_);
if (v___x_3457_ == 0)
{
uint8_t v___x_3458_; 
v___x_3458_ = lean_nat_dec_eq(v_partLevel_3454_, v___x_3456_);
lean_dec(v___x_3456_);
if (v___x_3458_ == 0)
{
lean_object* v___x_3459_; 
v___x_3459_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_3453_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_dec_ref(v_part_3455_);
lean_dec(v_partLevel_3454_);
return v___x_3459_;
}
else
{
lean_object* v_a_3460_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3459_, 1);
v_ctx_3453_ = v_a_3460_;
goto _start;
}
}
else
{
lean_object* v_content_3462_; lean_object* v_priorParts_3463_; lean_object* v_context_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3473_; 
lean_dec(v_partLevel_3454_);
v_content_3462_ = lean_ctor_get(v_ctx_3453_, 0);
v_priorParts_3463_ = lean_ctor_get(v_ctx_3453_, 1);
v_context_3464_ = lean_ctor_get(v_ctx_3453_, 2);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_ctx_3453_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3466_ = v_ctx_3453_;
v_isShared_3467_ = v_isSharedCheck_3473_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_context_3464_);
lean_inc(v_priorParts_3463_);
lean_inc(v_content_3462_);
lean_dec(v_ctx_3453_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3473_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3468_; lean_object* v___x_3470_; 
v___x_3468_ = lean_array_push(v_priorParts_3463_, v_part_3455_);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 1, v___x_3468_);
v___x_3470_ = v___x_3466_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_content_3462_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v___x_3468_);
lean_ctor_set(v_reuseFailAlloc_3472_, 2, v_context_3464_);
v___x_3470_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v___x_3471_; 
v___x_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
return v___x_3471_;
}
}
}
}
else
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
lean_dec_ref(v_part_3455_);
lean_dec_ref(v_ctx_3453_);
v___x_3474_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__0));
v___x_3475_ = l_Nat_reprFast(v___x_3456_);
v___x_3476_ = lean_string_append(v___x_3474_, v___x_3475_);
lean_dec_ref(v___x_3475_);
v___x_3477_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__1));
v___x_3478_ = lean_string_append(v___x_3476_, v___x_3477_);
v___x_3479_ = l_Nat_reprFast(v_partLevel_3454_);
v___x_3480_ = lean_string_append(v___x_3478_, v___x_3479_);
lean_dec_ref(v___x_3479_);
v___x_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
return v___x_3481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(lean_object* v_ctx_3485_, lean_object* v_blocks_3486_){
_start:
{
lean_object* v_content_3487_; lean_object* v_priorParts_3488_; lean_object* v_context_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3502_; 
v_content_3487_ = lean_ctor_get(v_ctx_3485_, 0);
v_priorParts_3488_ = lean_ctor_get(v_ctx_3485_, 1);
v_context_3489_ = lean_ctor_get(v_ctx_3485_, 2);
v_isSharedCheck_3502_ = !lean_is_exclusive(v_ctx_3485_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3491_ = v_ctx_3485_;
v_isShared_3492_ = v_isSharedCheck_3502_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_context_3489_);
lean_inc(v_priorParts_3488_);
lean_inc(v_content_3487_);
lean_dec(v_ctx_3485_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3502_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; uint8_t v___x_3495_; 
v___x_3493_ = lean_array_get_size(v_priorParts_3488_);
v___x_3494_ = lean_unsigned_to_nat(0u);
v___x_3495_ = lean_nat_dec_eq(v___x_3493_, v___x_3494_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3496_; 
lean_del_object(v___x_3491_);
lean_dec_ref(v_context_3489_);
lean_dec_ref(v_priorParts_3488_);
lean_dec_ref(v_content_3487_);
v___x_3496_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__1));
return v___x_3496_;
}
else
{
lean_object* v___x_3497_; lean_object* v___x_3499_; 
v___x_3497_ = l_Array_append___redArg(v_content_3487_, v_blocks_3486_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 0, v___x_3497_);
v___x_3499_ = v___x_3491_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v_priorParts_3488_);
lean_ctor_set(v_reuseFailAlloc_3501_, 2, v_context_3489_);
v___x_3499_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3500_; 
v___x_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
return v___x_3500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___boxed(lean_object* v_ctx_3503_, lean_object* v_blocks_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_3503_, v_blocks_3504_);
lean_dec_ref(v_blocks_3504_);
return v_res_3505_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(lean_object* v_as_3506_, size_t v_sz_3507_, size_t v_i_3508_, lean_object* v_b_3509_){
_start:
{
uint8_t v___x_3510_; 
v___x_3510_ = lean_usize_dec_lt(v_i_3508_, v_sz_3507_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3511_; 
v___x_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3511_, 0, v_b_3509_);
return v___x_3511_;
}
else
{
lean_object* v_a_3512_; lean_object* v_snd_3513_; lean_object* v_fst_3514_; lean_object* v_snd_3515_; lean_object* v___x_3516_; 
v_a_3512_ = lean_array_uget_borrowed(v_as_3506_, v_i_3508_);
v_snd_3513_ = lean_ctor_get(v_a_3512_, 1);
v_fst_3514_ = lean_ctor_get(v_a_3512_, 0);
v_snd_3515_ = lean_ctor_get(v_snd_3513_, 1);
lean_inc(v_snd_3515_);
lean_inc(v_fst_3514_);
v___x_3516_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(v_b_3509_, v_fst_3514_, v_snd_3515_);
if (lean_obj_tag(v___x_3516_) == 0)
{
return v___x_3516_;
}
else
{
lean_object* v_a_3517_; size_t v___x_3518_; size_t v___x_3519_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_a_3517_);
lean_dec_ref_known(v___x_3516_, 1);
v___x_3518_ = ((size_t)1ULL);
v___x_3519_ = lean_usize_add(v_i_3508_, v___x_3518_);
v_i_3508_ = v___x_3519_;
v_b_3509_ = v_a_3517_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3506_ = stack[0].m_obj;
size_t v_sz_3507_ = stack[1].m_num;
size_t v_i_3508_ = stack[2].m_num;
lean_object* v_b_3509_ = stack[3].m_obj;
lean_object* v_res_3521_;
v_res_3521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_as_3506_, v_sz_3507_, v_i_3508_, v_b_3509_);
stack->m_obj
 = v_res_3521_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0___boxed(lean_object* v_as_3522_, lean_object* v_sz_3523_, lean_object* v_i_3524_, lean_object* v_b_3525_){
_start:
{
size_t v_sz_boxed_3526_; size_t v_i_boxed_3527_; lean_object* v_res_3528_; 
v_sz_boxed_3526_ = lean_unbox_usize(v_sz_3523_);
lean_dec(v_sz_3523_);
v_i_boxed_3527_ = lean_unbox_usize(v_i_3524_);
lean_dec(v_i_3524_);
v_res_3528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_as_3522_, v_sz_boxed_3526_, v_i_boxed_3527_, v_b_3525_);
lean_dec_ref(v_as_3522_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(lean_object* v_ctx_3529_, lean_object* v_snippet_3530_){
_start:
{
lean_object* v_text_3531_; lean_object* v_sections_3532_; lean_object* v___x_3533_; 
v_text_3531_ = lean_ctor_get(v_snippet_3530_, 0);
v_sections_3532_ = lean_ctor_get(v_snippet_3530_, 1);
v___x_3533_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_3529_, v_text_3531_);
if (lean_obj_tag(v___x_3533_) == 0)
{
return v___x_3533_;
}
else
{
lean_object* v_a_3534_; size_t v_sz_3535_; size_t v___x_3536_; lean_object* v___x_3537_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v___x_3533_, 1);
v_sz_3535_ = lean_array_size(v_sections_3532_);
v___x_3536_ = ((size_t)0ULL);
v___x_3537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_sections_3532_, v_sz_3535_, v___x_3536_, v_a_3534_);
return v___x_3537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet___boxed(lean_object* v_ctx_3538_, lean_object* v_snippet_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_ctx_3538_, v_snippet_3539_);
lean_dec_ref(v_snippet_3539_);
return v_res_3540_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(lean_object* v_as_3541_, size_t v_sz_3542_, size_t v_i_3543_, lean_object* v_b_3544_){
_start:
{
uint8_t v___x_3545_; 
v___x_3545_ = lean_usize_dec_lt(v_i_3543_, v_sz_3542_);
if (v___x_3545_ == 0)
{
lean_object* v___x_3546_; 
v___x_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3546_, 0, v_b_3544_);
return v___x_3546_;
}
else
{
lean_object* v_snd_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3569_; 
v_snd_3547_ = lean_ctor_get(v_b_3544_, 1);
v_isSharedCheck_3569_ = !lean_is_exclusive(v_b_3544_);
if (v_isSharedCheck_3569_ == 0)
{
lean_object* v_unused_3570_; 
v_unused_3570_ = lean_ctor_get(v_b_3544_, 0);
lean_dec(v_unused_3570_);
v___x_3549_ = v_b_3544_;
v_isShared_3550_ = v_isSharedCheck_3569_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_snd_3547_);
lean_dec(v_b_3544_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3569_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v_a_3551_; lean_object* v___x_3552_; 
v_a_3551_ = lean_array_uget_borrowed(v_as_3541_, v_i_3543_);
v___x_3552_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_3547_, v_a_3551_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_del_object(v___x_3549_);
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3552_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3552_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3562_; lean_object* v___x_3564_; 
v_a_3561_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3552_, 1);
v___x_3562_ = lean_box(0);
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 1, v_a_3561_);
lean_ctor_set(v___x_3549_, 0, v___x_3562_);
v___x_3564_ = v___x_3549_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3562_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_a_3561_);
v___x_3564_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
size_t v___x_3565_; size_t v___x_3566_; 
v___x_3565_ = ((size_t)1ULL);
v___x_3566_ = lean_usize_add(v_i_3543_, v___x_3565_);
v_i_3543_ = v___x_3566_;
v_b_3544_ = v___x_3564_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3541_ = stack[0].m_obj;
size_t v_sz_3542_ = stack[1].m_num;
size_t v_i_3543_ = stack[2].m_num;
lean_object* v_b_3544_ = stack[3].m_obj;
lean_object* v_res_3571_;
v_res_3571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_3541_, v_sz_3542_, v_i_3543_, v_b_3544_);
stack->m_obj
 = v_res_3571_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4___boxed(lean_object* v_as_3572_, lean_object* v_sz_3573_, lean_object* v_i_3574_, lean_object* v_b_3575_){
_start:
{
size_t v_sz_boxed_3576_; size_t v_i_boxed_3577_; lean_object* v_res_3578_; 
v_sz_boxed_3576_ = lean_unbox_usize(v_sz_3573_);
lean_dec(v_sz_3573_);
v_i_boxed_3577_ = lean_unbox_usize(v_i_3574_);
lean_dec(v_i_3574_);
v_res_3578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_3572_, v_sz_boxed_3576_, v_i_boxed_3577_, v_b_3575_);
lean_dec_ref(v_as_3572_);
return v_res_3578_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(lean_object* v_as_3579_, size_t v_sz_3580_, size_t v_i_3581_, lean_object* v_b_3582_){
_start:
{
uint8_t v___x_3583_; 
v___x_3583_ = lean_usize_dec_lt(v_i_3581_, v_sz_3580_);
if (v___x_3583_ == 0)
{
lean_object* v___x_3584_; 
v___x_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3584_, 0, v_b_3582_);
return v___x_3584_;
}
else
{
lean_object* v_snd_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3607_; 
v_snd_3585_ = lean_ctor_get(v_b_3582_, 1);
v_isSharedCheck_3607_ = !lean_is_exclusive(v_b_3582_);
if (v_isSharedCheck_3607_ == 0)
{
lean_object* v_unused_3608_; 
v_unused_3608_ = lean_ctor_get(v_b_3582_, 0);
lean_dec(v_unused_3608_);
v___x_3587_ = v_b_3582_;
v_isShared_3588_ = v_isSharedCheck_3607_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_snd_3585_);
lean_dec(v_b_3582_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3607_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v_a_3589_; lean_object* v___x_3590_; 
v_a_3589_ = lean_array_uget_borrowed(v_as_3579_, v_i_3581_);
v___x_3590_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_3585_, v_a_3589_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
lean_del_object(v___x_3587_);
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3590_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3590_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3600_; lean_object* v___x_3602_; 
v_a_3599_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3590_, 1);
v___x_3600_ = lean_box(0);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 1, v_a_3599_);
lean_ctor_set(v___x_3587_, 0, v___x_3600_);
v___x_3602_ = v___x_3587_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3600_);
lean_ctor_set(v_reuseFailAlloc_3606_, 1, v_a_3599_);
v___x_3602_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
size_t v___x_3603_; size_t v___x_3604_; lean_object* v___x_3605_; 
v___x_3603_ = ((size_t)1ULL);
v___x_3604_ = lean_usize_add(v_i_3581_, v___x_3603_);
v___x_3605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_3579_, v_sz_3580_, v___x_3604_, v___x_3602_);
return v___x_3605_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3579_ = stack[0].m_obj;
size_t v_sz_3580_ = stack[1].m_num;
size_t v_i_3581_ = stack[2].m_num;
lean_object* v_b_3582_ = stack[3].m_obj;
lean_object* v_res_3609_;
v_res_3609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_as_3579_, v_sz_3580_, v_i_3581_, v_b_3582_);
stack->m_obj
 = v_res_3609_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1___boxed(lean_object* v_as_3610_, lean_object* v_sz_3611_, lean_object* v_i_3612_, lean_object* v_b_3613_){
_start:
{
size_t v_sz_boxed_3614_; size_t v_i_boxed_3615_; lean_object* v_res_3616_; 
v_sz_boxed_3614_ = lean_unbox_usize(v_sz_3611_);
lean_dec(v_sz_3611_);
v_i_boxed_3615_ = lean_unbox_usize(v_i_3612_);
lean_dec(v_i_3612_);
v_res_3616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_as_3610_, v_sz_boxed_3614_, v_i_boxed_3615_, v_b_3613_);
lean_dec_ref(v_as_3610_);
return v_res_3616_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_3617_, size_t v_sz_3618_, size_t v_i_3619_, lean_object* v_b_3620_){
_start:
{
uint8_t v___x_3621_; 
v___x_3621_ = lean_usize_dec_lt(v_i_3619_, v_sz_3618_);
if (v___x_3621_ == 0)
{
lean_object* v___x_3622_; 
v___x_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3622_, 0, v_b_3620_);
return v___x_3622_;
}
else
{
lean_object* v_snd_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3645_; 
v_snd_3623_ = lean_ctor_get(v_b_3620_, 1);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_b_3620_);
if (v_isSharedCheck_3645_ == 0)
{
lean_object* v_unused_3646_; 
v_unused_3646_ = lean_ctor_get(v_b_3620_, 0);
lean_dec(v_unused_3646_);
v___x_3625_ = v_b_3620_;
v_isShared_3626_ = v_isSharedCheck_3645_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_snd_3623_);
lean_dec(v_b_3620_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3645_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v_a_3627_; lean_object* v___x_3628_; 
v_a_3627_ = lean_array_uget_borrowed(v_as_3617_, v_i_3619_);
v___x_3628_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_3623_, v_a_3627_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
lean_del_object(v___x_3625_);
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3631_ = v___x_3628_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3628_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3634_; 
if (v_isShared_3632_ == 0)
{
v___x_3634_ = v___x_3631_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
else
{
lean_object* v_a_3637_; lean_object* v___x_3638_; lean_object* v___x_3640_; 
v_a_3637_ = lean_ctor_get(v___x_3628_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3628_, 1);
v___x_3638_ = lean_box(0);
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 1, v_a_3637_);
lean_ctor_set(v___x_3625_, 0, v___x_3638_);
v___x_3640_ = v___x_3625_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3638_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_a_3637_);
v___x_3640_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
size_t v___x_3641_; size_t v___x_3642_; 
v___x_3641_ = ((size_t)1ULL);
v___x_3642_ = lean_usize_add(v_i_3619_, v___x_3641_);
v_i_3619_ = v___x_3642_;
v_b_3620_ = v___x_3640_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3617_ = stack[0].m_obj;
size_t v_sz_3618_ = stack[1].m_num;
size_t v_i_3619_ = stack[2].m_num;
lean_object* v_b_3620_ = stack[3].m_obj;
lean_object* v_res_3647_;
v_res_3647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_3617_, v_sz_3618_, v_i_3619_, v_b_3620_);
stack->m_obj
 = v_res_3647_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_3648_, lean_object* v_sz_3649_, lean_object* v_i_3650_, lean_object* v_b_3651_){
_start:
{
size_t v_sz_boxed_3652_; size_t v_i_boxed_3653_; lean_object* v_res_3654_; 
v_sz_boxed_3652_ = lean_unbox_usize(v_sz_3649_);
lean_dec(v_sz_3649_);
v_i_boxed_3653_ = lean_unbox_usize(v_i_3650_);
lean_dec(v_i_3650_);
v_res_3654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_3648_, v_sz_boxed_3652_, v_i_boxed_3653_, v_b_3651_);
lean_dec_ref(v_as_3648_);
return v_res_3654_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(lean_object* v_as_3655_, size_t v_sz_3656_, size_t v_i_3657_, lean_object* v_b_3658_){
_start:
{
uint8_t v___x_3659_; 
v___x_3659_ = lean_usize_dec_lt(v_i_3657_, v_sz_3656_);
if (v___x_3659_ == 0)
{
lean_object* v___x_3660_; 
v___x_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3660_, 0, v_b_3658_);
return v___x_3660_;
}
else
{
lean_object* v_snd_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3683_; 
v_snd_3661_ = lean_ctor_get(v_b_3658_, 1);
v_isSharedCheck_3683_ = !lean_is_exclusive(v_b_3658_);
if (v_isSharedCheck_3683_ == 0)
{
lean_object* v_unused_3684_; 
v_unused_3684_ = lean_ctor_get(v_b_3658_, 0);
lean_dec(v_unused_3684_);
v___x_3663_ = v_b_3658_;
v_isShared_3664_ = v_isSharedCheck_3683_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_snd_3661_);
lean_dec(v_b_3658_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3683_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v_a_3665_; lean_object* v___x_3666_; 
v_a_3665_ = lean_array_uget_borrowed(v_as_3655_, v_i_3657_);
v___x_3666_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_3661_, v_a_3665_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
lean_del_object(v___x_3663_);
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3666_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3666_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3676_; lean_object* v___x_3678_; 
v_a_3675_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3675_);
lean_dec_ref_known(v___x_3666_, 1);
v___x_3676_ = lean_box(0);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 1, v_a_3675_);
lean_ctor_set(v___x_3663_, 0, v___x_3676_);
v___x_3678_ = v___x_3663_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v_a_3675_);
v___x_3678_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
size_t v___x_3679_; size_t v___x_3680_; lean_object* v___x_3681_; 
v___x_3679_ = ((size_t)1ULL);
v___x_3680_ = lean_usize_add(v_i_3657_, v___x_3679_);
v___x_3681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_3655_, v_sz_3656_, v___x_3680_, v___x_3678_);
return v___x_3681_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3655_ = stack[0].m_obj;
size_t v_sz_3656_ = stack[1].m_num;
size_t v_i_3657_ = stack[2].m_num;
lean_object* v_b_3658_ = stack[3].m_obj;
lean_object* v_res_3685_;
v_res_3685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_as_3655_, v_sz_3656_, v_i_3657_, v_b_3658_);
stack->m_obj
 = v_res_3685_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3686_, lean_object* v_sz_3687_, lean_object* v_i_3688_, lean_object* v_b_3689_){
_start:
{
size_t v_sz_boxed_3690_; size_t v_i_boxed_3691_; lean_object* v_res_3692_; 
v_sz_boxed_3690_ = lean_unbox_usize(v_sz_3687_);
lean_dec(v_sz_3687_);
v_i_boxed_3691_ = lean_unbox_usize(v_i_3688_);
lean_dec(v_i_3688_);
v_res_3692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_as_3686_, v_sz_boxed_3690_, v_i_boxed_3691_, v_b_3689_);
lean_dec_ref(v_as_3686_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(lean_object* v_init_3693_, lean_object* v_n_3694_, lean_object* v_b_3695_){
_start:
{
if (lean_obj_tag(v_n_3694_) == 0)
{
lean_object* v_cs_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; size_t v_sz_3699_; size_t v___x_3700_; lean_object* v___x_3701_; 
v_cs_3696_ = lean_ctor_get(v_n_3694_, 0);
v___x_3697_ = lean_box(0);
v___x_3698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3697_);
lean_ctor_set(v___x_3698_, 1, v_b_3695_);
v_sz_3699_ = lean_array_size(v_cs_3696_);
v___x_3700_ = ((size_t)0ULL);
v___x_3701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_init_3693_, v_cs_3696_, v_sz_3699_, v___x_3700_, v___x_3698_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3709_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3704_ = v___x_3701_;
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3701_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3705_ == 0)
{
v___x_3707_ = v___x_3704_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_a_3702_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
else
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3724_; 
v_a_3710_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3712_ = v___x_3701_;
v_isShared_3713_ = v_isSharedCheck_3724_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3701_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3724_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v_fst_3714_; 
v_fst_3714_ = lean_ctor_get(v_a_3710_, 0);
if (lean_obj_tag(v_fst_3714_) == 0)
{
lean_object* v_snd_3715_; lean_object* v___x_3716_; lean_object* v___x_3718_; 
v_snd_3715_ = lean_ctor_get(v_a_3710_, 1);
lean_inc(v_snd_3715_);
lean_dec(v_a_3710_);
v___x_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3716_, 0, v_snd_3715_);
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 0, v___x_3716_);
v___x_3718_ = v___x_3712_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
else
{
lean_object* v_val_3720_; lean_object* v___x_3722_; 
lean_inc_ref(v_fst_3714_);
lean_dec(v_a_3710_);
v_val_3720_ = lean_ctor_get(v_fst_3714_, 0);
lean_inc(v_val_3720_);
lean_dec_ref_known(v_fst_3714_, 1);
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 0, v_val_3720_);
v___x_3722_ = v___x_3712_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_val_3720_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
}
else
{
lean_object* v_vs_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; size_t v_sz_3728_; size_t v___x_3729_; lean_object* v___x_3730_; 
v_vs_3725_ = lean_ctor_get(v_n_3694_, 0);
v___x_3726_ = lean_box(0);
v___x_3727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3726_);
lean_ctor_set(v___x_3727_, 1, v_b_3695_);
v_sz_3728_ = lean_array_size(v_vs_3725_);
v___x_3729_ = ((size_t)0ULL);
v___x_3730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_vs_3725_, v_sz_3728_, v___x_3729_, v___x_3727_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3730_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3730_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3753_; 
v_a_3739_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3741_ = v___x_3730_;
v_isShared_3742_ = v_isSharedCheck_3753_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3730_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3753_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v_fst_3743_; 
v_fst_3743_ = lean_ctor_get(v_a_3739_, 0);
if (lean_obj_tag(v_fst_3743_) == 0)
{
lean_object* v_snd_3744_; lean_object* v___x_3745_; lean_object* v___x_3747_; 
v_snd_3744_ = lean_ctor_get(v_a_3739_, 1);
lean_inc(v_snd_3744_);
lean_dec(v_a_3739_);
v___x_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3745_, 0, v_snd_3744_);
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 0, v___x_3745_);
v___x_3747_ = v___x_3741_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
else
{
lean_object* v_val_3749_; lean_object* v___x_3751_; 
lean_inc_ref(v_fst_3743_);
lean_dec(v_a_3739_);
v_val_3749_ = lean_ctor_get(v_fst_3743_, 0);
lean_inc(v_val_3749_);
lean_dec_ref_known(v_fst_3743_, 1);
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 0, v_val_3749_);
v___x_3751_ = v___x_3741_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_val_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(lean_object* v_init_3754_, lean_object* v_as_3755_, size_t v_sz_3756_, size_t v_i_3757_, lean_object* v_b_3758_){
_start:
{
uint8_t v___x_3759_; 
v___x_3759_ = lean_usize_dec_lt(v_i_3757_, v_sz_3756_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; 
v___x_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3760_, 0, v_b_3758_);
return v___x_3760_;
}
else
{
lean_object* v_snd_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3795_; 
v_snd_3761_ = lean_ctor_get(v_b_3758_, 1);
v_isSharedCheck_3795_ = !lean_is_exclusive(v_b_3758_);
if (v_isSharedCheck_3795_ == 0)
{
lean_object* v_unused_3796_; 
v_unused_3796_ = lean_ctor_get(v_b_3758_, 0);
lean_dec(v_unused_3796_);
v___x_3763_ = v_b_3758_;
v_isShared_3764_ = v_isSharedCheck_3795_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_snd_3761_);
lean_dec(v_b_3758_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3795_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v_a_3765_; lean_object* v___x_3766_; 
v_a_3765_ = lean_array_uget_borrowed(v_as_3755_, v_i_3757_);
lean_inc(v_snd_3761_);
v___x_3766_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_3754_, v_a_3765_, v_snd_3761_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_del_object(v___x_3763_);
lean_dec(v_snd_3761_);
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3766_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3766_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3794_; 
v_a_3775_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3777_ = v___x_3766_;
v_isShared_3778_ = v_isSharedCheck_3794_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3766_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3794_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
if (lean_obj_tag(v_a_3775_) == 0)
{
lean_object* v___x_3779_; lean_object* v___x_3781_; 
v___x_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3779_, 0, v_a_3775_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v___x_3779_);
v___x_3781_ = v___x_3763_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3779_);
lean_ctor_set(v_reuseFailAlloc_3785_, 1, v_snd_3761_);
v___x_3781_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
lean_object* v___x_3783_; 
if (v_isShared_3778_ == 0)
{
lean_ctor_set(v___x_3777_, 0, v___x_3781_);
v___x_3783_ = v___x_3777_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3781_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3787_; lean_object* v___x_3789_; 
lean_del_object(v___x_3777_);
lean_dec(v_snd_3761_);
v_a_3786_ = lean_ctor_get(v_a_3775_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v_a_3775_, 1);
v___x_3787_ = lean_box(0);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 1, v_a_3786_);
lean_ctor_set(v___x_3763_, 0, v___x_3787_);
v___x_3789_ = v___x_3763_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v___x_3787_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_a_3786_);
v___x_3789_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
size_t v___x_3790_; size_t v___x_3791_; 
v___x_3790_ = ((size_t)1ULL);
v___x_3791_ = lean_usize_add(v_i_3757_, v___x_3790_);
v_i_3757_ = v___x_3791_;
v_b_3758_ = v___x_3789_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3754_ = stack[0].m_obj;
lean_object* v_as_3755_ = stack[1].m_obj;
size_t v_sz_3756_ = stack[2].m_num;
size_t v_i_3757_ = stack[3].m_num;
lean_object* v_b_3758_ = stack[4].m_obj;
lean_object* v_res_3797_;
v_res_3797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_init_3754_, v_as_3755_, v_sz_3756_, v_i_3757_, v_b_3758_);
stack->m_obj
 = v_res_3797_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3798_, lean_object* v_as_3799_, lean_object* v_sz_3800_, lean_object* v_i_3801_, lean_object* v_b_3802_){
_start:
{
size_t v_sz_boxed_3803_; size_t v_i_boxed_3804_; lean_object* v_res_3805_; 
v_sz_boxed_3803_ = lean_unbox_usize(v_sz_3800_);
lean_dec(v_sz_3800_);
v_i_boxed_3804_ = lean_unbox_usize(v_i_3801_);
lean_dec(v_i_3801_);
v_res_3805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_init_3798_, v_as_3799_, v_sz_boxed_3803_, v_i_boxed_3804_, v_b_3802_);
lean_dec_ref(v_as_3799_);
lean_dec_ref(v_init_3798_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0___boxed(lean_object* v_init_3806_, lean_object* v_n_3807_, lean_object* v_b_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_3806_, v_n_3807_, v_b_3808_);
lean_dec_ref(v_n_3807_);
lean_dec_ref(v_init_3806_);
return v_res_3809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(lean_object* v_t_3810_, lean_object* v_init_3811_){
_start:
{
lean_object* v_root_3812_; lean_object* v_tail_3813_; lean_object* v___x_3814_; 
v_root_3812_ = lean_ctor_get(v_t_3810_, 0);
v_tail_3813_ = lean_ctor_get(v_t_3810_, 1);
lean_inc_ref(v_init_3811_);
v___x_3814_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_3811_, v_root_3812_, v_init_3811_);
lean_dec_ref(v_init_3811_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3822_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3817_ = v___x_3814_;
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3814_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
if (v_isShared_3818_ == 0)
{
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3815_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3859_; 
v_a_3823_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3825_ = v___x_3814_;
v_isShared_3826_ = v_isSharedCheck_3859_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3814_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3859_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
if (lean_obj_tag(v_a_3823_) == 0)
{
lean_object* v_a_3827_; lean_object* v___x_3829_; 
v_a_3827_ = lean_ctor_get(v_a_3823_, 0);
lean_inc(v_a_3827_);
lean_dec_ref_known(v_a_3823_, 1);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v_a_3827_);
v___x_3829_ = v___x_3825_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3827_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; size_t v_sz_3834_; size_t v___x_3835_; lean_object* v___x_3836_; 
lean_del_object(v___x_3825_);
v_a_3831_ = lean_ctor_get(v_a_3823_, 0);
lean_inc(v_a_3831_);
lean_dec_ref_known(v_a_3823_, 1);
v___x_3832_ = lean_box(0);
v___x_3833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3832_);
lean_ctor_set(v___x_3833_, 1, v_a_3831_);
v_sz_3834_ = lean_array_size(v_tail_3813_);
v___x_3835_ = ((size_t)0ULL);
v___x_3836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_tail_3813_, v_sz_3834_, v___x_3835_, v___x_3833_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3836_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3836_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
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
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3858_; 
v_a_3845_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3847_ = v___x_3836_;
v_isShared_3848_ = v_isSharedCheck_3858_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3836_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3858_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v_fst_3849_; 
v_fst_3849_ = lean_ctor_get(v_a_3845_, 0);
if (lean_obj_tag(v_fst_3849_) == 0)
{
lean_object* v_snd_3850_; lean_object* v___x_3852_; 
v_snd_3850_ = lean_ctor_get(v_a_3845_, 1);
lean_inc(v_snd_3850_);
lean_dec(v_a_3845_);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 0, v_snd_3850_);
v___x_3852_ = v___x_3847_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_snd_3850_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
else
{
lean_object* v_val_3854_; lean_object* v___x_3856_; 
lean_inc_ref(v_fst_3849_);
lean_dec(v_a_3845_);
v_val_3854_ = lean_ctor_get(v_fst_3849_, 0);
lean_inc(v_val_3854_);
lean_dec_ref_known(v_fst_3849_, 1);
if (v_isShared_3848_ == 0)
{
lean_ctor_set(v___x_3847_, 0, v_val_3854_);
v___x_3856_ = v___x_3847_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_val_3854_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0___boxed(lean_object* v_t_3860_, lean_object* v_init_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(v_t_3860_, v_init_3861_);
lean_dec_ref(v_t_3860_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble(lean_object* v_docs_3865_){
_start:
{
lean_object* v_ctx_3866_; lean_object* v___x_3867_; 
v_ctx_3866_ = ((lean_object*)(l_Lean_VersoModuleDocs_assemble___closed__0));
v___x_3867_ = l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(v_docs_3865_, v_ctx_3866_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3867_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3867_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
else
{
lean_object* v_a_3876_; lean_object* v___x_3877_; 
v_a_3876_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3876_);
lean_dec_ref_known(v___x_3867_, 1);
v___x_3877_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(v_a_3876_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3877_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3877_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3896_; 
v_a_3886_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3888_ = v___x_3877_;
v_isShared_3889_ = v_isSharedCheck_3896_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3877_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3896_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v_content_3890_; lean_object* v_priorParts_3891_; lean_object* v___x_3892_; lean_object* v___x_3894_; 
v_content_3890_ = lean_ctor_get(v_a_3886_, 0);
lean_inc_ref(v_content_3890_);
v_priorParts_3891_ = lean_ctor_get(v_a_3886_, 1);
lean_inc_ref(v_priorParts_3891_);
lean_dec(v_a_3886_);
v___x_3892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3892_, 0, v_content_3890_);
lean_ctor_set(v___x_3892_, 1, v_priorParts_3891_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3892_);
v___x_3894_ = v___x_3888_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3892_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble___boxed(lean_object* v_docs_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Lean_VersoModuleDocs_assemble(v_docs_3897_);
lean_dec_ref(v_docs_3897_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v_es_3899_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = lean_array_mk(v_es_3899_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v_x_3903_, lean_object* v_x_3904_, lean_object* v_es_3905_){
_start:
{
lean_object* v_ents_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v_ents_3906_ = lean_array_mk(v_es_3905_);
v___x_3907_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_));
lean_inc_ref(v_ents_3906_);
v___x_3908_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
lean_ctor_set(v___x_3908_, 1, v_ents_3906_);
lean_ctor_set(v___x_3908_, 2, v_ents_3906_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v_x_3909_, lean_object* v_x_3910_, lean_object* v_es_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(v_x_3909_, v_x_3910_, v_es_3911_);
lean_dec_ref(v_x_3910_);
lean_dec_ref(v_x_3909_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v___x_3913_, lean_object* v_x_3914_){
_start:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; size_t v___x_3918_; lean_object* v___x_3919_; 
v___x_3915_ = lean_unsigned_to_nat(32u);
v___x_3916_ = lean_mk_empty_array_with_capacity(v___x_3915_);
v___x_3917_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_3918_ = ((size_t)5ULL);
lean_inc(v___x_3913_);
v___x_3919_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3919_, 0, v___x_3917_);
lean_ctor_set(v___x_3919_, 1, v___x_3916_);
lean_ctor_set(v___x_3919_, 2, v___x_3913_);
lean_ctor_set(v___x_3919_, 3, v___x_3913_);
lean_ctor_set_usize(v___x_3919_, 4, v___x_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v___x_3920_, lean_object* v_x_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(v___x_3920_, v_x_3921_);
lean_dec_ref(v_x_3921_);
return v_res_3922_;
}
}
lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3944_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_));
v___x_3945_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_3944_);
return v___x_3945_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3946_;
v_res_3946_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3946_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v_a_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_();
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainVersoModuleDocs(lean_object* v_env_3949_){
_start:
{
lean_object* v___x_3950_; lean_object* v_toEnvExtension_3951_; lean_object* v_asyncMode_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3950_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_3951_ = lean_ctor_get(v___x_3950_, 0);
v_asyncMode_3952_ = lean_ctor_get(v_toEnvExtension_3951_, 2);
v___x_3953_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_3954_ = lean_box(0);
v___x_3955_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3953_, v___x_3950_, v_env_3949_, v_asyncMode_3952_, v___x_3954_);
return v___x_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDocs(lean_object* v_env_3956_){
_start:
{
lean_object* v___x_3957_; 
v___x_3957_ = l_Lean_getMainVersoModuleDocs(v_env_3956_);
return v___x_3957_;
}
}
static lean_object* _init_l_Lean_getVersoModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3958_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_3959_ = lean_box(0);
v___x_3960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3959_);
lean_ctor_set(v___x_3960_, 1, v___x_3958_);
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f(lean_object* v_env_3961_, lean_object* v_moduleName_3962_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = l_Lean_Environment_getModuleIdx_x3f(v_env_3961_, v_moduleName_3962_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v___x_3964_; 
v___x_3964_ = lean_box(0);
return v___x_3964_;
}
else
{
lean_object* v_val_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3976_; 
v_val_3965_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3967_ = v___x_3963_;
v_isShared_3968_ = v_isSharedCheck_3976_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_val_3965_);
lean_dec(v___x_3963_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3976_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; uint8_t v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3974_; 
v___x_3969_ = lean_obj_once(&l_Lean_getVersoModuleDoc_x3f___closed__0, &l_Lean_getVersoModuleDoc_x3f___closed__0_once, _init_l_Lean_getVersoModuleDoc_x3f___closed__0);
v___x_3970_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v___x_3971_ = 1;
v___x_3972_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3969_, v___x_3970_, v_env_3961_, v_val_3965_, v___x_3971_);
lean_dec(v_val_3965_);
if (v_isShared_3968_ == 0)
{
lean_ctor_set(v___x_3967_, 0, v___x_3972_);
v___x_3974_ = v___x_3967_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3972_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f___boxed(lean_object* v_env_3977_, lean_object* v_moduleName_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l_Lean_getVersoModuleDoc_x3f(v_env_3977_, v_moduleName_3978_);
lean_dec(v_moduleName_3978_);
lean_dec_ref(v_env_3977_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet___lam__0(lean_object* v___x_3980_, lean_object* v_snippet_3981_, lean_object* v_s_3982_){
_start:
{
lean_object* v_addEntryFn_3983_; lean_object* v_importedEntries_3984_; lean_object* v_state_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3993_; 
v_addEntryFn_3983_ = lean_ctor_get(v___x_3980_, 3);
lean_inc(v_addEntryFn_3983_);
lean_dec_ref(v___x_3980_);
v_importedEntries_3984_ = lean_ctor_get(v_s_3982_, 0);
v_state_3985_ = lean_ctor_get(v_s_3982_, 1);
v_isSharedCheck_3993_ = !lean_is_exclusive(v_s_3982_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3987_ = v_s_3982_;
v_isShared_3988_ = v_isSharedCheck_3993_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_state_3985_);
lean_inc(v_importedEntries_3984_);
lean_dec(v_s_3982_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3993_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v_state_3989_; lean_object* v___x_3991_; 
v_state_3989_ = lean_apply_2(v_addEntryFn_3983_, v_state_3985_, v_snippet_3981_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 1, v_state_3989_);
v___x_3991_ = v___x_3987_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_importedEntries_3984_);
lean_ctor_set(v_reuseFailAlloc_3992_, 1, v_state_3989_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet(lean_object* v_env_3996_, lean_object* v_snippet_3997_){
_start:
{
lean_object* v_docs_3998_; uint8_t v___x_3999_; 
lean_inc_ref(v_env_3996_);
v_docs_3998_ = l_Lean_getMainVersoModuleDocs(v_env_3996_);
v___x_3999_ = l_Lean_VersoModuleDocs_canAdd(v_docs_3998_, v_snippet_3997_);
if (v___x_3999_ == 0)
{
lean_object* v___x_4000_; lean_object* v___y_4002_; lean_object* v___x_4007_; 
lean_dec_ref(v_snippet_3997_);
lean_dec_ref(v_env_3996_);
v___x_4000_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__0));
v___x_4007_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_3998_);
lean_dec_ref(v_docs_3998_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v___x_4008_; 
v___x_4008_ = ((lean_object*)(l_Lean_throwIfHasDocString___redArg___closed__0));
v___y_4002_ = v___x_4008_;
goto v___jp_4001_;
}
else
{
lean_object* v_val_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v_val_4009_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_val_4009_);
lean_dec_ref_known(v___x_4007_, 1);
v___x_4010_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__1));
v___x_4011_ = l_Nat_reprFast(v_val_4009_);
v___x_4012_ = lean_string_append(v___x_4010_, v___x_4011_);
lean_dec_ref(v___x_4011_);
v___x_4013_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1));
v___x_4014_ = lean_string_append(v___x_4012_, v___x_4013_);
v___y_4002_ = v___x_4014_;
goto v___jp_4001_;
}
v___jp_4001_:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4003_ = lean_string_append(v___x_4000_, v___y_4002_);
lean_dec_ref(v___y_4002_);
v___x_4004_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1));
v___x_4005_ = lean_string_append(v___x_4003_, v___x_4004_);
v___x_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
return v___x_4006_;
}
}
else
{
lean_object* v___x_4015_; lean_object* v_toEnvExtension_4016_; lean_object* v_asyncMode_4017_; uint8_t v_logWrites_4018_; lean_object* v___f_4019_; lean_object* v___x_4020_; 
lean_dec_ref(v_docs_3998_);
v___x_4015_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_4016_ = lean_ctor_get(v___x_4015_, 0);
v_asyncMode_4017_ = lean_ctor_get(v_toEnvExtension_4016_, 2);
v_logWrites_4018_ = lean_ctor_get_uint8(v_toEnvExtension_4016_, sizeof(void*)*6);
v___f_4019_ = lean_alloc_closure((void*)(l_Lean_addVersoModuleDocSnippet___lam__0), 3, 2);
lean_closure_set(v___f_4019_, 0, v___x_4015_);
lean_closure_set(v___f_4019_, 1, v_snippet_3997_);
v___x_4020_ = lean_box(0);
if (v_logWrites_4018_ == 0)
{
lean_object* v___x_4021_; lean_object* v___x_4022_; 
lean_inc_ref(v_toEnvExtension_4016_);
v___x_4021_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4016_, v_env_3996_, v___f_4019_, v_asyncMode_4017_, v___x_4020_, v___x_3999_);
v___x_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4021_);
return v___x_4022_;
}
else
{
lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
lean_inc_ref_n(v_toEnvExtension_4016_, 2);
v___x_4023_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4016_, v_env_3996_);
lean_dec_ref(v_env_3996_);
v___x_4024_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4016_, v___x_4023_, v___f_4019_, v_asyncMode_4017_, v___x_4020_, v___x_3999_);
v___x_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
return v___x_4025_;
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
