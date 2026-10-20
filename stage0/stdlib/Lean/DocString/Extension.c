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
LEAN_EXPORT lean_object* l_Lean_throwIfHasDocString___redArg___lam__0(lean_object* v_declName_1168_, lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v___x_1171_, lean_object* v___x_1172_, lean_object* v_toPure_1173_, lean_object* v_env_1174_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1183_ = l_Lean_docStringExt;
v___x_1184_ = lean_box(1);
lean_inc(v_declName_1168_);
lean_inc_ref(v_env_1174_);
v___x_1185_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_1171_, v___x_1183_, v_env_1174_, v_declName_1168_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_1168_);
v___x_1187_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_1172_, v___x_1186_, v_env_1174_, v_declName_1168_, v___x_1184_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec_ref(v_inst_1170_);
lean_dec_ref(v_inst_1169_);
lean_dec(v_declName_1168_);
v___x_1188_ = lean_box(0);
v___x_1189_ = lean_apply_2(v_toPure_1173_, lean_box(0), v___x_1188_);
return v___x_1189_;
}
else
{
lean_dec(v_toPure_1173_);
goto v___jp_1175_;
}
}
else
{
lean_dec_ref(v_env_1174_);
lean_dec(v_toPure_1173_);
lean_dec_ref(v___x_1172_);
goto v___jp_1175_;
}
v___jp_1175_:
{
lean_object* v___x_1176_; uint8_t v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1176_ = lean_obj_once(&l_Lean_throwIfHasDocString___redArg___lam__0___closed__1, &l_Lean_throwIfHasDocString___redArg___lam__0___closed__1_once, _init_l_Lean_throwIfHasDocString___redArg___lam__0___closed__1);
v___x_1177_ = 0;
v___x_1178_ = l_Lean_MessageData_ofConstName(v_declName_1168_, v___x_1177_);
v___x_1179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1176_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = lean_obj_once(&l_Lean_throwIfHasDocString___redArg___lam__0___closed__3, &l_Lean_throwIfHasDocString___redArg___lam__0___closed__3_once, _init_l_Lean_throwIfHasDocString___redArg___lam__0___closed__3);
v___x_1181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = l_Lean_throwError___redArg(v_inst_1169_, v_inst_1170_, v___x_1181_);
return v___x_1182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwIfHasDocString___redArg(lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_declName_1194_){
_start:
{
lean_object* v_toApplicative_1195_; lean_object* v_toBind_1196_; lean_object* v_getEnv_1197_; lean_object* v_toPure_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___f_1201_; lean_object* v___x_1202_; 
v_toApplicative_1195_ = lean_ctor_get(v_inst_1191_, 0);
v_toBind_1196_ = lean_ctor_get(v_inst_1191_, 1);
lean_inc(v_toBind_1196_);
v_getEnv_1197_ = lean_ctor_get(v_inst_1193_, 0);
lean_inc(v_getEnv_1197_);
lean_dec_ref(v_inst_1193_);
v_toPure_1198_ = lean_ctor_get(v_toApplicative_1195_, 1);
lean_inc(v_toPure_1198_);
v___x_1199_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default));
v___x_1200_ = ((lean_object*)(l_Lean_throwIfHasDocString___redArg___closed__0));
v___f_1201_ = lean_alloc_closure((void*)(l_Lean_throwIfHasDocString___redArg___lam__0), 7, 6);
lean_closure_set(v___f_1201_, 0, v_declName_1194_);
lean_closure_set(v___f_1201_, 1, v_inst_1191_);
lean_closure_set(v___f_1201_, 2, v_inst_1192_);
lean_closure_set(v___f_1201_, 3, v___x_1200_);
lean_closure_set(v___f_1201_, 4, v___x_1199_);
lean_closure_set(v___f_1201_, 5, v_toPure_1198_);
v___x_1202_ = lean_apply_4(v_toBind_1196_, lean_box(0), lean_box(0), v_getEnv_1197_, v___f_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwIfHasDocString(lean_object* v_m_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_declName_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_throwIfHasDocString___redArg(v_inst_1204_, v_inst_1205_, v_inst_1206_, v_declName_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__0(lean_object* v_docString_1209_, lean_object* v_declName_1210_, lean_object* v_env_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; 
v___x_1212_ = l_Lean_docStringExt;
v___x_1213_ = l_String_removeLeadingSpaces(v_docString_1209_);
v___x_1214_ = 1;
v___x_1215_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1212_, v_env_1211_, v_declName_1210_, v___x_1213_, v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__1(lean_object* v_modifyEnv_1216_, lean_object* v___f_1217_, lean_object* v_____r_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_apply_1(v_modifyEnv_1216_, v___f_1217_);
return v___x_1219_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l_Lean_addDocStringCore___redArg___lam__2___closed__0));
v___x_1222_ = l_Lean_stringToMessageData(v___x_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2(lean_object* v_declName_1223_, lean_object* v_modifyEnv_1224_, lean_object* v___f_1225_, lean_object* v_inst_1226_, lean_object* v_inst_1227_, lean_object* v_toBind_1228_, lean_object* v___f_1229_, lean_object* v_____do__lift_1230_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1230_, v_declName_1223_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v___x_1232_; 
lean_dec(v___f_1229_);
lean_dec(v_toBind_1228_);
lean_dec_ref(v_inst_1227_);
lean_dec_ref(v_inst_1226_);
lean_dec(v_declName_1223_);
v___x_1232_ = lean_apply_1(v_modifyEnv_1224_, v___f_1225_);
return v___x_1232_;
}
else
{
uint8_t v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_dec_ref_known(v___x_1231_, 1);
lean_dec_ref(v___f_1225_);
lean_dec(v_modifyEnv_1224_);
v___x_1233_ = 0;
v___x_1234_ = lean_obj_once(&l_Lean_throwIfHasDocString___redArg___lam__0___closed__1, &l_Lean_throwIfHasDocString___redArg___lam__0___closed__1_once, _init_l_Lean_throwIfHasDocString___redArg___lam__0___closed__1);
v___x_1235_ = l_Lean_MessageData_ofConstName(v_declName_1223_, v___x_1233_);
v___x_1236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
v___x_1237_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__1, &l_Lean_addDocStringCore___redArg___lam__2___closed__1_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1);
v___x_1238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1236_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
v___x_1239_ = l_Lean_throwError___redArg(v_inst_1226_, v_inst_1227_, v___x_1238_);
v___x_1240_ = lean_apply_4(v_toBind_1228_, lean_box(0), lean_box(0), v___x_1239_, v___f_1229_);
return v___x_1240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_1241_, lean_object* v_modifyEnv_1242_, lean_object* v___f_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_, lean_object* v_toBind_1246_, lean_object* v___f_1247_, lean_object* v_____do__lift_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_addDocStringCore___redArg___lam__2(v_declName_1241_, v_modifyEnv_1242_, v___f_1243_, v_inst_1244_, v_inst_1245_, v_toBind_1246_, v___f_1247_, v_____do__lift_1248_);
lean_dec_ref(v_____do__lift_1248_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___redArg(lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_declName_1253_, lean_object* v_docString_1254_){
_start:
{
lean_object* v_toBind_1255_; lean_object* v_getEnv_1256_; lean_object* v_modifyEnv_1257_; lean_object* v___f_1258_; lean_object* v___f_1259_; lean_object* v___f_1260_; lean_object* v___x_1261_; 
v_toBind_1255_ = lean_ctor_get(v_inst_1250_, 1);
lean_inc_n(v_toBind_1255_, 2);
v_getEnv_1256_ = lean_ctor_get(v_inst_1252_, 0);
lean_inc(v_getEnv_1256_);
v_modifyEnv_1257_ = lean_ctor_get(v_inst_1252_, 1);
lean_inc_n(v_modifyEnv_1257_, 2);
lean_dec_ref(v_inst_1252_);
lean_inc(v_declName_1253_);
v___f_1258_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1258_, 0, v_docString_1254_);
lean_closure_set(v___f_1258_, 1, v_declName_1253_);
lean_inc_ref(v___f_1258_);
v___f_1259_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1259_, 0, v_modifyEnv_1257_);
lean_closure_set(v___f_1259_, 1, v___f_1258_);
v___f_1260_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1260_, 0, v_declName_1253_);
lean_closure_set(v___f_1260_, 1, v_modifyEnv_1257_);
lean_closure_set(v___f_1260_, 2, v___f_1258_);
lean_closure_set(v___f_1260_, 3, v_inst_1250_);
lean_closure_set(v___f_1260_, 4, v_inst_1251_);
lean_closure_set(v___f_1260_, 5, v_toBind_1255_);
lean_closure_set(v___f_1260_, 6, v___f_1259_);
v___x_1261_ = lean_apply_4(v_toBind_1255_, lean_box(0), lean_box(0), v_getEnv_1256_, v___f_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore(lean_object* v_m_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_declName_1267_, lean_object* v_docString_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_addDocStringCore___redArg(v_inst_1263_, v_inst_1264_, v_inst_1265_, v_declName_1267_, v_docString_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___boxed(lean_object* v_m_1270_, lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_declName_1275_, lean_object* v_docString_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_addDocStringCore(v_m_1270_, v_inst_1271_, v_inst_1272_, v_inst_1273_, v_inst_1274_, v_declName_1275_, v_docString_1276_);
lean_dec(v_inst_1274_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__0(lean_object* v_declName_1279_, lean_object* v_ps_1280_){
_start:
{
lean_object* v_importedEntries_1281_; lean_object* v_state_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1291_; 
v_importedEntries_1281_ = lean_ctor_get(v_ps_1280_, 0);
v_state_1282_ = lean_ctor_get(v_ps_1280_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_ps_1280_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1284_ = v_ps_1280_;
v_isShared_1285_ = v_isSharedCheck_1291_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_state_1282_);
lean_inc(v_importedEntries_1281_);
lean_dec(v_ps_1280_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1291_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1286_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__0___closed__0));
v___x_1287_ = l_Std_DTreeMap_Internal_Impl_erase___redArg(v___x_1286_, v_declName_1279_, v_state_1282_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 1, v___x_1287_);
v___x_1289_ = v___x_1284_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_importedEntries_1281_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__1(lean_object* v___f_1292_, lean_object* v_env_1293_){
_start:
{
lean_object* v___x_1294_; lean_object* v_toEnvExtension_1295_; uint8_t v_logWrites_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1294_ = l_Lean_docStringExt;
v_toEnvExtension_1295_ = lean_ctor_get(v___x_1294_, 0);
v_logWrites_1296_ = lean_ctor_get_uint8(v_toEnvExtension_1295_, sizeof(void*)*6);
v___x_1297_ = lean_box(2);
v___x_1298_ = lean_box(0);
v___x_1299_ = 1;
if (v_logWrites_1296_ == 0)
{
lean_object* v___x_1300_; 
lean_inc_ref(v_toEnvExtension_1295_);
v___x_1300_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1295_, v_env_1293_, v___f_1292_, v___x_1297_, v___x_1298_, v___x_1299_);
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_inc_ref_n(v_toEnvExtension_1295_, 2);
v___x_1301_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1295_, v_env_1293_);
lean_dec_ref(v_env_1293_);
v___x_1302_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1295_, v___x_1301_, v___f_1292_, v___x_1297_, v___x_1298_, v___x_1299_);
return v___x_1302_;
}
}
}
static lean_object* _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l_Lean_removeDocStringCore___redArg___lam__3___closed__0));
v___x_1305_ = l_Lean_stringToMessageData(v___x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3(lean_object* v_declName_1306_, lean_object* v_modifyEnv_1307_, lean_object* v___f_1308_, lean_object* v_inst_1309_, lean_object* v_inst_1310_, lean_object* v_toBind_1311_, lean_object* v___f_1312_, lean_object* v_____do__lift_1313_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1313_, v_declName_1306_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v___x_1315_; 
lean_dec(v___f_1312_);
lean_dec(v_toBind_1311_);
lean_dec_ref(v_inst_1310_);
lean_dec_ref(v_inst_1309_);
lean_dec(v_declName_1306_);
v___x_1315_ = lean_apply_1(v_modifyEnv_1307_, v___f_1308_);
return v___x_1315_;
}
else
{
uint8_t v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_dec_ref_known(v___x_1314_, 1);
lean_dec_ref(v___f_1308_);
lean_dec(v_modifyEnv_1307_);
v___x_1316_ = 0;
v___x_1317_ = lean_obj_once(&l_Lean_removeDocStringCore___redArg___lam__3___closed__1, &l_Lean_removeDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_removeDocStringCore___redArg___lam__3___closed__1);
v___x_1318_ = l_Lean_MessageData_ofConstName(v_declName_1306_, v___x_1316_);
v___x_1319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1317_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__1, &l_Lean_addDocStringCore___redArg___lam__2___closed__1_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1);
v___x_1321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1319_);
lean_ctor_set(v___x_1321_, 1, v___x_1320_);
v___x_1322_ = l_Lean_throwError___redArg(v_inst_1309_, v_inst_1310_, v___x_1321_);
v___x_1323_ = lean_apply_4(v_toBind_1311_, lean_box(0), lean_box(0), v___x_1322_, v___f_1312_);
return v___x_1323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_1324_, lean_object* v_modifyEnv_1325_, lean_object* v___f_1326_, lean_object* v_inst_1327_, lean_object* v_inst_1328_, lean_object* v_toBind_1329_, lean_object* v___f_1330_, lean_object* v_____do__lift_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_removeDocStringCore___redArg___lam__3(v_declName_1324_, v_modifyEnv_1325_, v___f_1326_, v_inst_1327_, v_inst_1328_, v_toBind_1329_, v___f_1330_, v_____do__lift_1331_);
lean_dec_ref(v_____do__lift_1331_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___redArg(lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_declName_1336_){
_start:
{
lean_object* v_toBind_1337_; lean_object* v_getEnv_1338_; lean_object* v_modifyEnv_1339_; lean_object* v___f_1340_; lean_object* v___f_1341_; lean_object* v___f_1342_; lean_object* v___f_1343_; lean_object* v___x_1344_; 
v_toBind_1337_ = lean_ctor_get(v_inst_1333_, 1);
lean_inc_n(v_toBind_1337_, 2);
v_getEnv_1338_ = lean_ctor_get(v_inst_1335_, 0);
lean_inc(v_getEnv_1338_);
v_modifyEnv_1339_ = lean_ctor_get(v_inst_1335_, 1);
lean_inc_n(v_modifyEnv_1339_, 2);
lean_dec_ref(v_inst_1335_);
lean_inc(v_declName_1336_);
v___f_1340_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1340_, 0, v_declName_1336_);
v___f_1341_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1341_, 0, v___f_1340_);
lean_inc_ref(v___f_1341_);
v___f_1342_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1342_, 0, v_modifyEnv_1339_);
lean_closure_set(v___f_1342_, 1, v___f_1341_);
v___f_1343_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1343_, 0, v_declName_1336_);
lean_closure_set(v___f_1343_, 1, v_modifyEnv_1339_);
lean_closure_set(v___f_1343_, 2, v___f_1341_);
lean_closure_set(v___f_1343_, 3, v_inst_1333_);
lean_closure_set(v___f_1343_, 4, v_inst_1334_);
lean_closure_set(v___f_1343_, 5, v_toBind_1337_);
lean_closure_set(v___f_1343_, 6, v___f_1342_);
v___x_1344_ = lean_apply_4(v_toBind_1337_, lean_box(0), lean_box(0), v_getEnv_1338_, v___f_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore(lean_object* v_m_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_declName_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_removeDocStringCore___redArg(v_inst_1346_, v_inst_1347_, v_inst_1348_, v_declName_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___boxed(lean_object* v_m_1352_, lean_object* v_inst_1353_, lean_object* v_inst_1354_, lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_declName_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_removeDocStringCore(v_m_1352_, v_inst_1353_, v_inst_1354_, v_inst_1355_, v_inst_1356_, v_declName_1357_);
lean_dec(v_inst_1356_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___redArg(lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_inst_1361_, lean_object* v_declName_1362_, lean_object* v_docString_x3f_1363_){
_start:
{
if (lean_obj_tag(v_docString_x3f_1363_) == 0)
{
lean_object* v_toApplicative_1364_; lean_object* v_toPure_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v_toApplicative_1364_ = lean_ctor_get(v_inst_1359_, 0);
lean_inc_ref(v_toApplicative_1364_);
lean_dec(v_declName_1362_);
lean_dec_ref(v_inst_1361_);
lean_dec_ref(v_inst_1360_);
lean_dec_ref(v_inst_1359_);
v_toPure_1365_ = lean_ctor_get(v_toApplicative_1364_, 1);
lean_inc(v_toPure_1365_);
lean_dec_ref(v_toApplicative_1364_);
v___x_1366_ = lean_box(0);
v___x_1367_ = lean_apply_2(v_toPure_1365_, lean_box(0), v___x_1366_);
return v___x_1367_;
}
else
{
lean_object* v_val_1368_; lean_object* v___x_1369_; 
v_val_1368_ = lean_ctor_get(v_docString_x3f_1363_, 0);
lean_inc(v_val_1368_);
lean_dec_ref_known(v_docString_x3f_1363_, 1);
v___x_1369_ = l_Lean_addDocStringCore___redArg(v_inst_1359_, v_inst_1360_, v_inst_1361_, v_declName_1362_, v_val_1368_);
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27(lean_object* v_m_1370_, lean_object* v_inst_1371_, lean_object* v_inst_1372_, lean_object* v_inst_1373_, lean_object* v_inst_1374_, lean_object* v_declName_1375_, lean_object* v_docString_x3f_1376_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_addDocStringCore_x27___redArg(v_inst_1371_, v_inst_1372_, v_inst_1373_, v_declName_1375_, v_docString_x3f_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore_x27___boxed(lean_object* v_m_1378_, lean_object* v_inst_1379_, lean_object* v_inst_1380_, lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v_declName_1383_, lean_object* v_docString_x3f_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_addDocStringCore_x27(v_m_1378_, v_inst_1379_, v_inst_1380_, v_inst_1381_, v_inst_1382_, v_declName_1383_, v_docString_x3f_1384_);
lean_dec(v_inst_1382_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f(lean_object* v_env_1386_, lean_object* v_declName_1387_, uint8_t v_includeBuiltin_1388_){
_start:
{
lean_object* v_md_1391_; lean_object* v_v_1396_; lean_object* v___x_1403_; lean_object* v_toEnvExtension_1404_; lean_object* v_asyncMode_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; lean_object* v___x_1408_; 
v___x_1403_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1404_ = lean_ctor_get(v___x_1403_, 0);
v_asyncMode_1405_ = lean_ctor_get(v_toEnvExtension_1404_, 2);
v___x_1406_ = lean_box(0);
v___x_1407_ = 1;
lean_inc(v_declName_1387_);
lean_inc_ref(v_env_1386_);
v___x_1408_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1406_, v___x_1403_, v_env_1386_, v_declName_1387_, v_asyncMode_1405_, v___x_1407_);
if (lean_obj_tag(v___x_1408_) == 1)
{
lean_object* v_val_1409_; 
lean_dec(v_declName_1387_);
v_val_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_val_1409_);
lean_dec_ref_known(v___x_1408_, 1);
v_declName_1387_ = v_val_1409_;
goto _start;
}
else
{
lean_object* v___x_1411_; lean_object* v_toEnvExtension_1412_; lean_object* v_asyncMode_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
lean_dec(v___x_1408_);
v___x_1411_ = l_Lean_docStringExt;
v_toEnvExtension_1412_ = lean_ctor_get(v___x_1411_, 0);
v_asyncMode_1413_ = lean_ctor_get(v_toEnvExtension_1412_, 2);
v___x_1414_ = ((lean_object*)(l_Lean_throwIfHasDocString___redArg___closed__0));
lean_inc(v_declName_1387_);
lean_inc_ref(v_env_1386_);
v___x_1415_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1414_, v___x_1411_, v_env_1386_, v_declName_1387_, v_asyncMode_1413_, v___x_1407_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v___x_1416_; lean_object* v_toEnvExtension_1417_; lean_object* v_asyncMode_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1416_ = l_Lean_versoDocStringExt;
v_toEnvExtension_1417_ = lean_ctor_get(v___x_1416_, 0);
v_asyncMode_1418_ = lean_ctor_get(v_toEnvExtension_1417_, 2);
v___x_1419_ = ((lean_object*)(l_Lean_instInhabitedVersoDocString_default));
lean_inc(v_declName_1387_);
v___x_1420_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1419_, v___x_1416_, v_env_1386_, v_declName_1387_, v_asyncMode_1418_, v___x_1407_);
if (lean_obj_tag(v___x_1420_) == 0)
{
if (v_includeBuiltin_1388_ == 0)
{
lean_dec(v_declName_1387_);
goto v___jp_1400_;
}
else
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = l___private_Lean_DocString_Extension_0__Lean_builtinDocStrings;
v___x_1422_ = lean_st_ref_get(v___x_1421_);
v___x_1423_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1422_, v_declName_1387_);
lean_dec(v___x_1422_);
if (lean_obj_tag(v___x_1423_) == 1)
{
lean_object* v_val_1424_; 
lean_dec(v_declName_1387_);
v_val_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_val_1424_);
lean_dec_ref_known(v___x_1423_, 1);
v_md_1391_ = v_val_1424_;
goto v___jp_1390_;
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec(v___x_1423_);
v___x_1425_ = l___private_Lean_DocString_Extension_0__Lean_builtinVersoDocStrings;
v___x_1426_ = lean_st_ref_get(v___x_1425_);
v___x_1427_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1426_, v_declName_1387_);
lean_dec(v_declName_1387_);
lean_dec(v___x_1426_);
if (lean_obj_tag(v___x_1427_) == 1)
{
lean_object* v_val_1428_; 
v_val_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_val_1428_);
lean_dec_ref_known(v___x_1427_, 1);
v_v_1396_ = v_val_1428_;
goto v___jp_1395_;
}
else
{
lean_dec(v___x_1427_);
goto v___jp_1400_;
}
}
}
}
else
{
lean_object* v_val_1429_; 
lean_dec(v_declName_1387_);
v_val_1429_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_val_1429_);
lean_dec_ref_known(v___x_1420_, 1);
v_v_1396_ = v_val_1429_;
goto v___jp_1395_;
}
}
else
{
lean_object* v_val_1430_; 
lean_dec(v_declName_1387_);
lean_dec_ref(v_env_1386_);
v_val_1430_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_val_1430_);
lean_dec_ref_known(v___x_1415_, 1);
v_md_1391_ = v_val_1430_;
goto v___jp_1390_;
}
}
v___jp_1390_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v_md_1391_);
v___x_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
v___x_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
return v___x_1394_;
}
v___jp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_v_1396_);
v___x_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
v___x_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
return v___x_1399_;
}
v___jp_1400_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_box(0);
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
return v___x_1402_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findInternalDocString_x3f___boxed(lean_object* v_env_1431_, lean_object* v_declName_1432_, lean_object* v_includeBuiltin_1433_, lean_object* v_a_1434_){
_start:
{
uint8_t v_includeBuiltin_boxed_1435_; lean_object* v_res_1436_; 
v_includeBuiltin_boxed_1435_ = lean_unbox(v_includeBuiltin_1433_);
v_res_1436_ = l_Lean_findInternalDocString_x3f(v_env_1431_, v_declName_1432_, v_includeBuiltin_boxed_1435_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__0(lean_object* v_declName_1437_, lean_object* v_target_1438_, lean_object* v_x_1439_){
_start:
{
lean_object* v___x_1440_; uint8_t v___x_1441_; lean_object* v___x_1442_; 
v___x_1440_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v___x_1441_ = 0;
v___x_1442_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1440_, v_x_1439_, v_declName_1437_, v_target_1438_, v___x_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__1(lean_object* v_declName_1443_, lean_object* v_val_1444_, lean_object* v_x_1445_){
_start:
{
lean_object* v___x_1446_; uint8_t v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = l_Lean_docStringExt;
v___x_1447_ = 0;
v___x_1448_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1446_, v_x_1445_, v_declName_1443_, v_val_1444_, v___x_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__2(lean_object* v_declName_1449_, lean_object* v_val_1450_, lean_object* v_x_1451_){
_start:
{
lean_object* v___x_1452_; uint8_t v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = l_Lean_versoDocStringExt;
v___x_1453_ = 0;
v___x_1454_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1452_, v_x_1451_, v_declName_1449_, v_val_1450_, v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__3(lean_object* v_modifyEnv_1455_, lean_object* v___f_1456_, lean_object* v_declName_1457_, lean_object* v_____do__lift_1458_){
_start:
{
if (lean_obj_tag(v_____do__lift_1458_) == 0)
{
lean_object* v___x_1459_; 
lean_dec(v_declName_1457_);
v___x_1459_ = lean_apply_1(v_modifyEnv_1455_, v___f_1456_);
return v___x_1459_;
}
else
{
lean_object* v_val_1460_; 
lean_dec_ref(v___f_1456_);
v_val_1460_ = lean_ctor_get(v_____do__lift_1458_, 0);
lean_inc(v_val_1460_);
lean_dec_ref_known(v_____do__lift_1458_, 1);
if (lean_obj_tag(v_val_1460_) == 0)
{
lean_object* v_val_1461_; lean_object* v___f_1462_; lean_object* v___x_1463_; 
v_val_1461_ = lean_ctor_get(v_val_1460_, 0);
lean_inc(v_val_1461_);
lean_dec_ref_known(v_val_1460_, 1);
v___f_1462_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1462_, 0, v_declName_1457_);
lean_closure_set(v___f_1462_, 1, v_val_1461_);
v___x_1463_ = lean_apply_1(v_modifyEnv_1455_, v___f_1462_);
return v___x_1463_;
}
else
{
lean_object* v_val_1464_; lean_object* v___f_1465_; lean_object* v___x_1466_; 
v_val_1464_ = lean_ctor_get(v_val_1460_, 0);
lean_inc(v_val_1464_);
lean_dec_ref_known(v_val_1460_, 1);
v___f_1465_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1465_, 0, v_declName_1457_);
lean_closure_set(v___f_1465_, 1, v_val_1464_);
v___x_1466_ = lean_apply_1(v_modifyEnv_1455_, v___f_1465_);
return v___x_1466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__4(lean_object* v_declName_1467_, lean_object* v_target_1468_, uint8_t v___y_1469_, lean_object* v_x_1470_){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v___x_1472_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1471_, v_x_1470_, v_declName_1467_, v_target_1468_, v___y_1469_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__4___boxed(lean_object* v_declName_1473_, lean_object* v_target_1474_, lean_object* v___y_1475_, lean_object* v_x_1476_){
_start:
{
uint8_t v___y_622__boxed_1477_; lean_object* v_res_1478_; 
v___y_622__boxed_1477_ = lean_unbox(v___y_1475_);
v_res_1478_ = l_Lean_addInheritedDocString___redArg___lam__4(v_declName_1473_, v_target_1474_, v___y_622__boxed_1477_, v_x_1476_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5(lean_object* v_target_1479_, uint8_t v___x_1480_, lean_object* v_inst_1481_, lean_object* v_toBind_1482_, lean_object* v___f_1483_, lean_object* v_____do__lift_1484_){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1485_ = lean_box(v___x_1480_);
v___x_1486_ = lean_alloc_closure((void*)(l_Lean_findInternalDocString_x3f___boxed), 4, 3);
lean_closure_set(v___x_1486_, 0, v_____do__lift_1484_);
lean_closure_set(v___x_1486_, 1, v_target_1479_);
lean_closure_set(v___x_1486_, 2, v___x_1485_);
v___x_1487_ = lean_apply_2(v_inst_1481_, lean_box(0), v___x_1486_);
v___x_1488_ = lean_apply_4(v_toBind_1482_, lean_box(0), lean_box(0), v___x_1487_, v___f_1483_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__5___boxed(lean_object* v_target_1489_, lean_object* v___x_1490_, lean_object* v_inst_1491_, lean_object* v_toBind_1492_, lean_object* v___f_1493_, lean_object* v_____do__lift_1494_){
_start:
{
uint8_t v___x_632__boxed_1495_; lean_object* v_res_1496_; 
v___x_632__boxed_1495_ = lean_unbox(v___x_1490_);
v_res_1496_ = l_Lean_addInheritedDocString___redArg___lam__5(v_target_1489_, v___x_632__boxed_1495_, v_inst_1491_, v_toBind_1492_, v___f_1493_, v_____do__lift_1494_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__6(lean_object* v_declName_1497_, lean_object* v_target_1498_, lean_object* v_modifyEnv_1499_, lean_object* v_inst_1500_, lean_object* v_toBind_1501_, lean_object* v___f_1502_, lean_object* v_getEnv_1503_, lean_object* v_____r_1504_){
_start:
{
uint8_t v___y_1506_; uint8_t v___x_1510_; 
v___x_1510_ = l_Lean_isPrivateName(v_declName_1497_);
if (v___x_1510_ == 0)
{
uint8_t v___x_1511_; 
v___x_1511_ = l_Lean_isPrivateName(v_target_1498_);
if (v___x_1511_ == 0)
{
lean_dec(v_getEnv_1503_);
lean_dec(v___f_1502_);
lean_dec(v_toBind_1501_);
lean_dec(v_inst_1500_);
v___y_1506_ = v___x_1511_;
goto v___jp_1505_;
}
else
{
lean_object* v___x_1512_; lean_object* v___f_1513_; lean_object* v___x_1514_; 
lean_dec(v_modifyEnv_1499_);
lean_dec(v_declName_1497_);
v___x_1512_ = lean_box(v___x_1511_);
lean_inc(v_toBind_1501_);
v___f_1513_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_1513_, 0, v_target_1498_);
lean_closure_set(v___f_1513_, 1, v___x_1512_);
lean_closure_set(v___f_1513_, 2, v_inst_1500_);
lean_closure_set(v___f_1513_, 3, v_toBind_1501_);
lean_closure_set(v___f_1513_, 4, v___f_1502_);
v___x_1514_ = lean_apply_4(v_toBind_1501_, lean_box(0), lean_box(0), v_getEnv_1503_, v___f_1513_);
return v___x_1514_;
}
}
else
{
uint8_t v___x_1515_; 
lean_dec(v_getEnv_1503_);
lean_dec(v___f_1502_);
lean_dec(v_toBind_1501_);
lean_dec(v_inst_1500_);
v___x_1515_ = 0;
v___y_1506_ = v___x_1515_;
goto v___jp_1505_;
}
v___jp_1505_:
{
lean_object* v___x_1507_; lean_object* v___f_1508_; lean_object* v___x_1509_; 
v___x_1507_ = lean_box(v___y_1506_);
v___f_1508_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__4___boxed), 4, 3);
lean_closure_set(v___f_1508_, 0, v_declName_1497_);
lean_closure_set(v___f_1508_, 1, v_target_1498_);
lean_closure_set(v___f_1508_, 2, v___x_1507_);
v___x_1509_ = lean_apply_1(v_modifyEnv_1499_, v___f_1508_);
return v___x_1509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__7(lean_object* v___f_1516_, lean_object* v_____r_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_apply_1(v___f_1516_, v_____r_1517_);
return v___x_1518_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__8___closed__1(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__8___closed__0));
v___x_1521_ = l_Lean_stringToMessageData(v___x_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__8(lean_object* v___x_1522_, lean_object* v_target_1523_, lean_object* v_declName_1524_, lean_object* v___x_1525_, lean_object* v___f_1526_, lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_toBind_1529_, lean_object* v___f_1530_, lean_object* v_____do__lift_1531_){
_start:
{
lean_object* v___x_1532_; lean_object* v_toEnvExtension_1533_; lean_object* v_asyncMode_1534_; uint8_t v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1532_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1533_ = lean_ctor_get(v___x_1532_, 0);
v_asyncMode_1534_ = lean_ctor_get(v_toEnvExtension_1533_, 2);
v___x_1535_ = 1;
v___x_1536_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1522_, v___x_1532_, v_____do__lift_1531_, v_target_1523_, v_asyncMode_1534_, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1537_, 0, v_declName_1524_);
v___x_1538_ = l_instBEqOption_beq___redArg(v___x_1525_, v___x_1536_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_dec(v___f_1530_);
lean_dec(v_toBind_1529_);
lean_dec_ref(v_inst_1528_);
lean_dec_ref(v_inst_1527_);
v___x_1539_ = lean_box(0);
v___x_1540_ = lean_apply_1(v___f_1526_, v___x_1539_);
return v___x_1540_;
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_dec(v___f_1526_);
v___x_1541_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__8___closed__1, &l_Lean_addInheritedDocString___redArg___lam__8___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__8___closed__1);
v___x_1542_ = l_Lean_throwError___redArg(v_inst_1527_, v_inst_1528_, v___x_1541_);
v___x_1543_ = lean_apply_4(v_toBind_1529_, lean_box(0), lean_box(0), v___x_1542_, v___f_1530_);
return v___x_1543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__9(lean_object* v_toBind_1544_, lean_object* v_getEnv_1545_, lean_object* v___f_1546_, lean_object* v_____r_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_apply_4(v_toBind_1544_, lean_box(0), lean_box(0), v_getEnv_1545_, v___f_1546_);
return v___x_1548_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__10___closed__1(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__10___closed__0));
v___x_1551_ = l_Lean_stringToMessageData(v___x_1550_);
return v___x_1551_;
}
}
static lean_object* _init_l_Lean_addInheritedDocString___redArg___lam__10___closed__3(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___lam__10___closed__2));
v___x_1554_ = l_Lean_stringToMessageData(v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__10(lean_object* v___x_1555_, lean_object* v_declName_1556_, lean_object* v_toBind_1557_, lean_object* v_getEnv_1558_, lean_object* v___f_1559_, lean_object* v_inst_1560_, lean_object* v_inst_1561_, lean_object* v___f_1562_, lean_object* v_____do__lift_1563_){
_start:
{
lean_object* v___x_1564_; lean_object* v_toEnvExtension_1565_; lean_object* v_asyncMode_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; 
v___x_1564_ = l___private_Lean_DocString_Extension_0__Lean_inheritDocStringExt;
v_toEnvExtension_1565_ = lean_ctor_get(v___x_1564_, 0);
v_asyncMode_1566_ = lean_ctor_get(v_toEnvExtension_1565_, 2);
v___x_1567_ = 1;
lean_inc(v_declName_1556_);
v___x_1568_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1555_, v___x_1564_, v_____do__lift_1563_, v_declName_1556_, v_asyncMode_1566_, v___x_1567_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v___x_1569_; 
lean_dec(v___f_1562_);
lean_dec_ref(v_inst_1561_);
lean_dec_ref(v_inst_1560_);
lean_dec(v_declName_1556_);
v___x_1569_ = lean_apply_4(v_toBind_1557_, lean_box(0), lean_box(0), v_getEnv_1558_, v___f_1559_);
return v___x_1569_;
}
else
{
lean_object* v___x_1570_; uint8_t v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_dec_ref_known(v___x_1568_, 1);
lean_dec(v___f_1559_);
lean_dec(v_getEnv_1558_);
v___x_1570_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__10___closed__1, &l_Lean_addInheritedDocString___redArg___lam__10___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__10___closed__1);
v___x_1571_ = 0;
v___x_1572_ = l_Lean_MessageData_ofConstName(v_declName_1556_, v___x_1571_);
v___x_1573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1570_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__10___closed__3, &l_Lean_addInheritedDocString___redArg___lam__10___closed__3_once, _init_l_Lean_addInheritedDocString___redArg___lam__10___closed__3);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = l_Lean_throwError___redArg(v_inst_1560_, v_inst_1561_, v___x_1575_);
v___x_1577_ = lean_apply_4(v_toBind_1557_, lean_box(0), lean_box(0), v___x_1576_, v___f_1562_);
return v___x_1577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__12(lean_object* v_declName_1578_, lean_object* v_toBind_1579_, lean_object* v_getEnv_1580_, lean_object* v___f_1581_, lean_object* v_inst_1582_, lean_object* v_inst_1583_, lean_object* v___f_1584_, lean_object* v_____do__lift_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1585_, v_declName_1578_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v___x_1587_; 
lean_dec(v___f_1584_);
lean_dec_ref(v_inst_1583_);
lean_dec_ref(v_inst_1582_);
lean_dec(v_declName_1578_);
v___x_1587_ = lean_apply_4(v_toBind_1579_, lean_box(0), lean_box(0), v_getEnv_1580_, v___f_1581_);
return v___x_1587_;
}
else
{
uint8_t v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec_ref_known(v___x_1586_, 1);
lean_dec(v___f_1581_);
lean_dec(v_getEnv_1580_);
v___x_1588_ = 0;
v___x_1589_ = lean_obj_once(&l_Lean_addInheritedDocString___redArg___lam__10___closed__1, &l_Lean_addInheritedDocString___redArg___lam__10___closed__1_once, _init_l_Lean_addInheritedDocString___redArg___lam__10___closed__1);
v___x_1590_ = l_Lean_MessageData_ofConstName(v_declName_1578_, v___x_1588_);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = lean_obj_once(&l_Lean_addDocStringCore___redArg___lam__2___closed__1, &l_Lean_addDocStringCore___redArg___lam__2___closed__1_once, _init_l_Lean_addDocStringCore___redArg___lam__2___closed__1);
v___x_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = l_Lean_throwError___redArg(v_inst_1582_, v_inst_1583_, v___x_1593_);
v___x_1595_ = lean_apply_4(v_toBind_1579_, lean_box(0), lean_box(0), v___x_1594_, v___f_1584_);
return v___x_1595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg___lam__12___boxed(lean_object* v_declName_1596_, lean_object* v_toBind_1597_, lean_object* v_getEnv_1598_, lean_object* v___f_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, lean_object* v___f_1602_, lean_object* v_____do__lift_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_addInheritedDocString___redArg___lam__12(v_declName_1596_, v_toBind_1597_, v_getEnv_1598_, v___f_1599_, v_inst_1600_, v_inst_1601_, v___f_1602_, v_____do__lift_1603_);
lean_dec_ref(v_____do__lift_1603_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString___redArg(lean_object* v_inst_1606_, lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_declName_1610_, lean_object* v_target_1611_){
_start:
{
lean_object* v_toBind_1612_; lean_object* v_getEnv_1613_; lean_object* v_modifyEnv_1614_; lean_object* v___f_1615_; lean_object* v___f_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___f_1619_; lean_object* v___f_1620_; lean_object* v___f_1621_; lean_object* v___f_1622_; lean_object* v___f_1623_; lean_object* v___f_1624_; lean_object* v___f_1625_; lean_object* v___x_1626_; 
v_toBind_1612_ = lean_ctor_get(v_inst_1606_, 1);
lean_inc_n(v_toBind_1612_, 7);
v_getEnv_1613_ = lean_ctor_get(v_inst_1608_, 0);
lean_inc_n(v_getEnv_1613_, 6);
v_modifyEnv_1614_ = lean_ctor_get(v_inst_1608_, 1);
lean_inc_n(v_modifyEnv_1614_, 2);
lean_dec_ref(v_inst_1608_);
lean_inc_n(v_target_1611_, 2);
lean_inc_n(v_declName_1610_, 5);
v___f_1615_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1615_, 0, v_declName_1610_);
lean_closure_set(v___f_1615_, 1, v_target_1611_);
v___f_1616_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__3), 4, 3);
lean_closure_set(v___f_1616_, 0, v_modifyEnv_1614_);
lean_closure_set(v___f_1616_, 1, v___f_1615_);
lean_closure_set(v___f_1616_, 2, v_declName_1610_);
v___x_1617_ = ((lean_object*)(l_Lean_addInheritedDocString___redArg___closed__0));
v___x_1618_ = lean_box(0);
v___f_1619_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__6), 8, 7);
lean_closure_set(v___f_1619_, 0, v_declName_1610_);
lean_closure_set(v___f_1619_, 1, v_target_1611_);
lean_closure_set(v___f_1619_, 2, v_modifyEnv_1614_);
lean_closure_set(v___f_1619_, 3, v_inst_1609_);
lean_closure_set(v___f_1619_, 4, v_toBind_1612_);
lean_closure_set(v___f_1619_, 5, v___f_1616_);
lean_closure_set(v___f_1619_, 6, v_getEnv_1613_);
lean_inc_ref(v___f_1619_);
v___f_1620_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__7), 2, 1);
lean_closure_set(v___f_1620_, 0, v___f_1619_);
lean_inc_ref_n(v_inst_1607_, 2);
lean_inc_ref_n(v_inst_1606_, 2);
v___f_1621_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__8), 10, 9);
lean_closure_set(v___f_1621_, 0, v___x_1618_);
lean_closure_set(v___f_1621_, 1, v_target_1611_);
lean_closure_set(v___f_1621_, 2, v_declName_1610_);
lean_closure_set(v___f_1621_, 3, v___x_1617_);
lean_closure_set(v___f_1621_, 4, v___f_1619_);
lean_closure_set(v___f_1621_, 5, v_inst_1606_);
lean_closure_set(v___f_1621_, 6, v_inst_1607_);
lean_closure_set(v___f_1621_, 7, v_toBind_1612_);
lean_closure_set(v___f_1621_, 8, v___f_1620_);
lean_inc_ref(v___f_1621_);
v___f_1622_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__9), 4, 3);
lean_closure_set(v___f_1622_, 0, v_toBind_1612_);
lean_closure_set(v___f_1622_, 1, v_getEnv_1613_);
lean_closure_set(v___f_1622_, 2, v___f_1621_);
v___f_1623_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__10), 9, 8);
lean_closure_set(v___f_1623_, 0, v___x_1618_);
lean_closure_set(v___f_1623_, 1, v_declName_1610_);
lean_closure_set(v___f_1623_, 2, v_toBind_1612_);
lean_closure_set(v___f_1623_, 3, v_getEnv_1613_);
lean_closure_set(v___f_1623_, 4, v___f_1621_);
lean_closure_set(v___f_1623_, 5, v_inst_1606_);
lean_closure_set(v___f_1623_, 6, v_inst_1607_);
lean_closure_set(v___f_1623_, 7, v___f_1622_);
lean_inc_ref(v___f_1623_);
v___f_1624_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__9), 4, 3);
lean_closure_set(v___f_1624_, 0, v_toBind_1612_);
lean_closure_set(v___f_1624_, 1, v_getEnv_1613_);
lean_closure_set(v___f_1624_, 2, v___f_1623_);
v___f_1625_ = lean_alloc_closure((void*)(l_Lean_addInheritedDocString___redArg___lam__12___boxed), 8, 7);
lean_closure_set(v___f_1625_, 0, v_declName_1610_);
lean_closure_set(v___f_1625_, 1, v_toBind_1612_);
lean_closure_set(v___f_1625_, 2, v_getEnv_1613_);
lean_closure_set(v___f_1625_, 3, v___f_1623_);
lean_closure_set(v___f_1625_, 4, v_inst_1606_);
lean_closure_set(v___f_1625_, 5, v_inst_1607_);
lean_closure_set(v___f_1625_, 6, v___f_1624_);
v___x_1626_ = lean_apply_4(v_toBind_1612_, lean_box(0), lean_box(0), v_getEnv_1613_, v___f_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_addInheritedDocString(lean_object* v_m_1627_, lean_object* v_inst_1628_, lean_object* v_inst_1629_, lean_object* v_inst_1630_, lean_object* v_inst_1631_, lean_object* v_declName_1632_, lean_object* v_target_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_addInheritedDocString___redArg(v_inst_1628_, v_inst_1629_, v_inst_1630_, v_inst_1631_, v_declName_1632_, v_target_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v_es_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_array_mk(v_es_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v_x_1639_, lean_object* v_x_1640_, lean_object* v_es_1641_){
_start:
{
lean_object* v_ents_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_ents_1642_ = lean_array_mk(v_es_1641_);
v___x_1643_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_));
lean_inc_ref(v_ents_1642_);
v___x_1644_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_ctor_set(v___x_1644_, 1, v_ents_1642_);
lean_ctor_set(v___x_1644_, 2, v_ents_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v_x_1645_, lean_object* v_x_1646_, lean_object* v_es_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(v_x_1645_, v_x_1646_, v_es_1647_);
lean_dec_ref(v_x_1646_);
lean_dec_ref(v_x_1645_);
return v_res_1648_;
}
}
static lean_object* _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = lean_unsigned_to_nat(32u);
v___x_1650_ = lean_mk_empty_array_with_capacity(v___x_1649_);
v___x_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(lean_object* v___x_1652_, lean_object* v_x_1653_){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; size_t v___x_1657_; lean_object* v___x_1658_; 
v___x_1654_ = lean_unsigned_to_nat(32u);
v___x_1655_ = lean_mk_empty_array_with_capacity(v___x_1654_);
v___x_1656_ = lean_obj_once(&l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_, &l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2__once, _init_l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_);
v___x_1657_ = ((size_t)5ULL);
lean_inc(v___x_1652_);
v___x_1658_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set(v___x_1658_, 1, v___x_1655_);
lean_ctor_set(v___x_1658_, 2, v___x_1652_);
lean_ctor_set(v___x_1658_, 3, v___x_1652_);
lean_ctor_set_usize(v___x_1658_, 4, v___x_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v___x_1659_, lean_object* v_x_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(v___x_1659_, v_x_1660_);
lean_dec_ref(v_x_1660_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_));
v___x_1684_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2____boxed(lean_object* v_a_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1709132598____hygCtx___hyg_2_();
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMainModuleDoc___lam__0(lean_object* v_addEntryFn_1687_, lean_object* v_doc_1688_, lean_object* v_s_1689_){
_start:
{
lean_object* v_importedEntries_1690_; lean_object* v_state_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1699_; 
v_importedEntries_1690_ = lean_ctor_get(v_s_1689_, 0);
v_state_1691_ = lean_ctor_get(v_s_1689_, 1);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_s_1689_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1693_ = v_s_1689_;
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_state_1691_);
lean_inc(v_importedEntries_1690_);
lean_dec(v_s_1689_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v_state_1695_; lean_object* v___x_1697_; 
v_state_1695_ = lean_apply_2(v_addEntryFn_1687_, v_state_1691_, v_doc_1688_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 1, v_state_1695_);
v___x_1697_ = v___x_1693_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_importedEntries_1690_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_state_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMainModuleDoc(lean_object* v_env_1700_, lean_object* v_doc_1701_){
_start:
{
lean_object* v___x_1702_; lean_object* v_toEnvExtension_1703_; lean_object* v_addEntryFn_1704_; lean_object* v_asyncMode_1705_; uint8_t v_logWrites_1706_; lean_object* v___f_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1702_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_1703_ = lean_ctor_get(v___x_1702_, 0);
v_addEntryFn_1704_ = lean_ctor_get(v___x_1702_, 3);
v_asyncMode_1705_ = lean_ctor_get(v_toEnvExtension_1703_, 2);
v_logWrites_1706_ = lean_ctor_get_uint8(v_toEnvExtension_1703_, sizeof(void*)*6);
lean_inc(v_addEntryFn_1704_);
v___f_1707_ = lean_alloc_closure((void*)(l_Lean_addMainModuleDoc___lam__0), 3, 2);
lean_closure_set(v___f_1707_, 0, v_addEntryFn_1704_);
lean_closure_set(v___f_1707_, 1, v_doc_1701_);
v___x_1708_ = lean_box(0);
v___x_1709_ = 1;
if (v_logWrites_1706_ == 0)
{
lean_object* v___x_1710_; 
lean_inc_ref(v_toEnvExtension_1703_);
v___x_1710_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1703_, v_env_1700_, v___f_1707_, v_asyncMode_1705_, v___x_1708_, v___x_1709_);
return v___x_1710_;
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_inc_ref_n(v_toEnvExtension_1703_, 2);
v___x_1711_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1703_, v_env_1700_);
lean_dec_ref(v_env_1700_);
v___x_1712_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1703_, v___x_1711_, v___f_1707_, v_asyncMode_1705_, v___x_1708_, v___x_1709_);
return v___x_1712_;
}
}
}
static lean_object* _init_l_Lean_getMainModuleDoc___closed__0(void){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModuleDoc(lean_object* v_env_1714_){
_start:
{
lean_object* v___x_1715_; lean_object* v_toEnvExtension_1716_; lean_object* v_asyncMode_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1715_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v_toEnvExtension_1716_ = lean_ctor_get(v___x_1715_, 0);
v_asyncMode_1717_ = lean_ctor_get(v_toEnvExtension_1716_, 2);
v___x_1718_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_1719_ = lean_box(0);
v___x_1720_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1718_, v___x_1715_, v_env_1714_, v_asyncMode_1717_, v___x_1719_);
return v___x_1720_;
}
}
static lean_object* _init_l_Lean_getModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = lean_obj_once(&l_Lean_getMainModuleDoc___closed__0, &l_Lean_getMainModuleDoc___closed__0_once, _init_l_Lean_getMainModuleDoc___closed__0);
v___x_1722_ = lean_box(0);
v___x_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
lean_ctor_set(v___x_1723_, 1, v___x_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f(lean_object* v_env_1724_, lean_object* v_moduleName_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Lean_Environment_getModuleIdx_x3f(v_env_1724_, v_moduleName_1725_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_box(0);
return v___x_1727_;
}
else
{
lean_object* v_val_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1739_; 
v_val_1728_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1730_ = v___x_1726_;
v_isShared_1731_ = v_isSharedCheck_1739_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_val_1728_);
lean_dec(v___x_1726_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1739_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1732_ = lean_obj_once(&l_Lean_getModuleDoc_x3f___closed__0, &l_Lean_getModuleDoc_x3f___closed__0_once, _init_l_Lean_getModuleDoc_x3f___closed__0);
v___x_1733_ = l___private_Lean_DocString_Extension_0__Lean_moduleDocExt;
v___x_1734_ = 1;
v___x_1735_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1732_, v___x_1733_, v_env_1724_, v_val_1728_, v___x_1734_);
lean_dec(v_val_1728_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1735_);
v___x_1737_ = v___x_1730_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getModuleDoc_x3f___boxed(lean_object* v_env_1740_, lean_object* v_moduleName_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_getModuleDoc_x3f(v_env_1740_, v_moduleName_1741_);
lean_dec(v_moduleName_1741_);
lean_dec_ref(v_env_1740_);
return v_res_1742_;
}
}
static lean_object* _init_l_Lean_getDocStringText___redArg___closed__1(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__0));
v___x_1745_ = l_Lean_stringToMessageData(v___x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___redArg(lean_object* v_inst_1749_, lean_object* v_inst_1750_, lean_object* v_stx_1751_){
_start:
{
lean_object* v_toApplicative_1758_; lean_object* v_toPure_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_toApplicative_1758_ = lean_ctor_get(v_inst_1749_, 0);
v_toPure_1759_ = lean_ctor_get(v_toApplicative_1758_, 1);
v___x_1760_ = lean_unsigned_to_nat(1u);
v___x_1761_ = l_Lean_Syntax_getArg(v_stx_1751_, v___x_1760_);
if (lean_obj_tag(v___x_1761_) == 1)
{
lean_object* v_kind_1762_; 
v_kind_1762_ = lean_ctor_get(v___x_1761_, 1);
lean_inc(v_kind_1762_);
if (lean_obj_tag(v_kind_1762_) == 1)
{
lean_object* v_pre_1763_; 
v_pre_1763_ = lean_ctor_get(v_kind_1762_, 0);
lean_inc(v_pre_1763_);
if (lean_obj_tag(v_pre_1763_) == 1)
{
lean_object* v_pre_1764_; 
v_pre_1764_ = lean_ctor_get(v_pre_1763_, 0);
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
if (lean_obj_tag(v_pre_1766_) == 0)
{
lean_object* v_args_1767_; lean_object* v_str_1768_; lean_object* v_str_1769_; lean_object* v_str_1770_; lean_object* v_str_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v_args_1767_ = lean_ctor_get(v___x_1761_, 2);
lean_inc_ref(v_args_1767_);
lean_dec_ref_known(v___x_1761_, 3);
v_str_1768_ = lean_ctor_get(v_kind_1762_, 1);
lean_inc_ref(v_str_1768_);
lean_dec_ref_known(v_kind_1762_, 2);
v_str_1769_ = lean_ctor_get(v_pre_1763_, 1);
lean_inc_ref(v_str_1769_);
lean_dec_ref_known(v_pre_1763_, 2);
v_str_1770_ = lean_ctor_get(v_pre_1764_, 1);
lean_inc_ref(v_str_1770_);
lean_dec_ref_known(v_pre_1764_, 2);
v_str_1771_ = lean_ctor_get(v_pre_1765_, 1);
lean_inc_ref(v_str_1771_);
lean_dec_ref_known(v_pre_1765_, 2);
v___x_1772_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__5_00___x40_Lean_DocString_Extension_1462683259____hygCtx___hyg_4_));
v___x_1773_ = lean_string_dec_eq(v_str_1771_, v___x_1772_);
lean_dec_ref(v_str_1771_);
if (v___x_1773_ == 0)
{
lean_dec_ref(v_str_1770_);
lean_dec_ref(v_str_1769_);
lean_dec_ref(v_str_1768_);
lean_dec_ref(v_args_1767_);
goto v___jp_1752_;
}
else
{
lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1774_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__2));
v___x_1775_ = lean_string_dec_eq(v_str_1770_, v___x_1774_);
lean_dec_ref(v_str_1770_);
if (v___x_1775_ == 0)
{
lean_dec_ref(v_str_1769_);
lean_dec_ref(v_str_1768_);
lean_dec_ref(v_args_1767_);
goto v___jp_1752_;
}
else
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__3));
v___x_1777_ = lean_string_dec_eq(v_str_1769_, v___x_1776_);
lean_dec_ref(v_str_1769_);
if (v___x_1777_ == 0)
{
lean_dec_ref(v_str_1768_);
lean_dec_ref(v_args_1767_);
goto v___jp_1752_;
}
else
{
lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = ((lean_object*)(l_Lean_getDocStringText___redArg___closed__4));
v___x_1779_ = lean_string_dec_eq(v_str_1768_, v___x_1778_);
lean_dec_ref(v_str_1768_);
if (v___x_1779_ == 0)
{
lean_dec_ref(v_args_1767_);
goto v___jp_1752_;
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1780_ = lean_array_get_size(v_args_1767_);
v___x_1781_ = lean_unsigned_to_nat(2u);
v___x_1782_ = lean_nat_dec_eq(v___x_1780_, v___x_1781_);
if (v___x_1782_ == 0)
{
lean_dec_ref(v_args_1767_);
goto v___jp_1752_;
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = lean_array_fget(v_args_1767_, v___x_1783_);
lean_dec_ref(v_args_1767_);
if (lean_obj_tag(v___x_1784_) == 2)
{
lean_object* v_val_1785_; lean_object* v___x_1786_; 
lean_inc(v_toPure_1759_);
lean_dec(v_stx_1751_);
lean_dec_ref(v_inst_1750_);
lean_dec_ref(v_inst_1749_);
v_val_1785_ = lean_ctor_get(v___x_1784_, 1);
lean_inc_ref(v_val_1785_);
lean_dec_ref_known(v___x_1784_, 2);
v___x_1786_ = lean_apply_2(v_toPure_1759_, lean_box(0), v_val_1785_);
return v___x_1786_;
}
else
{
lean_dec(v___x_1784_);
goto v___jp_1752_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1765_, 2);
lean_dec_ref_known(v_pre_1764_, 2);
lean_dec_ref_known(v_pre_1763_, 2);
lean_dec_ref_known(v_kind_1762_, 2);
lean_dec_ref_known(v___x_1761_, 3);
goto v___jp_1752_;
}
}
else
{
lean_dec(v_pre_1765_);
lean_dec_ref_known(v_pre_1764_, 2);
lean_dec_ref_known(v_pre_1763_, 2);
lean_dec_ref_known(v_kind_1762_, 2);
lean_dec_ref_known(v___x_1761_, 3);
goto v___jp_1752_;
}
}
else
{
lean_dec_ref_known(v_pre_1763_, 2);
lean_dec(v_pre_1764_);
lean_dec_ref_known(v_kind_1762_, 2);
lean_dec_ref_known(v___x_1761_, 3);
goto v___jp_1752_;
}
}
else
{
lean_dec(v_pre_1763_);
lean_dec_ref_known(v_kind_1762_, 2);
lean_dec_ref_known(v___x_1761_, 3);
goto v___jp_1752_;
}
}
else
{
lean_dec_ref_known(v___x_1761_, 3);
lean_dec(v_kind_1762_);
goto v___jp_1752_;
}
}
else
{
lean_dec(v___x_1761_);
goto v___jp_1752_;
}
v___jp_1752_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1753_ = lean_obj_once(&l_Lean_getDocStringText___redArg___closed__1, &l_Lean_getDocStringText___redArg___closed__1_once, _init_l_Lean_getDocStringText___redArg___closed__1);
lean_inc(v_stx_1751_);
v___x_1754_ = l_Lean_MessageData_ofSyntax(v_stx_1751_);
v___x_1755_ = l_Lean_indentD(v___x_1754_);
v___x_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1753_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = l_Lean_throwErrorAt___redArg(v_inst_1749_, v_inst_1750_, v_stx_1751_, v___x_1756_);
return v___x_1757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText(lean_object* v_m_1787_, lean_object* v_inst_1788_, lean_object* v_inst_1789_, lean_object* v_stx_1790_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_getDocStringText___redArg(v_inst_1788_, v_inst_1789_, v_stx_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT uint8_t l_Lean_isVersoDocComment(lean_object* v_stx_1798_){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1799_ = lean_unsigned_to_nat(1u);
v___x_1800_ = l_Lean_Syntax_getArg(v_stx_1798_, v___x_1799_);
v___x_1801_ = ((lean_object*)(l_Lean_isVersoDocComment___closed__1));
v___x_1802_ = l_Lean_Syntax_isOfKind(v___x_1800_, v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_isVersoDocComment___boxed(lean_object* v_stx_1803_){
_start:
{
uint8_t v_res_1804_; lean_object* v_r_1805_; 
v_res_1804_ = l_Lean_isVersoDocComment(v_stx_1803_);
lean_dec(v_stx_1803_);
v_r_1805_ = lean_box(v_res_1804_);
return v_r_1805_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = l_Lean_instInhabitedDeclarationRange_default;
v___x_1809_ = ((lean_object*)(l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__0));
v___x_1810_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
lean_ctor_set(v___x_1810_, 2, v___x_1808_);
return v___x_1810_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default(void){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = lean_obj_once(&l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1, &l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1_once, _init_l_Lean_VersoModuleDocs_instInhabitedSnippet_default___closed__1);
return v___x_1811_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instInhabitedSnippet(void){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_VersoModuleDocs_instInhabitedSnippet_default;
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__2(lean_object* v_a_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_nat_to_int(v_a_1813_);
return v___x_1814_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = lean_unsigned_to_nat(2u);
v___x_1822_ = lean_nat_to_int(v___x_1821_);
return v___x_1822_;
}
}
static lean_object* _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = lean_unsigned_to_nat(1u);
v___x_1824_ = lean_nat_to_int(v___x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(lean_object* v_x_1837_, lean_object* v_x_1838_, lean_object* v_x_1839_){
_start:
{
if (lean_obj_tag(v_x_1839_) == 0)
{
lean_dec(v_x_1837_);
return v_x_1838_;
}
else
{
lean_object* v_head_1840_; lean_object* v_tail_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1852_; 
v_head_1840_ = lean_ctor_get(v_x_1839_, 0);
v_tail_1841_ = lean_ctor_get(v_x_1839_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_x_1839_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1843_ = v_x_1839_;
v_isShared_1844_ = v_isSharedCheck_1852_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_tail_1841_);
lean_inc(v_head_1840_);
lean_dec(v_x_1839_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1852_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
lean_inc(v_x_1837_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set_tag(v___x_1843_, 5);
lean_ctor_set(v___x_1843_, 1, v_x_1837_);
lean_ctor_set(v___x_1843_, 0, v_x_1838_);
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_x_1838_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_x_1837_);
v___x_1846_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_unsigned_to_nat(0u);
v___x_1848_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_1840_, v___x_1847_);
v___x_1849_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1846_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v_x_1838_ = v___x_1849_;
v_x_1839_ = v_tail_1841_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(lean_object* v_x_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
if (lean_obj_tag(v_x_1855_) == 0)
{
lean_dec(v_x_1853_);
return v_x_1854_;
}
else
{
lean_object* v_head_1856_; lean_object* v_tail_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1868_; 
v_head_1856_ = lean_ctor_get(v_x_1855_, 0);
v_tail_1857_ = lean_ctor_get(v_x_1855_, 1);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_x_1855_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1859_ = v_x_1855_;
v_isShared_1860_ = v_isSharedCheck_1868_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_tail_1857_);
lean_inc(v_head_1856_);
lean_dec(v_x_1855_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1868_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
lean_inc(v_x_1853_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set_tag(v___x_1859_, 5);
lean_ctor_set(v___x_1859_, 1, v_x_1853_);
lean_ctor_set(v___x_1859_, 0, v_x_1854_);
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_x_1854_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_x_1853_);
v___x_1862_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1863_ = lean_unsigned_to_nat(0u);
v___x_1864_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_head_1856_, v___x_1863_);
v___x_1865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1862_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10_spec__18(v_x_1853_, v___x_1865_, v_tail_1857_);
return v___x_1866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_1869_, lean_object* v_x_1870_){
_start:
{
if (lean_obj_tag(v_x_1869_) == 0)
{
lean_object* v___x_1871_; 
lean_dec(v_x_1870_);
v___x_1871_ = lean_box(0);
return v___x_1871_;
}
else
{
lean_object* v_tail_1872_; 
v_tail_1872_ = lean_ctor_get(v_x_1869_, 1);
if (lean_obj_tag(v_tail_1872_) == 0)
{
lean_object* v_head_1873_; lean_object* v___x_1874_; 
lean_dec(v_x_1870_);
v_head_1873_ = lean_ctor_get(v_x_1869_, 0);
lean_inc(v_head_1873_);
lean_dec_ref_known(v_x_1869_, 2);
v___x_1874_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_1873_);
return v___x_1874_;
}
else
{
lean_object* v_head_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_inc(v_tail_1872_);
v_head_1875_ = lean_ctor_get(v_x_1869_, 0);
lean_inc(v_head_1875_);
lean_dec_ref_known(v_x_1869_, 2);
v___x_1876_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(v_head_1875_);
v___x_1877_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5_spec__10(v_x_1870_, v___x_1876_, v_tail_1872_);
return v___x_1877_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5(void){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__0));
v___x_1880_ = lean_string_length(v___x_1879_);
return v___x_1880_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6(void){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__5);
v___x_1882_ = lean_nat_to_int(v___x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_xs_1891_){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1892_ = lean_array_get_size(v_xs_1891_);
v___x_1893_ = lean_unsigned_to_nat(0u);
v___x_1894_ = lean_nat_dec_eq(v___x_1892_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1895_ = lean_array_to_list(v_xs_1891_);
v___x_1896_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_1897_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_1895_, v___x_1896_);
v___x_1898_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_1899_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_1900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
lean_ctor_set(v___x_1900_, 1, v___x_1897_);
v___x_1901_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_1902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1900_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1898_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = l_Std_Format_fill(v___x_1903_);
return v___x_1904_;
}
else
{
lean_object* v___x_1905_; 
lean_dec_ref(v_xs_1891_);
v___x_1905_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_1905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_1960_, lean_object* v_prec_1961_){
_start:
{
switch(lean_obj_tag(v_x_1960_))
{
case 0:
{
lean_object* v_string_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1982_; 
v_string_1962_ = lean_ctor_get(v_x_1960_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_x_1960_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1964_ = v_x_1960_;
v_isShared_1965_ = v_isSharedCheck_1982_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_string_1962_);
lean_dec(v_x_1960_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1982_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___y_1967_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1978_ = lean_unsigned_to_nat(1024u);
v___x_1979_ = lean_nat_dec_le(v___x_1978_, v_prec_1961_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_1967_ = v___x_1980_;
goto v___jp_1966_;
}
else
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_1967_ = v___x_1981_;
goto v___jp_1966_;
}
v___jp_1966_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1968_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__2));
v___x_1969_ = l_String_quote(v_string_1962_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set_tag(v___x_1964_, 3);
lean_ctor_set(v___x_1964_, 0, v___x_1969_);
v___x_1971_ = v___x_1964_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1968_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
lean_inc(v___y_1967_);
v___x_1973_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___y_1967_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = 0;
v___x_1975_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1975_, 0, v___x_1973_);
lean_ctor_set_uint8(v___x_1975_, sizeof(void*)*1, v___x_1974_);
v___x_1976_ = l_Repr_addAppParen(v___x_1975_, v_prec_1961_);
return v___x_1976_;
}
}
}
}
case 1:
{
lean_object* v_content_1983_; lean_object* v___y_1985_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v_content_1983_ = lean_ctor_get(v_x_1960_, 0);
lean_inc_ref(v_content_1983_);
lean_dec_ref_known(v_x_1960_, 1);
v___x_1993_ = lean_unsigned_to_nat(1024u);
v___x_1994_ = lean_nat_dec_le(v___x_1993_, v_prec_1961_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; 
v___x_1995_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_1985_ = v___x_1995_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_1996_; 
v___x_1996_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_1985_ = v___x_1996_;
goto v___jp_1984_;
}
v___jp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1986_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__7));
v___x_1987_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_1983_);
v___x_1988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
lean_inc(v___y_1985_);
v___x_1989_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___y_1985_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = 0;
v___x_1991_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set_uint8(v___x_1991_, sizeof(void*)*1, v___x_1990_);
v___x_1992_ = l_Repr_addAppParen(v___x_1991_, v_prec_1961_);
return v___x_1992_;
}
}
case 2:
{
lean_object* v_content_1997_; lean_object* v___y_1999_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v_content_1997_ = lean_ctor_get(v_x_1960_, 0);
lean_inc_ref(v_content_1997_);
lean_dec_ref_known(v_x_1960_, 1);
v___x_2007_ = lean_unsigned_to_nat(1024u);
v___x_2008_ = lean_nat_dec_le(v___x_2007_, v_prec_1961_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_1999_ = v___x_2009_;
goto v___jp_1998_;
}
else
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_1999_ = v___x_2010_;
goto v___jp_1998_;
}
v___jp_1998_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2000_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__10));
v___x_2001_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_1997_);
v___x_2002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2000_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
lean_inc(v___y_1999_);
v___x_2003_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___y_1999_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = 0;
v___x_2005_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2005_, 0, v___x_2003_);
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*1, v___x_2004_);
v___x_2006_ = l_Repr_addAppParen(v___x_2005_, v_prec_1961_);
return v___x_2006_;
}
}
case 3:
{
lean_object* v_string_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2031_; 
v_string_2011_ = lean_ctor_get(v_x_1960_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_x_1960_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2013_ = v_x_1960_;
v_isShared_2014_ = v_isSharedCheck_2031_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_string_2011_);
lean_dec(v_x_1960_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2031_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___y_2016_; lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = lean_unsigned_to_nat(1024u);
v___x_2028_ = lean_nat_dec_le(v___x_2027_, v_prec_1961_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; 
v___x_2029_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2016_ = v___x_2029_;
goto v___jp_2015_;
}
else
{
lean_object* v___x_2030_; 
v___x_2030_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2016_ = v___x_2030_;
goto v___jp_2015_;
}
v___jp_2015_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2017_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__13));
v___x_2018_ = l_String_quote(v_string_2011_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2018_);
v___x_2020_ = v___x_2013_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2017_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
lean_inc(v___y_2016_);
v___x_2022_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___y_2016_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
v___x_2023_ = 0;
v___x_2024_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2024_, 0, v___x_2022_);
lean_ctor_set_uint8(v___x_2024_, sizeof(void*)*1, v___x_2023_);
v___x_2025_ = l_Repr_addAppParen(v___x_2024_, v_prec_1961_);
return v___x_2025_;
}
}
}
}
case 4:
{
uint8_t v_mode_2032_; lean_object* v_string_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2058_; 
v_mode_2032_ = lean_ctor_get_uint8(v_x_1960_, sizeof(void*)*1);
v_string_2033_ = lean_ctor_get(v_x_1960_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_x_1960_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2035_ = v_x_1960_;
v_isShared_2036_ = v_isSharedCheck_2058_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_string_2033_);
lean_dec(v_x_1960_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2058_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___y_2038_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2054_ = lean_unsigned_to_nat(1024u);
v___x_2055_ = lean_nat_dec_le(v___x_2054_, v_prec_1961_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2038_ = v___x_2056_;
goto v___jp_2037_;
}
else
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2038_ = v___x_2057_;
goto v___jp_2037_;
}
v___jp_2037_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; lean_object* v___x_2051_; 
v___x_2039_ = lean_box(1);
v___x_2040_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__16));
v___x_2041_ = lean_unsigned_to_nat(1024u);
v___x_2042_ = l_Lean_Doc_instReprMathMode_repr(v_mode_2032_, v___x_2041_);
v___x_2043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2040_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set(v___x_2044_, 1, v___x_2039_);
v___x_2045_ = l_String_quote(v_string_2033_);
v___x_2046_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
v___x_2047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2044_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
lean_inc(v___y_2038_);
v___x_2048_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___y_2038_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
v___x_2049_ = 0;
if (v_isShared_2036_ == 0)
{
lean_ctor_set_tag(v___x_2035_, 6);
lean_ctor_set(v___x_2035_, 0, v___x_2048_);
v___x_2051_ = v___x_2035_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2048_);
v___x_2051_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2052_; 
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*1, v___x_2049_);
v___x_2052_ = l_Repr_addAppParen(v___x_2051_, v_prec_1961_);
return v___x_2052_;
}
}
}
}
case 5:
{
lean_object* v_string_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2079_; 
v_string_2059_ = lean_ctor_get(v_x_1960_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_x_1960_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2061_ = v_x_1960_;
v_isShared_2062_ = v_isSharedCheck_2079_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_string_2059_);
lean_dec(v_x_1960_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2079_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___y_2064_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = lean_unsigned_to_nat(1024u);
v___x_2076_ = lean_nat_dec_le(v___x_2075_, v_prec_1961_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; 
v___x_2077_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2064_ = v___x_2077_;
goto v___jp_2063_;
}
else
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2064_ = v___x_2078_;
goto v___jp_2063_;
}
v___jp_2063_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2065_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__19));
v___x_2066_ = l_String_quote(v_string_2059_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set_tag(v___x_2061_, 3);
lean_ctor_set(v___x_2061_, 0, v___x_2066_);
v___x_2068_ = v___x_2061_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2065_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
lean_inc(v___y_2064_);
v___x_2070_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___y_2064_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = 0;
v___x_2072_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set_uint8(v___x_2072_, sizeof(void*)*1, v___x_2071_);
v___x_2073_ = l_Repr_addAppParen(v___x_2072_, v_prec_1961_);
return v___x_2073_;
}
}
}
}
case 6:
{
lean_object* v_content_2080_; lean_object* v_url_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2105_; 
v_content_2080_ = lean_ctor_get(v_x_1960_, 0);
v_url_2081_ = lean_ctor_get(v_x_1960_, 1);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_x_1960_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2083_ = v_x_1960_;
v_isShared_2084_ = v_isSharedCheck_2105_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_url_2081_);
lean_inc(v_content_2080_);
lean_dec(v_x_1960_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2105_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___y_2086_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2101_ = lean_unsigned_to_nat(1024u);
v___x_2102_ = lean_nat_dec_le(v___x_2101_, v_prec_1961_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; 
v___x_2103_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2086_ = v___x_2103_;
goto v___jp_2085_;
}
else
{
lean_object* v___x_2104_; 
v___x_2104_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2086_ = v___x_2104_;
goto v___jp_2085_;
}
v___jp_2085_:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2087_ = lean_box(1);
v___x_2088_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__22));
v___x_2089_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2080_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set_tag(v___x_2083_, 5);
lean_ctor_set(v___x_2083_, 1, v___x_2089_);
lean_ctor_set(v___x_2083_, 0, v___x_2088_);
v___x_2091_ = v___x_2083_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2092_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v___x_2087_);
v___x_2093_ = l_String_quote(v_url_2081_);
v___x_2094_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
v___x_2095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2092_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
lean_inc(v___y_2086_);
v___x_2096_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___y_2086_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = 0;
v___x_2098_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2098_, 0, v___x_2096_);
lean_ctor_set_uint8(v___x_2098_, sizeof(void*)*1, v___x_2097_);
v___x_2099_ = l_Repr_addAppParen(v___x_2098_, v_prec_1961_);
return v___x_2099_;
}
}
}
}
case 7:
{
lean_object* v_name_2106_; lean_object* v_content_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2131_; 
v_name_2106_ = lean_ctor_get(v_x_1960_, 0);
v_content_2107_ = lean_ctor_get(v_x_1960_, 1);
v_isSharedCheck_2131_ = !lean_is_exclusive(v_x_1960_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2109_ = v_x_1960_;
v_isShared_2110_ = v_isSharedCheck_2131_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_content_2107_);
lean_inc(v_name_2106_);
lean_dec(v_x_1960_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2131_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___y_2112_; lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2127_ = lean_unsigned_to_nat(1024u);
v___x_2128_ = lean_nat_dec_le(v___x_2127_, v_prec_1961_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; 
v___x_2129_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2112_ = v___x_2129_;
goto v___jp_2111_;
}
else
{
lean_object* v___x_2130_; 
v___x_2130_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2112_ = v___x_2130_;
goto v___jp_2111_;
}
v___jp_2111_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2118_; 
v___x_2113_ = lean_box(1);
v___x_2114_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__25));
v___x_2115_ = l_String_quote(v_name_2106_);
v___x_2116_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set_tag(v___x_2109_, 5);
lean_ctor_set(v___x_2109_, 1, v___x_2116_);
lean_ctor_set(v___x_2109_, 0, v___x_2114_);
v___x_2118_ = v___x_2109_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
lean_ctor_set(v___x_2119_, 1, v___x_2113_);
v___x_2120_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2107_);
v___x_2121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2119_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
lean_inc(v___y_2112_);
v___x_2122_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___y_2112_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = 0;
v___x_2124_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*1, v___x_2123_);
v___x_2125_ = l_Repr_addAppParen(v___x_2124_, v_prec_1961_);
return v___x_2125_;
}
}
}
}
case 8:
{
lean_object* v_alt_2132_; lean_object* v_url_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2158_; 
v_alt_2132_ = lean_ctor_get(v_x_1960_, 0);
v_url_2133_ = lean_ctor_get(v_x_1960_, 1);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_x_1960_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2135_ = v_x_1960_;
v_isShared_2136_ = v_isSharedCheck_2158_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_url_2133_);
lean_inc(v_alt_2132_);
lean_dec(v_x_1960_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2158_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___y_2138_; lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2154_ = lean_unsigned_to_nat(1024u);
v___x_2155_ = lean_nat_dec_le(v___x_2154_, v_prec_1961_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2138_ = v___x_2156_;
goto v___jp_2137_;
}
else
{
lean_object* v___x_2157_; 
v___x_2157_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2138_ = v___x_2157_;
goto v___jp_2137_;
}
v___jp_2137_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2139_ = lean_box(1);
v___x_2140_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__28));
v___x_2141_ = l_String_quote(v_alt_2132_);
v___x_2142_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set_tag(v___x_2135_, 5);
lean_ctor_set(v___x_2135_, 1, v___x_2142_);
lean_ctor_set(v___x_2135_, 0, v___x_2140_);
v___x_2144_ = v___x_2135_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
lean_ctor_set(v___x_2145_, 1, v___x_2139_);
v___x_2146_ = l_String_quote(v_url_2133_);
v___x_2147_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
v___x_2148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2145_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
lean_inc(v___y_2138_);
v___x_2149_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___y_2138_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = 0;
v___x_2151_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2151_, 0, v___x_2149_);
lean_ctor_set_uint8(v___x_2151_, sizeof(void*)*1, v___x_2150_);
v___x_2152_ = l_Repr_addAppParen(v___x_2151_, v_prec_1961_);
return v___x_2152_;
}
}
}
}
case 9:
{
lean_object* v_content_2159_; lean_object* v___y_2161_; lean_object* v___x_2169_; uint8_t v___x_2170_; 
v_content_2159_ = lean_ctor_get(v_x_1960_, 0);
lean_inc_ref(v_content_2159_);
lean_dec_ref_known(v_x_1960_, 1);
v___x_2169_ = lean_unsigned_to_nat(1024u);
v___x_2170_ = lean_nat_dec_le(v___x_2169_, v_prec_1961_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; 
v___x_2171_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2161_ = v___x_2171_;
goto v___jp_2160_;
}
else
{
lean_object* v___x_2172_; 
v___x_2172_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2161_ = v___x_2172_;
goto v___jp_2160_;
}
v___jp_2160_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2162_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__31));
v___x_2163_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2159_);
v___x_2164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
lean_inc(v___y_2161_);
v___x_2165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___y_2161_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = 0;
v___x_2167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2167_, 0, v___x_2165_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*1, v___x_2166_);
v___x_2168_ = l_Repr_addAppParen(v___x_2167_, v_prec_1961_);
return v___x_2168_;
}
}
default: 
{
lean_object* v_container_2173_; lean_object* v_content_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2224_; 
v_container_2173_ = lean_ctor_get(v_x_1960_, 0);
v_content_2174_ = lean_ctor_get(v_x_1960_, 1);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_x_1960_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2176_ = v_x_1960_;
v_isShared_2177_ = v_isSharedCheck_2224_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_content_2174_);
lean_inc(v_container_2173_);
lean_dec(v_x_1960_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2224_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2194_; lean_object* v___x_2220_; uint8_t v___x_2221_; 
v___x_2220_ = lean_unsigned_to_nat(1024u);
v___x_2221_ = lean_nat_dec_le(v___x_2220_, v_prec_1961_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; 
v___x_2222_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2194_ = v___x_2222_;
goto v___jp_2193_;
}
else
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2194_ = v___x_2223_;
goto v___jp_2193_;
}
v___jp_2178_:
{
lean_object* v___x_2184_; 
lean_inc(v___y_2181_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set_tag(v___x_2176_, 5);
lean_ctor_set(v___x_2176_, 1, v___y_2182_);
lean_ctor_set(v___x_2176_, 0, v___y_2181_);
v___x_2184_ = v___x_2176_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___y_2181_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v___y_2182_);
v___x_2184_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_inc(v___y_2179_);
v___x_2185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
lean_ctor_set(v___x_2185_, 1, v___y_2179_);
v___x_2186_ = l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_content_2174_);
v___x_2187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2185_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
lean_inc(v___y_2180_);
v___x_2188_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___y_2180_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
v___x_2189_ = 0;
v___x_2190_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2190_, 0, v___x_2188_);
lean_ctor_set_uint8(v___x_2190_, sizeof(void*)*1, v___x_2189_);
v___x_2191_ = l_Repr_addAppParen(v___x_2190_, v_prec_1961_);
return v___x_2191_;
}
}
v___jp_2193_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = lean_box(1);
v___x_2196_ = ((lean_object*)(l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__34));
if (lean_obj_tag(v_container_2173_) == 0)
{
lean_object* v_val_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; lean_object* v___x_2206_; 
v_val_2197_ = lean_ctor_get(v_container_2173_, 0);
lean_inc(v_val_2197_);
lean_dec_ref_known(v_container_2173_, 1);
v___x_2198_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__5));
v___x_2199_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_2197_);
lean_dec(v_val_2197_);
v___x_2200_ = lean_unsigned_to_nat(0u);
v___x_2201_ = l_Lean_Name_reprPrec(v___x_2199_, v___x_2200_);
v___x_2202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2198_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__7));
v___x_2204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = 0;
v___x_2206_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2206_, 0, v___x_2204_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*1, v___x_2205_);
v___y_2179_ = v___x_2195_;
v___y_2180_ = v___y_2194_;
v___y_2181_ = v___x_2196_;
v___y_2182_ = v___x_2206_;
goto v___jp_2178_;
}
else
{
lean_object* v_index_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2219_; 
v_index_2207_ = lean_ctor_get(v_container_2173_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v_container_2173_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2209_ = v_container_2173_;
v_isShared_2210_ = v_isSharedCheck_2219_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_index_2207_);
lean_dec(v_container_2173_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2219_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2211_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__10));
v___x_2212_ = l_Nat_reprFast(v_index_2207_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set_tag(v___x_2209_, 3);
lean_ctor_set(v___x_2209_, 0, v___x_2212_);
v___x_2214_ = v___x_2209_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2211_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = 0;
v___x_2217_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2217_, 0, v___x_2215_);
lean_ctor_set_uint8(v___x_2217_, sizeof(void*)*1, v___x_2216_);
v___y_2179_ = v___x_2195_;
v___y_2180_ = v___y_2194_;
v___y_2181_ = v___x_2196_;
v___y_2182_ = v___x_2217_;
goto v___jp_2178_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5___lam__0(lean_object* v___y_2225_){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_unsigned_to_nat(0u);
v___x_2227_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v___y_2225_, v___x_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_2228_, lean_object* v_prec_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4(v_x_2228_, v_prec_2229_);
lean_dec(v_prec_2229_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(lean_object* v_xs_2231_){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; uint8_t v___x_2234_; 
v___x_2232_ = lean_array_get_size(v_xs_2231_);
v___x_2233_ = lean_unsigned_to_nat(0u);
v___x_2234_ = lean_nat_dec_eq(v___x_2232_, v___x_2233_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2235_ = lean_array_to_list(v_xs_2231_);
v___x_2236_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2237_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__5(v___x_2235_, v___x_2236_);
v___x_2238_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2239_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
lean_ctor_set(v___x_2240_, 1, v___x_2237_);
v___x_2241_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2240_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
v___x_2243_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2238_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = l_Std_Format_fill(v___x_2243_);
return v___x_2244_;
}
else
{
lean_object* v___x_2245_; 
lean_dec_ref(v_xs_2231_);
v___x_2245_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2245_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = lean_unsigned_to_nat(12u);
v___x_2277_ = lean_nat_to_int(v___x_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(lean_object* v_x_2278_, lean_object* v_x_2279_, lean_object* v_x_2280_){
_start:
{
if (lean_obj_tag(v_x_2280_) == 0)
{
lean_dec(v_x_2278_);
return v_x_2279_;
}
else
{
lean_object* v_head_2281_; lean_object* v_tail_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2293_; 
v_head_2281_ = lean_ctor_get(v_x_2280_, 0);
v_tail_2282_ = lean_ctor_get(v_x_2280_, 1);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_x_2280_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2284_ = v_x_2280_;
v_isShared_2285_ = v_isSharedCheck_2293_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_tail_2282_);
lean_inc(v_head_2281_);
lean_dec(v_x_2280_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2293_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
lean_inc(v_x_2278_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set_tag(v___x_2284_, 5);
lean_ctor_set(v___x_2284_, 1, v_x_2278_);
lean_ctor_set(v___x_2284_, 0, v_x_2279_);
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_x_2279_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_x_2278_);
v___x_2287_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2288_ = lean_unsigned_to_nat(0u);
v___x_2289_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_2281_, v___x_2288_);
v___x_2290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2287_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v_x_2279_ = v___x_2290_;
v_x_2280_ = v_tail_2282_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(lean_object* v_x_2294_, lean_object* v_x_2295_, lean_object* v_x_2296_){
_start:
{
if (lean_obj_tag(v_x_2296_) == 0)
{
lean_dec(v_x_2294_);
return v_x_2295_;
}
else
{
lean_object* v_head_2297_; lean_object* v_tail_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2309_; 
v_head_2297_ = lean_ctor_get(v_x_2296_, 0);
v_tail_2298_ = lean_ctor_get(v_x_2296_, 1);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_x_2296_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2300_ = v_x_2296_;
v_isShared_2301_ = v_isSharedCheck_2309_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_tail_2298_);
lean_inc(v_head_2297_);
lean_dec(v_x_2296_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2309_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
lean_inc(v_x_2294_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set_tag(v___x_2300_, 5);
lean_ctor_set(v___x_2300_, 1, v_x_2294_);
lean_ctor_set(v___x_2300_, 0, v_x_2295_);
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_x_2295_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_x_2294_);
v___x_2303_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2304_ = lean_unsigned_to_nat(0u);
v___x_2305_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_head_2297_, v___x_2304_);
v___x_2306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2303_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7_spec__15(v_x_2294_, v___x_2306_, v_tail_2298_);
return v___x_2307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(lean_object* v_x_2310_, lean_object* v_x_2311_){
_start:
{
if (lean_obj_tag(v_x_2310_) == 0)
{
lean_object* v___x_2312_; 
lean_dec(v_x_2311_);
v___x_2312_ = lean_box(0);
return v___x_2312_;
}
else
{
lean_object* v_tail_2313_; 
v_tail_2313_ = lean_ctor_get(v_x_2310_, 1);
if (lean_obj_tag(v_tail_2313_) == 0)
{
lean_object* v_head_2314_; lean_object* v___x_2315_; 
lean_dec(v_x_2311_);
v_head_2314_ = lean_ctor_get(v_x_2310_, 0);
lean_inc(v_head_2314_);
lean_dec_ref_known(v_x_2310_, 2);
v___x_2315_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_2314_);
return v___x_2315_;
}
else
{
lean_object* v_head_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_inc(v_tail_2313_);
v_head_2316_ = lean_ctor_get(v_x_2310_, 0);
lean_inc(v_head_2316_);
lean_dec_ref_known(v_x_2310_, 2);
v___x_2317_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(v_head_2316_);
v___x_2318_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1_spec__7(v_x_2311_, v___x_2317_, v_tail_2313_);
return v___x_2318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(lean_object* v_xs_2319_){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; 
v___x_2320_ = lean_array_get_size(v_xs_2319_);
v___x_2321_ = lean_unsigned_to_nat(0u);
v___x_2322_ = lean_nat_dec_eq(v___x_2320_, v___x_2321_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2323_ = lean_array_to_list(v_xs_2319_);
v___x_2324_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2325_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_2323_, v___x_2324_);
v___x_2326_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2327_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
lean_ctor_set(v___x_2328_, 1, v___x_2325_);
v___x_2329_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2328_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
v___x_2331_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2326_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = l_Std_Format_fill(v___x_2331_);
return v___x_2332_;
}
else
{
lean_object* v___x_2333_; 
lean_dec_ref(v_xs_2319_);
v___x_2333_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2333_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__0));
v___x_2336_ = lean_string_length(v___x_2335_);
return v___x_2336_;
}
}
static lean_object* _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__9);
v___x_2338_ = lean_nat_to_int(v___x_2337_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_x_2344_){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2345_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__6));
v___x_2346_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_2347_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_x_2344_);
v___x_2348_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2346_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = 0;
v___x_2350_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set_uint8(v___x_2350_, sizeof(void*)*1, v___x_2349_);
v___x_2351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2345_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
v___x_2352_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_2353_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_2354_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
lean_ctor_set(v___x_2354_, 1, v___x_2351_);
v___x_2355_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_2356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2354_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
v___x_2357_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2352_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
lean_ctor_set_uint8(v___x_2358_, sizeof(void*)*1, v___x_2349_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(lean_object* v_x_2359_, lean_object* v_x_2360_, lean_object* v_x_2361_){
_start:
{
if (lean_obj_tag(v_x_2361_) == 0)
{
lean_dec(v_x_2359_);
return v_x_2360_;
}
else
{
lean_object* v_head_2362_; lean_object* v_tail_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2373_; 
v_head_2362_ = lean_ctor_get(v_x_2361_, 0);
v_tail_2363_ = lean_ctor_get(v_x_2361_, 1);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_x_2361_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2365_ = v_x_2361_;
v_isShared_2366_ = v_isSharedCheck_2373_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_tail_2363_);
lean_inc(v_head_2362_);
lean_dec(v_x_2361_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2373_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
lean_inc(v_x_2359_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set_tag(v___x_2365_, 5);
lean_ctor_set(v___x_2365_, 1, v_x_2359_);
lean_ctor_set(v___x_2365_, 0, v_x_2360_);
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_x_2360_);
lean_ctor_set(v_reuseFailAlloc_2372_, 1, v_x_2359_);
v___x_2368_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_2362_);
v___x_2370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2368_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v_x_2360_ = v___x_2370_;
v_x_2361_ = v_tail_2363_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(lean_object* v_x_2374_, lean_object* v_x_2375_, lean_object* v_x_2376_){
_start:
{
if (lean_obj_tag(v_x_2376_) == 0)
{
lean_dec(v_x_2374_);
return v_x_2375_;
}
else
{
lean_object* v_head_2377_; lean_object* v_tail_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2388_; 
v_head_2377_ = lean_ctor_get(v_x_2376_, 0);
v_tail_2378_ = lean_ctor_get(v_x_2376_, 1);
v_isSharedCheck_2388_ = !lean_is_exclusive(v_x_2376_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2380_ = v_x_2376_;
v_isShared_2381_ = v_isSharedCheck_2388_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_tail_2378_);
lean_inc(v_head_2377_);
lean_dec(v_x_2376_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2388_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
lean_inc(v_x_2374_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set_tag(v___x_2380_, 5);
lean_ctor_set(v___x_2380_, 1, v_x_2374_);
lean_ctor_set(v___x_2380_, 0, v_x_2375_);
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_x_2375_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v_x_2374_);
v___x_2383_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_2377_);
v___x_2385_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2383_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14_spec__22(v_x_2374_, v___x_2385_, v_tail_2378_);
return v___x_2386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(lean_object* v_x_2389_, lean_object* v_x_2390_){
_start:
{
if (lean_obj_tag(v_x_2389_) == 0)
{
lean_object* v___x_2391_; 
lean_dec(v_x_2390_);
v___x_2391_ = lean_box(0);
return v___x_2391_;
}
else
{
lean_object* v_tail_2392_; 
v_tail_2392_ = lean_ctor_get(v_x_2389_, 1);
if (lean_obj_tag(v_tail_2392_) == 0)
{
lean_object* v_head_2393_; lean_object* v___x_2394_; 
lean_dec(v_x_2390_);
v_head_2393_ = lean_ctor_get(v_x_2389_, 0);
lean_inc(v_head_2393_);
lean_dec_ref_known(v_x_2389_, 2);
v___x_2394_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_2393_);
return v___x_2394_;
}
else
{
lean_object* v_head_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
lean_inc(v_tail_2392_);
v_head_2395_ = lean_ctor_get(v_x_2389_, 0);
lean_inc(v_head_2395_);
lean_dec_ref_known(v_x_2389_, 2);
v___x_2396_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_head_2395_);
v___x_2397_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8_spec__14(v_x_2390_, v___x_2396_, v_tail_2392_);
return v___x_2397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(lean_object* v_xs_2398_){
_start:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; uint8_t v___x_2401_; 
v___x_2399_ = lean_array_get_size(v_xs_2398_);
v___x_2400_ = lean_unsigned_to_nat(0u);
v___x_2401_ = lean_nat_dec_eq(v___x_2399_, v___x_2400_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2402_ = lean_array_to_list(v_xs_2398_);
v___x_2403_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2404_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__8(v___x_2402_, v___x_2403_);
v___x_2405_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2406_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2407_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
lean_ctor_set(v___x_2407_, 1, v___x_2404_);
v___x_2408_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2405_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = l_Std_Format_fill(v___x_2410_);
return v___x_2411_;
}
else
{
lean_object* v___x_2412_; 
lean_dec_ref(v_xs_2398_);
v___x_2412_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2412_;
}
}
}
static lean_object* _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_unsigned_to_nat(0u);
v___x_2420_ = lean_nat_to_int(v___x_2419_);
return v___x_2420_;
}
}
static lean_object* _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = lean_unsigned_to_nat(8u);
v___x_2437_ = lean_nat_to_int(v___x_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_x_2441_){
_start:
{
lean_object* v_term_2442_; lean_object* v_desc_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2475_; 
v_term_2442_ = lean_ctor_get(v_x_2441_, 0);
v_desc_2443_ = lean_ctor_get(v_x_2441_, 1);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_x_2441_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2445_ = v_x_2441_;
v_isShared_2446_ = v_isSharedCheck_2475_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_desc_2443_);
lean_inc(v_term_2442_);
lean_dec(v_x_2441_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2475_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2447_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_2448_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__3));
v___x_2449_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_2450_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_term_2442_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set_tag(v___x_2445_, 4);
lean_ctor_set(v___x_2445_, 1, v___x_2450_);
lean_ctor_set(v___x_2445_, 0, v___x_2449_);
v___x_2452_ = v___x_2445_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
uint8_t v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2453_ = 0;
v___x_2454_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2454_, 0, v___x_2452_);
lean_ctor_set_uint8(v___x_2454_, sizeof(void*)*1, v___x_2453_);
v___x_2455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2448_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
v___x_2456_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_2457_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2455_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
v___x_2458_ = lean_box(1);
v___x_2459_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2457_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = ((lean_object*)(l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__6));
v___x_2461_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2459_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
lean_ctor_set(v___x_2462_, 1, v___x_2447_);
v___x_2463_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_desc_2443_);
v___x_2464_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2449_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
lean_ctor_set_uint8(v___x_2465_, sizeof(void*)*1, v___x_2453_);
v___x_2466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2462_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_2468_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_2469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
lean_ctor_set(v___x_2469_, 1, v___x_2466_);
v___x_2470_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_2471_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2469_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
v___x_2472_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2467_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
lean_ctor_set_uint8(v___x_2473_, sizeof(void*)*1, v___x_2453_);
return v___x_2473_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(lean_object* v_x_2476_, lean_object* v_x_2477_, lean_object* v_x_2478_){
_start:
{
if (lean_obj_tag(v_x_2478_) == 0)
{
lean_dec(v_x_2476_);
return v_x_2477_;
}
else
{
lean_object* v_head_2479_; lean_object* v_tail_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2490_; 
v_head_2479_ = lean_ctor_get(v_x_2478_, 0);
v_tail_2480_ = lean_ctor_get(v_x_2478_, 1);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_x_2478_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2482_ = v_x_2478_;
v_isShared_2483_ = v_isSharedCheck_2490_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_tail_2480_);
lean_inc(v_head_2479_);
lean_dec(v_x_2478_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2490_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
lean_inc(v_x_2476_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set_tag(v___x_2482_, 5);
lean_ctor_set(v___x_2482_, 1, v_x_2476_);
lean_ctor_set(v___x_2482_, 0, v_x_2477_);
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_x_2477_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_x_2476_);
v___x_2485_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_2479_);
v___x_2487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
v_x_2477_ = v___x_2487_;
v_x_2478_ = v_tail_2480_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(lean_object* v_x_2491_, lean_object* v_x_2492_, lean_object* v_x_2493_){
_start:
{
if (lean_obj_tag(v_x_2493_) == 0)
{
lean_dec(v_x_2491_);
return v_x_2492_;
}
else
{
lean_object* v_head_2494_; lean_object* v_tail_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2505_; 
v_head_2494_ = lean_ctor_get(v_x_2493_, 0);
v_tail_2495_ = lean_ctor_get(v_x_2493_, 1);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_x_2493_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2497_ = v_x_2493_;
v_isShared_2498_ = v_isSharedCheck_2505_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_tail_2495_);
lean_inc(v_head_2494_);
lean_dec(v_x_2493_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2505_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
lean_inc(v_x_2491_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set_tag(v___x_2497_, 5);
lean_ctor_set(v___x_2497_, 1, v_x_2491_);
lean_ctor_set(v___x_2497_, 0, v_x_2492_);
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_x_2492_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v_x_2491_);
v___x_2500_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2501_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_2494_);
v___x_2502_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2500_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
v___x_2503_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18_spec__26(v_x_2491_, v___x_2502_, v_tail_2495_);
return v___x_2503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(lean_object* v_x_2506_, lean_object* v_x_2507_){
_start:
{
if (lean_obj_tag(v_x_2506_) == 0)
{
lean_object* v___x_2508_; 
lean_dec(v_x_2507_);
v___x_2508_ = lean_box(0);
return v___x_2508_;
}
else
{
lean_object* v_tail_2509_; 
v_tail_2509_ = lean_ctor_get(v_x_2506_, 1);
if (lean_obj_tag(v_tail_2509_) == 0)
{
lean_object* v_head_2510_; lean_object* v___x_2511_; 
lean_dec(v_x_2507_);
v_head_2510_ = lean_ctor_get(v_x_2506_, 0);
lean_inc(v_head_2510_);
lean_dec_ref_known(v_x_2506_, 2);
v___x_2511_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_2510_);
return v___x_2511_;
}
else
{
lean_object* v_head_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
lean_inc(v_tail_2509_);
v_head_2512_ = lean_ctor_get(v_x_2506_, 0);
lean_inc(v_head_2512_);
lean_dec_ref_known(v_x_2506_, 2);
v___x_2513_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_head_2512_);
v___x_2514_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11_spec__18(v_x_2507_, v___x_2513_, v_tail_2509_);
return v___x_2514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(lean_object* v_xs_2515_){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2516_ = lean_array_get_size(v_xs_2515_);
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = lean_nat_dec_eq(v___x_2516_, v___x_2517_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2519_ = lean_array_to_list(v_xs_2515_);
v___x_2520_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2521_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__11(v___x_2519_, v___x_2520_);
v___x_2522_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2523_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
lean_ctor_set(v___x_2524_, 1, v___x_2521_);
v___x_2525_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2524_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
v___x_2527_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2522_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = l_Std_Format_fill(v___x_2527_);
return v___x_2528_;
}
else
{
lean_object* v___x_2529_; 
lean_dec_ref(v_xs_2515_);
v___x_2529_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(lean_object* v_x_2548_, lean_object* v_prec_2549_){
_start:
{
switch(lean_obj_tag(v_x_2548_))
{
case 0:
{
lean_object* v_contents_2550_; lean_object* v___y_2552_; lean_object* v___x_2560_; uint8_t v___x_2561_; 
v_contents_2550_ = lean_ctor_get(v_x_2548_, 0);
lean_inc_ref(v_contents_2550_);
lean_dec_ref_known(v_x_2548_, 1);
v___x_2560_ = lean_unsigned_to_nat(1024u);
v___x_2561_ = lean_nat_dec_le(v___x_2560_, v_prec_2549_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2562_; 
v___x_2562_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2552_ = v___x_2562_;
goto v___jp_2551_;
}
else
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2552_ = v___x_2563_;
goto v___jp_2551_;
}
v___jp_2551_:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; uint8_t v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2553_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__2));
v___x_2554_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_contents_2550_);
v___x_2555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2553_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
lean_inc(v___y_2552_);
v___x_2556_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___y_2552_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = 0;
v___x_2558_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2558_, 0, v___x_2556_);
lean_ctor_set_uint8(v___x_2558_, sizeof(void*)*1, v___x_2557_);
v___x_2559_ = l_Repr_addAppParen(v___x_2558_, v_prec_2549_);
return v___x_2559_;
}
}
case 1:
{
lean_object* v_content_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2584_; 
v_content_2564_ = lean_ctor_get(v_x_2548_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_x_2548_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2566_ = v_x_2548_;
v_isShared_2567_ = v_isSharedCheck_2584_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_content_2564_);
lean_dec(v_x_2548_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2584_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___y_2569_; lean_object* v___x_2580_; uint8_t v___x_2581_; 
v___x_2580_ = lean_unsigned_to_nat(1024u);
v___x_2581_ = lean_nat_dec_le(v___x_2580_, v_prec_2549_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; 
v___x_2582_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2569_ = v___x_2582_;
goto v___jp_2568_;
}
else
{
lean_object* v___x_2583_; 
v___x_2583_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2569_ = v___x_2583_;
goto v___jp_2568_;
}
v___jp_2568_:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2573_; 
v___x_2570_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__5));
v___x_2571_ = l_String_quote(v_content_2564_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set_tag(v___x_2566_, 3);
lean_ctor_set(v___x_2566_, 0, v___x_2571_);
v___x_2573_ = v___x_2566_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2570_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
lean_inc(v___y_2569_);
v___x_2575_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___y_2569_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = 0;
v___x_2577_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2577_, 0, v___x_2575_);
lean_ctor_set_uint8(v___x_2577_, sizeof(void*)*1, v___x_2576_);
v___x_2578_ = l_Repr_addAppParen(v___x_2577_, v_prec_2549_);
return v___x_2578_;
}
}
}
}
case 2:
{
lean_object* v_items_2585_; lean_object* v___y_2587_; lean_object* v___x_2595_; uint8_t v___x_2596_; 
v_items_2585_ = lean_ctor_get(v_x_2548_, 0);
lean_inc_ref(v_items_2585_);
lean_dec_ref_known(v_x_2548_, 1);
v___x_2595_ = lean_unsigned_to_nat(1024u);
v___x_2596_ = lean_nat_dec_le(v___x_2595_, v_prec_2549_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; 
v___x_2597_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2587_ = v___x_2597_;
goto v___jp_2586_;
}
else
{
lean_object* v___x_2598_; 
v___x_2598_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2587_ = v___x_2598_;
goto v___jp_2586_;
}
v___jp_2586_:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2588_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__8));
v___x_2589_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_2585_);
v___x_2590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
lean_inc(v___y_2587_);
v___x_2591_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___y_2587_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
v___x_2592_ = 0;
v___x_2593_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2593_, 0, v___x_2591_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*1, v___x_2592_);
v___x_2594_ = l_Repr_addAppParen(v___x_2593_, v_prec_2549_);
return v___x_2594_;
}
}
case 3:
{
lean_object* v_start_2599_; lean_object* v_items_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2635_; 
v_start_2599_ = lean_ctor_get(v_x_2548_, 0);
v_items_2600_ = lean_ctor_get(v_x_2548_, 1);
v_isSharedCheck_2635_ = !lean_is_exclusive(v_x_2548_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2602_ = v_x_2548_;
v_isShared_2603_ = v_isSharedCheck_2635_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_items_2600_);
lean_inc(v_start_2599_);
lean_dec(v_x_2548_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2635_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2620_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2631_ = lean_unsigned_to_nat(1024u);
v___x_2632_ = lean_nat_dec_le(v___x_2631_, v_prec_2549_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; 
v___x_2633_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2620_ = v___x_2633_;
goto v___jp_2619_;
}
else
{
lean_object* v___x_2634_; 
v___x_2634_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2620_ = v___x_2634_;
goto v___jp_2619_;
}
v___jp_2604_:
{
lean_object* v___x_2610_; 
lean_inc(v___y_2606_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set_tag(v___x_2602_, 5);
lean_ctor_set(v___x_2602_, 1, v___y_2608_);
lean_ctor_set(v___x_2602_, 0, v___y_2606_);
v___x_2610_ = v___x_2602_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___y_2606_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v___y_2608_);
v___x_2610_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; uint8_t v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
lean_inc(v___y_2607_);
v___x_2611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
lean_ctor_set(v___x_2611_, 1, v___y_2607_);
v___x_2612_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3(v_items_2600_);
v___x_2613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2611_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
lean_inc(v___y_2605_);
v___x_2614_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___y_2605_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = 0;
v___x_2616_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2616_, 0, v___x_2614_);
lean_ctor_set_uint8(v___x_2616_, sizeof(void*)*1, v___x_2615_);
v___x_2617_ = l_Repr_addAppParen(v___x_2616_, v_prec_2549_);
return v___x_2617_;
}
}
v___jp_2619_:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2621_ = lean_box(1);
v___x_2622_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__11));
v___x_2623_ = lean_obj_once(&l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12, &l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12_once, _init_l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__12);
v___x_2624_ = lean_int_dec_lt(v_start_2599_, v___x_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = l_Int_repr(v_start_2599_);
lean_dec(v_start_2599_);
v___x_2626_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
v___y_2605_ = v___y_2620_;
v___y_2606_ = v___x_2622_;
v___y_2607_ = v___x_2621_;
v___y_2608_ = v___x_2626_;
goto v___jp_2604_;
}
else
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2627_ = lean_unsigned_to_nat(1024u);
v___x_2628_ = l_Int_repr(v_start_2599_);
lean_dec(v_start_2599_);
v___x_2629_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
v___x_2630_ = l_Repr_addAppParen(v___x_2629_, v___x_2627_);
v___y_2605_ = v___y_2620_;
v___y_2606_ = v___x_2622_;
v___y_2607_ = v___x_2621_;
v___y_2608_ = v___x_2630_;
goto v___jp_2604_;
}
}
}
}
case 4:
{
lean_object* v_items_2636_; lean_object* v___y_2638_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v_items_2636_ = lean_ctor_get(v_x_2548_, 0);
lean_inc_ref(v_items_2636_);
lean_dec_ref_known(v_x_2548_, 1);
v___x_2646_ = lean_unsigned_to_nat(1024u);
v___x_2647_ = lean_nat_dec_le(v___x_2646_, v_prec_2549_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; 
v___x_2648_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2638_ = v___x_2648_;
goto v___jp_2637_;
}
else
{
lean_object* v___x_2649_; 
v___x_2649_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2638_ = v___x_2649_;
goto v___jp_2637_;
}
v___jp_2637_:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2639_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__15));
v___x_2640_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4(v_items_2636_);
v___x_2641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2639_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
lean_inc(v___y_2638_);
v___x_2642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___y_2638_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
v___x_2643_ = 0;
v___x_2644_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2644_, 0, v___x_2642_);
lean_ctor_set_uint8(v___x_2644_, sizeof(void*)*1, v___x_2643_);
v___x_2645_ = l_Repr_addAppParen(v___x_2644_, v_prec_2549_);
return v___x_2645_;
}
}
case 5:
{
lean_object* v_items_2650_; lean_object* v___y_2652_; lean_object* v___x_2660_; uint8_t v___x_2661_; 
v_items_2650_ = lean_ctor_get(v_x_2548_, 0);
lean_inc_ref(v_items_2650_);
lean_dec_ref_known(v_x_2548_, 1);
v___x_2660_ = lean_unsigned_to_nat(1024u);
v___x_2661_ = lean_nat_dec_le(v___x_2660_, v_prec_2549_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; 
v___x_2662_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2652_ = v___x_2662_;
goto v___jp_2651_;
}
else
{
lean_object* v___x_2663_; 
v___x_2663_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2652_ = v___x_2663_;
goto v___jp_2651_;
}
v___jp_2651_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2653_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__18));
v___x_2654_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_items_2650_);
v___x_2655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2653_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
lean_inc(v___y_2652_);
v___x_2656_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___y_2652_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = 0;
v___x_2658_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2658_, 0, v___x_2656_);
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*1, v___x_2657_);
v___x_2659_ = l_Repr_addAppParen(v___x_2658_, v_prec_2549_);
return v___x_2659_;
}
}
case 6:
{
lean_object* v_content_2664_; lean_object* v___y_2666_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v_content_2664_ = lean_ctor_get(v_x_2548_, 0);
lean_inc_ref(v_content_2664_);
lean_dec_ref_known(v_x_2548_, 1);
v___x_2674_ = lean_unsigned_to_nat(1024u);
v___x_2675_ = lean_nat_dec_le(v___x_2674_, v_prec_2549_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2676_; 
v___x_2676_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2666_ = v___x_2676_;
goto v___jp_2665_;
}
else
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2666_ = v___x_2677_;
goto v___jp_2665_;
}
v___jp_2665_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2667_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__21));
v___x_2668_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_2664_);
v___x_2669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2667_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
lean_inc(v___y_2666_);
v___x_2670_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___y_2666_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = 0;
v___x_2672_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2672_, 0, v___x_2670_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*1, v___x_2671_);
v___x_2673_ = l_Repr_addAppParen(v___x_2672_, v_prec_2549_);
return v___x_2673_;
}
}
default: 
{
lean_object* v_container_2678_; lean_object* v_content_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2729_; 
v_container_2678_ = lean_ctor_get(v_x_2548_, 0);
v_content_2679_ = lean_ctor_get(v_x_2548_, 1);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_x_2548_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2681_ = v_x_2548_;
v_isShared_2682_ = v_isSharedCheck_2729_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_content_2679_);
lean_inc(v_container_2678_);
lean_dec(v_x_2548_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2729_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v___y_2699_; lean_object* v___x_2725_; uint8_t v___x_2726_; 
v___x_2725_ = lean_unsigned_to_nat(1024u);
v___x_2726_ = lean_nat_dec_le(v___x_2725_, v_prec_2549_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; 
v___x_2727_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___y_2699_ = v___x_2727_;
goto v___jp_2698_;
}
else
{
lean_object* v___x_2728_; 
v___x_2728_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__4);
v___y_2699_ = v___x_2728_;
goto v___jp_2698_;
}
v___jp_2683_:
{
lean_object* v___x_2689_; 
lean_inc(v___y_2684_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set_tag(v___x_2681_, 5);
lean_ctor_set(v___x_2681_, 1, v___y_2687_);
lean_ctor_set(v___x_2681_, 0, v___y_2684_);
v___x_2689_ = v___x_2681_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___y_2684_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___y_2687_);
v___x_2689_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
lean_inc(v___y_2686_);
v___x_2690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
lean_ctor_set(v___x_2690_, 1, v___y_2686_);
v___x_2691_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__5(v_content_2679_);
v___x_2692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2690_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
lean_inc(v___y_2685_);
v___x_2693_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___y_2685_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = 0;
v___x_2695_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set_uint8(v___x_2695_, sizeof(void*)*1, v___x_2694_);
v___x_2696_ = l_Repr_addAppParen(v___x_2695_, v_prec_2549_);
return v___x_2696_;
}
}
v___jp_2698_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = lean_box(1);
v___x_2701_ = ((lean_object*)(l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___closed__24));
if (lean_obj_tag(v_container_2678_) == 0)
{
lean_object* v_val_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; uint8_t v___x_2710_; lean_object* v___x_2711_; 
v_val_2702_ = lean_ctor_get(v_container_2678_, 0);
lean_inc(v_val_2702_);
lean_dec_ref_known(v_container_2678_, 1);
v___x_2703_ = ((lean_object*)(l_Lean_instReprElabBlock___lam__0___closed__3));
v___x_2704_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_val_2702_);
lean_dec(v_val_2702_);
v___x_2705_ = lean_unsigned_to_nat(0u);
v___x_2706_ = l_Lean_Name_reprPrec(v___x_2704_, v___x_2705_);
v___x_2707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2703_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = ((lean_object*)(l_Lean_instReprElabInline___lam__0___closed__7));
v___x_2709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = 0;
v___x_2711_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2711_, 0, v___x_2709_);
lean_ctor_set_uint8(v___x_2711_, sizeof(void*)*1, v___x_2710_);
v___y_2684_ = v___x_2701_;
v___y_2685_ = v___y_2699_;
v___y_2686_ = v___x_2700_;
v___y_2687_ = v___x_2711_;
goto v___jp_2683_;
}
else
{
lean_object* v_index_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2724_; 
v_index_2712_ = lean_ctor_get(v_container_2678_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v_container_2678_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2714_ = v_container_2678_;
v_isShared_2715_ = v_isSharedCheck_2724_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_index_2712_);
lean_dec(v_container_2678_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2724_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2716_ = ((lean_object*)(l_Lean_instReprElabBlock___lam__0___closed__6));
v___x_2717_ = l_Nat_reprFast(v_index_2712_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set_tag(v___x_2714_, 3);
lean_ctor_set(v___x_2714_, 0, v___x_2717_);
v___x_2719_ = v___x_2714_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2720_; uint8_t v___x_2721_; lean_object* v___x_2722_; 
v___x_2720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2716_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
v___x_2721_ = 0;
v___x_2722_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2722_, 0, v___x_2720_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*1, v___x_2721_);
v___y_2684_ = v___x_2701_;
v___y_2685_ = v___y_2699_;
v___y_2686_ = v___x_2700_;
v___y_2687_ = v___x_2722_;
goto v___jp_2683_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1___lam__0(lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = lean_unsigned_to_nat(0u);
v___x_2732_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v___y_2730_, v___x_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0___boxed(lean_object* v_x_2733_, lean_object* v_prec_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0(v_x_2733_, v_prec_2734_);
lean_dec(v_prec_2734_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(lean_object* v_xs_2736_){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
v___x_2737_ = lean_array_get_size(v_xs_2736_);
v___x_2738_ = lean_unsigned_to_nat(0u);
v___x_2739_ = lean_nat_dec_eq(v___x_2737_, v___x_2738_);
if (v___x_2739_ == 0)
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2740_ = lean_array_to_list(v_xs_2736_);
v___x_2741_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2742_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__1(v___x_2740_, v___x_2741_);
v___x_2743_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2744_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
lean_ctor_set(v___x_2745_, 1, v___x_2742_);
v___x_2746_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2745_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2743_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = l_Std_Format_fill(v___x_2748_);
return v___x_2749_;
}
else
{
lean_object* v___x_2750_; 
lean_dec_ref(v_xs_2736_);
v___x_2750_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(lean_object* v_x_2754_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = ((lean_object*)(l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___closed__1));
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg___boxed(lean_object* v_x_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_2756_);
lean_dec(v_x_2756_);
return v_res_2757_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = lean_unsigned_to_nat(9u);
v___x_2768_ = lean_nat_to_int(v___x_2767_);
return v___x_2768_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7(void){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = lean_unsigned_to_nat(15u);
v___x_2773_ = lean_nat_to_int(v___x_2772_);
return v___x_2773_;
}
}
static lean_object* _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12(void){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = lean_unsigned_to_nat(11u);
v___x_2781_ = lean_nat_to_int(v___x_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(lean_object* v_x_2785_, lean_object* v_x_2786_, lean_object* v_x_2787_){
_start:
{
if (lean_obj_tag(v_x_2787_) == 0)
{
lean_dec(v_x_2785_);
return v_x_2786_;
}
else
{
lean_object* v_head_2788_; lean_object* v_tail_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2799_; 
v_head_2788_ = lean_ctor_get(v_x_2787_, 0);
v_tail_2789_ = lean_ctor_get(v_x_2787_, 1);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_x_2787_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2791_ = v_x_2787_;
v_isShared_2792_ = v_isSharedCheck_2799_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_tail_2789_);
lean_inc(v_head_2788_);
lean_dec(v_x_2787_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2799_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
lean_inc(v_x_2785_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set_tag(v___x_2791_, 5);
lean_ctor_set(v___x_2791_, 1, v_x_2785_);
lean_ctor_set(v___x_2791_, 0, v_x_2786_);
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_x_2786_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_x_2785_);
v___x_2794_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2795_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_2788_);
v___x_2796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2794_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(v_x_2785_, v___x_2796_, v_tail_2789_);
return v___x_2797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(lean_object* v_x_2800_, lean_object* v_x_2801_){
_start:
{
if (lean_obj_tag(v_x_2800_) == 0)
{
lean_object* v___x_2802_; 
lean_dec(v_x_2801_);
v___x_2802_ = lean_box(0);
return v___x_2802_;
}
else
{
lean_object* v_tail_2803_; 
v_tail_2803_ = lean_ctor_get(v_x_2800_, 1);
if (lean_obj_tag(v_tail_2803_) == 0)
{
lean_object* v_head_2804_; lean_object* v___x_2805_; 
lean_dec(v_x_2801_);
v_head_2804_ = lean_ctor_get(v_x_2800_, 0);
lean_inc(v_head_2804_);
lean_dec_ref_known(v_x_2800_, 2);
v___x_2805_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_2804_);
return v___x_2805_;
}
else
{
lean_object* v_head_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
lean_inc(v_tail_2803_);
v_head_2806_ = lean_ctor_get(v_x_2800_, 0);
lean_inc(v_head_2806_);
lean_dec_ref_known(v_x_2800_, 2);
v___x_2807_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_2806_);
v___x_2808_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34(v_x_2801_, v___x_2807_, v_tail_2803_);
return v___x_2808_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(lean_object* v_xs_2809_){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; 
v___x_2810_ = lean_array_get_size(v_xs_2809_);
v___x_2811_ = lean_unsigned_to_nat(0u);
v___x_2812_ = lean_nat_dec_eq(v___x_2810_, v___x_2811_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2813_ = lean_array_to_list(v_xs_2809_);
v___x_2814_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2815_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31(v___x_2813_, v___x_2814_);
v___x_2816_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_2817_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_2818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
lean_ctor_set(v___x_2818_, 1, v___x_2815_);
v___x_2819_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_2820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2818_);
lean_ctor_set(v___x_2820_, 1, v___x_2819_);
v___x_2821_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2821_, 0, v___x_2816_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = l_Std_Format_fill(v___x_2821_);
return v___x_2822_;
}
else
{
lean_object* v___x_2823_; 
lean_dec_ref(v_xs_2809_);
v___x_2823_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_2823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(lean_object* v_x_2824_){
_start:
{
lean_object* v_title_2825_; lean_object* v_titleString_2826_; lean_object* v_metadata_2827_; lean_object* v_content_2828_; lean_object* v_subParts_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_title_2825_ = lean_ctor_get(v_x_2824_, 0);
lean_inc_ref(v_title_2825_);
v_titleString_2826_ = lean_ctor_get(v_x_2824_, 1);
lean_inc_ref(v_titleString_2826_);
v_metadata_2827_ = lean_ctor_get(v_x_2824_, 2);
lean_inc(v_metadata_2827_);
v_content_2828_ = lean_ctor_get(v_x_2824_, 3);
lean_inc_ref(v_content_2828_);
v_subParts_2829_ = lean_ctor_get(v_x_2824_, 4);
lean_inc_ref(v_subParts_2829_);
lean_dec_ref(v_x_2824_);
v___x_2830_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_2831_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__3));
v___x_2832_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__4);
v___x_2833_ = l_Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2(v_title_2825_);
v___x_2834_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2832_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
v___x_2835_ = 0;
v___x_2836_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2836_, 0, v___x_2834_);
lean_ctor_set_uint8(v___x_2836_, sizeof(void*)*1, v___x_2835_);
v___x_2837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2831_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_2839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2837_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = lean_box(1);
v___x_2841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2839_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__6));
v___x_2843_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2841_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
v___x_2844_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
lean_ctor_set(v___x_2844_, 1, v___x_2830_);
v___x_2845_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__7);
v___x_2846_ = l_String_quote(v_titleString_2826_);
v___x_2847_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
v___x_2848_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2845_);
lean_ctor_set(v___x_2848_, 1, v___x_2847_);
v___x_2849_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*1, v___x_2835_);
v___x_2850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2844_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
v___x_2851_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
lean_ctor_set(v___x_2851_, 1, v___x_2838_);
v___x_2852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
lean_ctor_set(v___x_2852_, 1, v___x_2840_);
v___x_2853_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__9));
v___x_2854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2852_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
lean_ctor_set(v___x_2855_, 1, v___x_2830_);
v___x_2856_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_2857_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_metadata_2827_);
lean_dec(v_metadata_2827_);
v___x_2858_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2856_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
v___x_2859_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
lean_ctor_set_uint8(v___x_2859_, sizeof(void*)*1, v___x_2835_);
v___x_2860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2855_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
v___x_2861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
lean_ctor_set(v___x_2861_, 1, v___x_2838_);
v___x_2862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
lean_ctor_set(v___x_2862_, 1, v___x_2840_);
v___x_2863_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__11));
v___x_2864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
lean_ctor_set(v___x_2865_, 1, v___x_2830_);
v___x_2866_ = lean_obj_once(&l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12, &l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12_once, _init_l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__12);
v___x_2867_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_content_2828_);
v___x_2868_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
lean_ctor_set_uint8(v___x_2869_, sizeof(void*)*1, v___x_2835_);
v___x_2870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2865_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
v___x_2871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
lean_ctor_set(v___x_2871_, 1, v___x_2838_);
v___x_2872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
lean_ctor_set(v___x_2872_, 1, v___x_2840_);
v___x_2873_ = ((lean_object*)(l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg___closed__14));
v___x_2874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2872_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2874_);
lean_ctor_set(v___x_2875_, 1, v___x_2830_);
v___x_2876_ = l_Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25(v_subParts_2829_);
v___x_2877_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2856_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
v___x_2878_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
lean_ctor_set_uint8(v___x_2878_, sizeof(void*)*1, v___x_2835_);
v___x_2879_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2875_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
v___x_2880_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_2881_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_2882_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v___x_2879_);
v___x_2883_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_2884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2882_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2885_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2880_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
v___x_2886_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
lean_ctor_set_uint8(v___x_2886_, sizeof(void*)*1, v___x_2835_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__25_spec__31_spec__34_spec__35(lean_object* v_x_2887_, lean_object* v_x_2888_, lean_object* v_x_2889_){
_start:
{
if (lean_obj_tag(v_x_2889_) == 0)
{
lean_dec(v_x_2887_);
return v_x_2888_;
}
else
{
lean_object* v_head_2890_; lean_object* v_tail_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2901_; 
v_head_2890_ = lean_ctor_get(v_x_2889_, 0);
v_tail_2891_ = lean_ctor_get(v_x_2889_, 1);
v_isSharedCheck_2901_ = !lean_is_exclusive(v_x_2889_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2893_ = v_x_2889_;
v_isShared_2894_ = v_isSharedCheck_2901_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_tail_2891_);
lean_inc(v_head_2890_);
lean_dec(v_x_2889_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2901_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
lean_inc(v_x_2887_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set_tag(v___x_2893_, 5);
lean_ctor_set(v___x_2893_, 1, v_x_2887_);
lean_ctor_set(v___x_2893_, 0, v_x_2888_);
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_x_2888_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_x_2887_);
v___x_2896_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2897_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_head_2890_);
v___x_2898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2896_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
v_x_2888_ = v___x_2898_;
v_x_2889_ = v_tail_2891_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(lean_object* v_x_2902_, lean_object* v_x_2903_){
_start:
{
lean_object* v_fst_2904_; lean_object* v_snd_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2915_; 
v_fst_2904_ = lean_ctor_get(v_x_2902_, 0);
v_snd_2905_ = lean_ctor_get(v_x_2902_, 1);
v_isSharedCheck_2915_ = !lean_is_exclusive(v_x_2902_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2907_ = v_x_2902_;
v_isShared_2908_ = v_isSharedCheck_2915_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_snd_2905_);
lean_inc(v_fst_2904_);
lean_dec(v_x_2902_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2915_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; lean_object* v___x_2911_; 
v___x_2909_ = l_Lean_instReprDeclarationRange_repr___redArg(v_fst_2904_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set_tag(v___x_2907_, 1);
lean_ctor_set(v___x_2907_, 1, v_x_2903_);
lean_ctor_set(v___x_2907_, 0, v___x_2909_);
v___x_2911_ = v___x_2907_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v_x_2903_);
v___x_2911_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_snd_2905_);
v___x_2913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
lean_ctor_set(v___x_2913_, 1, v___x_2911_);
return v___x_2913_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(lean_object* v_x_2916_, lean_object* v_x_2917_, lean_object* v_x_2918_){
_start:
{
if (lean_obj_tag(v_x_2918_) == 0)
{
lean_dec(v_x_2916_);
return v_x_2917_;
}
else
{
lean_object* v_head_2919_; lean_object* v_tail_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2929_; 
v_head_2919_ = lean_ctor_get(v_x_2918_, 0);
v_tail_2920_ = lean_ctor_get(v_x_2918_, 1);
v_isSharedCheck_2929_ = !lean_is_exclusive(v_x_2918_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2922_ = v_x_2918_;
v_isShared_2923_ = v_isSharedCheck_2929_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_tail_2920_);
lean_inc(v_head_2919_);
lean_dec(v_x_2918_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2929_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
lean_inc(v_x_2916_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set_tag(v___x_2922_, 5);
lean_ctor_set(v___x_2922_, 1, v_x_2916_);
lean_ctor_set(v___x_2922_, 0, v_x_2917_);
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_x_2917_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_x_2916_);
v___x_2925_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_object* v___x_2926_; 
v___x_2926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
lean_ctor_set(v___x_2926_, 1, v_head_2919_);
v_x_2917_ = v___x_2926_;
v_x_2918_ = v_tail_2920_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(lean_object* v_x_2930_, lean_object* v_x_2931_){
_start:
{
if (lean_obj_tag(v_x_2930_) == 0)
{
lean_object* v___x_2932_; 
lean_dec(v_x_2931_);
v___x_2932_ = lean_box(0);
return v___x_2932_;
}
else
{
lean_object* v_tail_2933_; 
v_tail_2933_ = lean_ctor_get(v_x_2930_, 1);
if (lean_obj_tag(v_tail_2933_) == 0)
{
lean_object* v_head_2934_; 
lean_dec(v_x_2931_);
v_head_2934_ = lean_ctor_get(v_x_2930_, 0);
lean_inc(v_head_2934_);
lean_dec_ref_known(v_x_2930_, 2);
return v_head_2934_;
}
else
{
lean_object* v_head_2935_; lean_object* v___x_2936_; 
lean_inc(v_tail_2933_);
v_head_2935_ = lean_ctor_get(v_x_2930_, 0);
lean_inc(v_head_2935_);
lean_dec_ref_known(v_x_2930_, 2);
v___x_2936_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11_spec__20(v_x_2931_, v_head_2935_, v_tail_2933_);
return v___x_2936_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__0));
v___x_2940_ = lean_string_length(v___x_2939_);
return v___x_2940_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__2);
v___x_2942_ = lean_nat_to_int(v___x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(lean_object* v_x_2947_){
_start:
{
lean_object* v_fst_2948_; lean_object* v_snd_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2971_; 
v_fst_2948_ = lean_ctor_get(v_x_2947_, 0);
v_snd_2949_ = lean_ctor_get(v_x_2947_, 1);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_x_2947_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2951_ = v_x_2947_;
v_isShared_2952_ = v_isSharedCheck_2971_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_snd_2949_);
lean_inc(v_fst_2948_);
lean_dec(v_x_2947_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2971_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2957_; 
v___x_2953_ = l_Nat_reprFast(v_fst_2948_);
v___x_2954_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
v___x_2955_ = lean_box(0);
if (v_isShared_2952_ == 0)
{
lean_ctor_set_tag(v___x_2951_, 1);
lean_ctor_set(v___x_2951_, 1, v___x_2955_);
lean_ctor_set(v___x_2951_, 0, v___x_2954_);
v___x_2957_ = v___x_2951_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2954_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; uint8_t v___x_2968_; lean_object* v___x_2969_; 
v___x_2958_ = l_Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10(v_snd_2949_, v___x_2957_);
v___x_2959_ = l_List_reverse___redArg(v___x_2958_);
v___x_2960_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_2961_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__11(v___x_2959_, v___x_2960_);
v___x_2962_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3, &l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3_once, _init_l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__3);
v___x_2963_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__4));
v___x_2964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
lean_ctor_set(v___x_2964_, 1, v___x_2961_);
v___x_2965_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__5));
v___x_2966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2964_);
lean_ctor_set(v___x_2966_, 1, v___x_2965_);
v___x_2967_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2962_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
v___x_2968_ = 0;
v___x_2969_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2969_, 0, v___x_2967_);
lean_ctor_set_uint8(v___x_2969_, sizeof(void*)*1, v___x_2968_);
return v___x_2969_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(lean_object* v_x_2972_, lean_object* v_x_2973_, lean_object* v_x_2974_){
_start:
{
if (lean_obj_tag(v_x_2974_) == 0)
{
lean_dec(v_x_2972_);
return v_x_2973_;
}
else
{
lean_object* v_head_2975_; lean_object* v_tail_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2986_; 
v_head_2975_ = lean_ctor_get(v_x_2974_, 0);
v_tail_2976_ = lean_ctor_get(v_x_2974_, 1);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_x_2974_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2978_ = v_x_2974_;
v_isShared_2979_ = v_isSharedCheck_2986_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_tail_2976_);
lean_inc(v_head_2975_);
lean_dec(v_x_2974_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2986_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
lean_inc(v_x_2972_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set_tag(v___x_2978_, 5);
lean_ctor_set(v___x_2978_, 1, v_x_2972_);
lean_ctor_set(v___x_2978_, 0, v_x_2973_);
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_x_2973_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_x_2972_);
v___x_2981_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_2975_);
v___x_2983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2981_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
v_x_2973_ = v___x_2983_;
v_x_2974_ = v_tail_2976_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(lean_object* v_x_2987_, lean_object* v_x_2988_, lean_object* v_x_2989_){
_start:
{
if (lean_obj_tag(v_x_2989_) == 0)
{
lean_dec(v_x_2987_);
return v_x_2988_;
}
else
{
lean_object* v_head_2990_; lean_object* v_tail_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3001_; 
v_head_2990_ = lean_ctor_get(v_x_2989_, 0);
v_tail_2991_ = lean_ctor_get(v_x_2989_, 1);
v_isSharedCheck_3001_ = !lean_is_exclusive(v_x_2989_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2993_ = v_x_2989_;
v_isShared_2994_ = v_isSharedCheck_3001_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_tail_2991_);
lean_inc(v_head_2990_);
lean_dec(v_x_2989_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3001_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
lean_inc(v_x_2987_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set_tag(v___x_2993_, 5);
lean_ctor_set(v___x_2993_, 1, v_x_2987_);
lean_ctor_set(v___x_2993_, 0, v_x_2988_);
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_x_2988_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v_x_2987_);
v___x_2996_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2997_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_2990_);
v___x_2998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2996_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
v___x_2999_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13_spec__23(v_x_2987_, v___x_2998_, v_tail_2991_);
return v___x_2999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(lean_object* v_x_3002_, lean_object* v_x_3003_){
_start:
{
if (lean_obj_tag(v_x_3002_) == 0)
{
lean_object* v___x_3004_; 
lean_dec(v_x_3003_);
v___x_3004_ = lean_box(0);
return v___x_3004_;
}
else
{
lean_object* v_tail_3005_; 
v_tail_3005_ = lean_ctor_get(v_x_3002_, 1);
if (lean_obj_tag(v_tail_3005_) == 0)
{
lean_object* v_head_3006_; lean_object* v___x_3007_; 
lean_dec(v_x_3003_);
v_head_3006_ = lean_ctor_get(v_x_3002_, 0);
lean_inc(v_head_3006_);
lean_dec_ref_known(v_x_3002_, 2);
v___x_3007_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3006_);
return v___x_3007_;
}
else
{
lean_object* v_head_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
lean_inc(v_tail_3005_);
v_head_3008_ = lean_ctor_get(v_x_3002_, 0);
lean_inc(v_head_3008_);
lean_dec_ref_known(v_x_3002_, 2);
v___x_3009_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_head_3008_);
v___x_3010_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4_spec__13(v_x_3003_, v___x_3009_, v_tail_3005_);
return v___x_3010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(lean_object* v_xs_3011_){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v___x_3012_ = lean_array_get_size(v_xs_3011_);
v___x_3013_ = lean_unsigned_to_nat(0u);
v___x_3014_ = lean_nat_dec_eq(v___x_3012_, v___x_3013_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3015_ = lean_array_to_list(v_xs_3011_);
v___x_3016_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__3));
v___x_3017_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__4(v___x_3015_, v___x_3016_);
v___x_3018_ = lean_obj_once(&l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6, &l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6_once, _init_l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__6);
v___x_3019_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__7));
v___x_3020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
lean_ctor_set(v___x_3020_, 1, v___x_3017_);
v___x_3021_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__8));
v___x_3022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3020_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___x_3023_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3018_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
v___x_3024_ = l_Std_Format_fill(v___x_3023_);
return v___x_3024_;
}
else
{
lean_object* v___x_3025_; 
lean_dec_ref(v_xs_3011_);
v___x_3025_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__10));
return v___x_3025_;
}
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = lean_unsigned_to_nat(20u);
v___x_3042_ = lean_nat_to_int(v___x_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(lean_object* v_x_3043_){
_start:
{
lean_object* v_text_3044_; lean_object* v_sections_3045_; lean_object* v_declarationRange_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; uint8_t v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v_text_3044_ = lean_ctor_get(v_x_3043_, 0);
lean_inc_ref(v_text_3044_);
v_sections_3045_ = lean_ctor_get(v_x_3043_, 1);
lean_inc_ref(v_sections_3045_);
v_declarationRange_3046_ = lean_ctor_get(v_x_3043_, 2);
lean_inc_ref(v_declarationRange_3046_);
lean_dec_ref(v_x_3043_);
v___x_3047_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__5));
v___x_3048_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__3));
v___x_3049_ = lean_obj_once(&l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4, &l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4_once, _init_l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg___closed__4);
v___x_3050_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0(v_text_3044_);
v___x_3051_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3049_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
v___x_3052_ = 0;
v___x_3053_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3053_, 0, v___x_3051_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*1, v___x_3052_);
v___x_3054_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3048_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = ((lean_object*)(l_Array_repr___at___00Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4_spec__8___closed__2));
v___x_3056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3054_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
v___x_3057_ = lean_box(1);
v___x_3058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3056_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
v___x_3059_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__5));
v___x_3060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3058_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
v___x_3061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3060_);
lean_ctor_set(v___x_3061_, 1, v___x_3047_);
v___x_3062_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__7);
v___x_3063_ = l_Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1(v_sections_3045_);
v___x_3064_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3062_);
lean_ctor_set(v___x_3064_, 1, v___x_3063_);
v___x_3065_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
lean_ctor_set_uint8(v___x_3065_, sizeof(void*)*1, v___x_3052_);
v___x_3066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3061_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
lean_ctor_set(v___x_3067_, 1, v___x_3055_);
v___x_3068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
lean_ctor_set(v___x_3068_, 1, v___x_3057_);
v___x_3069_ = ((lean_object*)(l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__7));
v___x_3070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3068_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
lean_ctor_set(v___x_3071_, 1, v___x_3047_);
v___x_3072_ = lean_obj_once(&l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8, &l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8_once, _init_l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg___closed__8);
v___x_3073_ = l_Lean_instReprDeclarationRange_repr___redArg(v_declarationRange_3046_);
v___x_3074_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3072_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
v___x_3075_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set_uint8(v___x_3075_, sizeof(void*)*1, v___x_3052_);
v___x_3076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3071_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v___x_3077_ = lean_obj_once(&l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10, &l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10_once, _init_l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__10);
v___x_3078_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
lean_ctor_set(v___x_3079_, 1, v___x_3076_);
v___x_3080_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3079_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___x_3082_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3077_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
v___x_3083_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
lean_ctor_set_uint8(v___x_3083_, sizeof(void*)*1, v___x_3052_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr(lean_object* v_x_3084_, lean_object* v_prec_3085_){
_start:
{
lean_object* v___x_3086_; 
v___x_3086_ = l_Lean_VersoModuleDocs_instReprSnippet_repr___redArg(v_x_3084_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_instReprSnippet_repr___boxed(lean_object* v_x_3087_, lean_object* v_prec_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Lean_VersoModuleDocs_instReprSnippet_repr(v_x_3087_, v_prec_3088_);
lean_dec(v_prec_3088_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(lean_object* v_x_3090_, lean_object* v_x_3091_){
_start:
{
lean_object* v___x_3092_; 
v___x_3092_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg(v_x_3090_);
return v___x_3092_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___boxed(lean_object* v_x_3093_, lean_object* v_x_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3(v_x_3093_, v_x_3094_);
lean_dec(v_x_3094_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_3096_, lean_object* v_prec_3097_){
_start:
{
lean_object* v___x_3098_; 
v___x_3098_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg(v_x_3096_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* v_x_3099_, lean_object* v_prec_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7(v_x_3099_, v_prec_3100_);
lean_dec(v_prec_3100_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(lean_object* v_x_3102_, lean_object* v_prec_3103_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___redArg(v_x_3102_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10___boxed(lean_object* v_x_3105_, lean_object* v_prec_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_Doc_instReprDescItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__4_spec__10(v_x_3105_, v_prec_3106_);
lean_dec(v_prec_3106_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(lean_object* v_x_3108_, lean_object* v_x_3109_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___redArg(v_x_3108_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24___boxed(lean_object* v_x_3111_, lean_object* v_x_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Option_repr___at___00Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18_spec__24(v_x_3111_, v_x_3112_);
lean_dec(v_x_3112_);
lean_dec(v_x_3111_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(lean_object* v_x_3114_, lean_object* v_prec_3115_){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___redArg(v_x_3114_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18___boxed(lean_object* v_x_3117_, lean_object* v_prec_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l_Lean_Doc_instReprPart_repr___at___00Prod_reprTuple___at___00Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3_spec__10_spec__18(v_x_3117_, v_prec_3118_);
lean_dec(v_prec_3118_);
return v_res_3119_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_Snippet_canNestIn(lean_object* v_level_3122_, lean_object* v_snippet_3123_){
_start:
{
lean_object* v_sections_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; uint8_t v___x_3127_; 
v_sections_3124_ = lean_ctor_get(v_snippet_3123_, 1);
v___x_3125_ = lean_unsigned_to_nat(0u);
v___x_3126_ = lean_array_get_size(v_sections_3124_);
v___x_3127_ = lean_nat_dec_lt(v___x_3125_, v___x_3126_);
if (v___x_3127_ == 0)
{
uint8_t v___x_3128_; 
v___x_3128_ = 1;
return v___x_3128_;
}
else
{
lean_object* v___x_3129_; lean_object* v_fst_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; uint8_t v___x_3133_; 
v___x_3129_ = lean_array_fget_borrowed(v_sections_3124_, v___x_3125_);
v_fst_3130_ = lean_ctor_get(v___x_3129_, 0);
v___x_3131_ = lean_unsigned_to_nat(1u);
v___x_3132_ = lean_nat_add(v_level_3122_, v___x_3131_);
v___x_3133_ = lean_nat_dec_le(v_fst_3130_, v___x_3132_);
lean_dec(v___x_3132_);
return v___x_3133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_canNestIn___boxed(lean_object* v_level_3134_, lean_object* v_snippet_3135_){
_start:
{
uint8_t v_res_3136_; lean_object* v_r_3137_; 
v_res_3136_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_level_3134_, v_snippet_3135_);
lean_dec_ref(v_snippet_3135_);
lean_dec(v_level_3134_);
v_r_3137_ = lean_box(v_res_3136_);
return v_r_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting(lean_object* v_snippet_3138_){
_start:
{
lean_object* v_sections_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; uint8_t v___x_3143_; 
v_sections_3139_ = lean_ctor_get(v_snippet_3138_, 1);
v___x_3140_ = lean_array_get_size(v_sections_3139_);
v___x_3141_ = lean_unsigned_to_nat(1u);
v___x_3142_ = lean_nat_sub(v___x_3140_, v___x_3141_);
v___x_3143_ = lean_nat_dec_lt(v___x_3142_, v___x_3140_);
if (v___x_3143_ == 0)
{
lean_object* v___x_3144_; 
lean_dec(v___x_3142_);
v___x_3144_ = lean_box(0);
return v___x_3144_;
}
else
{
lean_object* v___x_3145_; lean_object* v_fst_3146_; lean_object* v___x_3147_; 
v___x_3145_ = lean_array_fget_borrowed(v_sections_3139_, v___x_3142_);
lean_dec(v___x_3142_);
v_fst_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_fst_3146_);
v___x_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3147_, 0, v_fst_3146_);
return v___x_3147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_terminalNesting___boxed(lean_object* v_snippet_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v_snippet_3148_);
lean_dec_ref(v_snippet_3148_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addBlock(lean_object* v_snippet_3150_, lean_object* v_block_3151_){
_start:
{
lean_object* v_text_3152_; lean_object* v_sections_3153_; lean_object* v_declarationRange_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; uint8_t v___x_3157_; 
v_text_3152_ = lean_ctor_get(v_snippet_3150_, 0);
v_sections_3153_ = lean_ctor_get(v_snippet_3150_, 1);
v_declarationRange_3154_ = lean_ctor_get(v_snippet_3150_, 2);
v___x_3155_ = lean_array_get_size(v_sections_3153_);
v___x_3156_ = lean_unsigned_to_nat(0u);
v___x_3157_ = lean_nat_dec_eq(v___x_3155_, v___x_3156_);
if (v___x_3157_ == 0)
{
lean_object* v___x_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; 
v___x_3158_ = lean_unsigned_to_nat(1u);
v___x_3159_ = lean_nat_sub(v___x_3155_, v___x_3158_);
v___x_3160_ = lean_nat_dec_lt(v___x_3159_, v___x_3155_);
if (v___x_3160_ == 0)
{
lean_dec(v___x_3159_);
lean_dec_ref(v_block_3151_);
return v_snippet_3150_;
}
else
{
lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3204_; 
lean_inc_ref(v_declarationRange_3154_);
lean_inc_ref(v_sections_3153_);
lean_inc_ref(v_text_3152_);
v_isSharedCheck_3204_ = !lean_is_exclusive(v_snippet_3150_);
if (v_isSharedCheck_3204_ == 0)
{
lean_object* v_unused_3205_; lean_object* v_unused_3206_; lean_object* v_unused_3207_; 
v_unused_3205_ = lean_ctor_get(v_snippet_3150_, 2);
lean_dec(v_unused_3205_);
v_unused_3206_ = lean_ctor_get(v_snippet_3150_, 1);
lean_dec(v_unused_3206_);
v_unused_3207_ = lean_ctor_get(v_snippet_3150_, 0);
lean_dec(v_unused_3207_);
v___x_3162_ = v_snippet_3150_;
v_isShared_3163_ = v_isSharedCheck_3204_;
goto v_resetjp_3161_;
}
else
{
lean_dec(v_snippet_3150_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3204_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v_v_3164_; lean_object* v_snd_3165_; lean_object* v_snd_3166_; lean_object* v_fst_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3202_; 
v_v_3164_ = lean_array_fget(v_sections_3153_, v___x_3159_);
v_snd_3165_ = lean_ctor_get(v_v_3164_, 1);
lean_inc(v_snd_3165_);
v_snd_3166_ = lean_ctor_get(v_snd_3165_, 1);
lean_inc(v_snd_3166_);
v_fst_3167_ = lean_ctor_get(v_v_3164_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v_v_3164_);
if (v_isSharedCheck_3202_ == 0)
{
lean_object* v_unused_3203_; 
v_unused_3203_ = lean_ctor_get(v_v_3164_, 1);
lean_dec(v_unused_3203_);
v___x_3169_ = v_v_3164_;
v_isShared_3170_ = v_isSharedCheck_3202_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_fst_3167_);
lean_dec(v_v_3164_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3202_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v_fst_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3200_; 
v_fst_3171_ = lean_ctor_get(v_snd_3165_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_snd_3165_);
if (v_isSharedCheck_3200_ == 0)
{
lean_object* v_unused_3201_; 
v_unused_3201_ = lean_ctor_get(v_snd_3165_, 1);
lean_dec(v_unused_3201_);
v___x_3173_ = v_snd_3165_;
v_isShared_3174_ = v_isSharedCheck_3200_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_fst_3171_);
lean_dec(v_snd_3165_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3200_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v_title_3175_; lean_object* v_titleString_3176_; lean_object* v_metadata_3177_; lean_object* v_content_3178_; lean_object* v_subParts_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3199_; 
v_title_3175_ = lean_ctor_get(v_snd_3166_, 0);
v_titleString_3176_ = lean_ctor_get(v_snd_3166_, 1);
v_metadata_3177_ = lean_ctor_get(v_snd_3166_, 2);
v_content_3178_ = lean_ctor_get(v_snd_3166_, 3);
v_subParts_3179_ = lean_ctor_get(v_snd_3166_, 4);
v_isSharedCheck_3199_ = !lean_is_exclusive(v_snd_3166_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3181_ = v_snd_3166_;
v_isShared_3182_ = v_isSharedCheck_3199_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_subParts_3179_);
lean_inc(v_content_3178_);
lean_inc(v_metadata_3177_);
lean_inc(v_titleString_3176_);
lean_inc(v_title_3175_);
lean_dec(v_snd_3166_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3199_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3183_; lean_object* v_xs_x27_3184_; lean_object* v___x_3185_; lean_object* v___x_3187_; 
v___x_3183_ = lean_box(0);
v_xs_x27_3184_ = lean_array_fset(v_sections_3153_, v___x_3159_, v___x_3183_);
v___x_3185_ = lean_array_push(v_content_3178_, v_block_3151_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 3, v___x_3185_);
v___x_3187_ = v___x_3181_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_title_3175_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_titleString_3176_);
lean_ctor_set(v_reuseFailAlloc_3198_, 2, v_metadata_3177_);
lean_ctor_set(v_reuseFailAlloc_3198_, 3, v___x_3185_);
lean_ctor_set(v_reuseFailAlloc_3198_, 4, v_subParts_3179_);
v___x_3187_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3189_; 
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 1, v___x_3187_);
v___x_3189_ = v___x_3173_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_fst_3171_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3191_; 
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 1, v___x_3189_);
v___x_3191_ = v___x_3169_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_fst_3167_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v___x_3189_);
v___x_3191_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3192_; lean_object* v___x_3194_; 
v___x_3192_ = lean_array_fset(v_xs_x27_3184_, v___x_3159_, v___x_3191_);
lean_dec(v___x_3159_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 1, v___x_3192_);
v___x_3194_ = v___x_3162_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_text_3152_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v___x_3192_);
lean_ctor_set(v_reuseFailAlloc_3195_, 2, v_declarationRange_3154_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
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
lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3215_; 
lean_inc_ref(v_declarationRange_3154_);
lean_inc_ref(v_sections_3153_);
lean_inc_ref(v_text_3152_);
v_isSharedCheck_3215_ = !lean_is_exclusive(v_snippet_3150_);
if (v_isSharedCheck_3215_ == 0)
{
lean_object* v_unused_3216_; lean_object* v_unused_3217_; lean_object* v_unused_3218_; 
v_unused_3216_ = lean_ctor_get(v_snippet_3150_, 2);
lean_dec(v_unused_3216_);
v_unused_3217_ = lean_ctor_get(v_snippet_3150_, 1);
lean_dec(v_unused_3217_);
v_unused_3218_ = lean_ctor_get(v_snippet_3150_, 0);
lean_dec(v_unused_3218_);
v___x_3209_ = v_snippet_3150_;
v_isShared_3210_ = v_isSharedCheck_3215_;
goto v_resetjp_3208_;
}
else
{
lean_dec(v_snippet_3150_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3215_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3211_; lean_object* v___x_3213_; 
v___x_3211_ = lean_array_push(v_text_3152_, v_block_3151_);
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 0, v___x_3211_);
v___x_3213_ = v___x_3209_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_sections_3153_);
lean_ctor_set(v_reuseFailAlloc_3214_, 2, v_declarationRange_3154_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_Snippet_addPart(lean_object* v_snippet_3219_, lean_object* v_level_3220_, lean_object* v_range_3221_, lean_object* v_part_3222_){
_start:
{
lean_object* v_text_3223_; lean_object* v_sections_3224_; lean_object* v_declarationRange_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3235_; 
v_text_3223_ = lean_ctor_get(v_snippet_3219_, 0);
v_sections_3224_ = lean_ctor_get(v_snippet_3219_, 1);
v_declarationRange_3225_ = lean_ctor_get(v_snippet_3219_, 2);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_snippet_3219_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3227_ = v_snippet_3219_;
v_isShared_3228_ = v_isSharedCheck_3235_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_declarationRange_3225_);
lean_inc(v_sections_3224_);
lean_inc(v_text_3223_);
lean_dec(v_snippet_3219_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3235_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3233_; 
v___x_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3229_, 0, v_range_3221_);
lean_ctor_set(v___x_3229_, 1, v_part_3222_);
v___x_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3230_, 0, v_level_3220_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___x_3231_ = lean_array_push(v_sections_3224_, v___x_3230_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 1, v___x_3231_);
v___x_3233_ = v___x_3227_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_text_3223_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v___x_3231_);
lean_ctor_set(v_reuseFailAlloc_3234_, 2, v_declarationRange_3225_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0(void){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3236_ = lean_unsigned_to_nat(32u);
v___x_3237_ = lean_mk_empty_array_with_capacity(v___x_3236_);
v___x_3238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
return v___x_3238_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1(void){
_start:
{
size_t v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3239_ = ((size_t)5ULL);
v___x_3240_ = lean_unsigned_to_nat(0u);
v___x_3241_ = lean_unsigned_to_nat(32u);
v___x_3242_ = lean_mk_empty_array_with_capacity(v___x_3241_);
v___x_3243_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_3244_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
lean_ctor_set(v___x_3244_, 1, v___x_3242_);
lean_ctor_set(v___x_3244_, 2, v___x_3240_);
lean_ctor_set(v___x_3244_, 3, v___x_3240_);
lean_ctor_set_usize(v___x_3244_, 4, v___x_3239_);
return v___x_3244_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs_default(void){
_start:
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__1, &l_Lean_instInhabitedVersoModuleDocs_default___closed__1_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__1);
return v___x_3245_;
}
}
static lean_object* _init_l_Lean_instInhabitedVersoModuleDocs(void){
_start:
{
lean_object* v___x_3246_; 
v___x_3246_ = l_Lean_instInhabitedVersoModuleDocs_default;
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(lean_object* v_as_3247_, lean_object* v_i_3248_){
_start:
{
lean_object* v_zero_3249_; uint8_t v_isZero_3250_; 
v_zero_3249_ = lean_unsigned_to_nat(0u);
v_isZero_3250_ = lean_nat_dec_eq(v_i_3248_, v_zero_3249_);
if (v_isZero_3250_ == 1)
{
lean_object* v___x_3251_; 
lean_dec(v_i_3248_);
v___x_3251_ = lean_box(0);
return v___x_3251_;
}
else
{
lean_object* v_one_3252_; lean_object* v_n_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v_one_3252_ = lean_unsigned_to_nat(1u);
v_n_3253_ = lean_nat_sub(v_i_3248_, v_one_3252_);
lean_dec(v_i_3248_);
v___x_3254_ = lean_array_fget_borrowed(v_as_3247_, v_n_3253_);
v___x_3255_ = l_Lean_VersoModuleDocs_Snippet_terminalNesting(v___x_3254_);
if (lean_obj_tag(v___x_3255_) == 0)
{
v_i_3248_ = v_n_3253_;
goto _start;
}
else
{
lean_dec(v_n_3253_);
return v___x_3255_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg___boxed(lean_object* v_as_3257_, lean_object* v_i_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_as_3257_, v_i_3258_);
lean_dec_ref(v_as_3257_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(lean_object* v_as_3260_, lean_object* v_i_3261_){
_start:
{
lean_object* v_zero_3262_; uint8_t v_isZero_3263_; 
v_zero_3262_ = lean_unsigned_to_nat(0u);
v_isZero_3263_ = lean_nat_dec_eq(v_i_3261_, v_zero_3262_);
if (v_isZero_3263_ == 1)
{
lean_object* v___x_3264_; 
lean_dec(v_i_3261_);
v___x_3264_ = lean_box(0);
return v___x_3264_;
}
else
{
lean_object* v_one_3265_; lean_object* v_n_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_one_3265_ = lean_unsigned_to_nat(1u);
v_n_3266_ = lean_nat_sub(v_i_3261_, v_one_3265_);
lean_dec(v_i_3261_);
v___x_3267_ = lean_array_fget_borrowed(v_as_3260_, v_n_3266_);
v___x_3268_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v___x_3267_);
if (lean_obj_tag(v___x_3268_) == 0)
{
v_i_3261_ = v_n_3266_;
goto _start;
}
else
{
lean_dec(v_n_3266_);
return v___x_3268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(lean_object* v_x_3270_){
_start:
{
if (lean_obj_tag(v_x_3270_) == 0)
{
lean_object* v_cs_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v_cs_3271_ = lean_ctor_get(v_x_3270_, 0);
v___x_3272_ = lean_array_get_size(v_cs_3271_);
v___x_3273_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_cs_3271_, v___x_3272_);
return v___x_3273_;
}
else
{
lean_object* v_vs_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v_vs_3274_ = lean_ctor_get(v_x_3270_, 0);
v___x_3275_ = lean_array_get_size(v_vs_3274_);
v___x_3276_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_vs_3274_, v___x_3275_);
return v___x_3276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1___boxed(lean_object* v_x_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v_x_3277_);
lean_dec_ref(v_x_3277_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_as_3279_, lean_object* v_i_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_as_3279_, v_i_3280_);
lean_dec_ref(v_as_3279_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(lean_object* v_t_3282_){
_start:
{
lean_object* v_root_3283_; lean_object* v_tail_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v_root_3283_ = lean_ctor_get(v_t_3282_, 0);
v_tail_3284_ = lean_ctor_get(v_t_3282_, 1);
v___x_3285_ = lean_array_get_size(v_tail_3284_);
v___x_3286_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_tail_3284_, v___x_3285_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1(v_root_3283_);
return v___x_3287_;
}
else
{
return v___x_3286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0___boxed(lean_object* v_t_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_t_3288_);
lean_dec_ref(v_t_3288_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_terminalNesting(lean_object* v_x_3290_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_x_3290_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_terminalNesting___boxed(lean_object* v_x_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_Lean_VersoModuleDocs_terminalNesting(v_x_3292_);
lean_dec_ref(v_x_3292_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0(lean_object* v_as_3294_, lean_object* v_i_3295_, lean_object* v_a_3296_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___redArg(v_as_3294_, v_i_3295_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0___boxed(lean_object* v_as_3298_, lean_object* v_i_3299_, lean_object* v_a_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__0(v_as_3298_, v_i_3299_, v_a_3300_);
lean_dec_ref(v_as_3298_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2(lean_object* v_as_3302_, lean_object* v_i_3303_, lean_object* v_a_3304_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___redArg(v_as_3302_, v_i_3303_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2___boxed(lean_object* v_as_3306_, lean_object* v_i_3307_, lean_object* v_a_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0_spec__1_spec__2(v_as_3306_, v_i_3307_, v_a_3308_);
lean_dec_ref(v_as_3306_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0(lean_object* v___x_3316_, lean_object* v_v_3317_, lean_object* v_x_3318_){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3319_ = lean_obj_once(&l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3, &l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3_once, _init_l_Lean_Doc_instReprInline_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__2_spec__4___closed__3);
v___x_3320_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__11));
v___x_3321_ = lean_box(1);
v___x_3322_ = ((lean_object*)(l_Lean_instReprVersoModuleDocs___lam__0___closed__2));
v___x_3323_ = l_Lean_PersistentArray_toArray___redArg(v_v_3317_);
v___x_3324_ = l_Array_repr___redArg(v___x_3316_, v___x_3323_);
v___x_3325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3322_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3319_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
v___x_3327_ = 0;
v___x_3328_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3328_, 0, v___x_3326_);
lean_ctor_set_uint8(v___x_3328_, sizeof(void*)*1, v___x_3327_);
lean_inc_ref(v___x_3328_);
v___x_3329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3320_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
lean_ctor_set(v___x_3330_, 1, v___x_3321_);
v___x_3331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
lean_ctor_set(v___x_3331_, 1, v___x_3328_);
v___x_3332_ = ((lean_object*)(l_Lean_Doc_instReprListItem_repr___at___00Array_repr___at___00Lean_Doc_instReprBlock_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__0_spec__0_spec__3_spec__7___redArg___closed__12));
v___x_3333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3331_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
v___x_3334_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3319_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
lean_ctor_set_uint8(v___x_3335_, sizeof(void*)*1, v___x_3327_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprVersoModuleDocs___lam__0___boxed(lean_object* v___x_3336_, lean_object* v_v_3337_, lean_object* v_x_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l_Lean_instReprVersoModuleDocs___lam__0(v___x_3336_, v_v_3337_, v_x_3338_);
lean_dec(v_x_3338_);
lean_dec_ref(v_v_3337_);
return v_res_3339_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_isEmpty(lean_object* v_docs_3343_){
_start:
{
uint8_t v___x_3344_; 
v___x_3344_ = l_Lean_PersistentArray_isEmpty___redArg(v_docs_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_isEmpty___boxed(lean_object* v_docs_3345_){
_start:
{
uint8_t v_res_3346_; lean_object* v_r_3347_; 
v_res_3346_ = l_Lean_VersoModuleDocs_isEmpty(v_docs_3345_);
lean_dec_ref(v_docs_3345_);
v_r_3347_ = lean_box(v_res_3346_);
return v_r_3347_;
}
}
LEAN_EXPORT uint8_t l_Lean_VersoModuleDocs_canAdd(lean_object* v_docs_3348_, lean_object* v_snippet_3349_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_3348_);
if (lean_obj_tag(v___x_3350_) == 1)
{
lean_object* v_val_3351_; uint8_t v___x_3352_; 
v_val_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_val_3351_);
lean_dec_ref_known(v___x_3350_, 1);
v___x_3352_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_3351_, v_snippet_3349_);
lean_dec(v_val_3351_);
return v___x_3352_;
}
else
{
uint8_t v___x_3353_; 
lean_dec(v___x_3350_);
v___x_3353_ = 1;
return v___x_3353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_canAdd___boxed(lean_object* v_docs_3354_, lean_object* v_snippet_3355_){
_start:
{
uint8_t v_res_3356_; lean_object* v_r_3357_; 
v_res_3356_ = l_Lean_VersoModuleDocs_canAdd(v_docs_3354_, v_snippet_3355_);
lean_dec_ref(v_snippet_3355_);
lean_dec_ref(v_docs_3354_);
v_r_3357_ = lean_box(v_res_3356_);
return v_r_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add(lean_object* v_docs_3361_, lean_object* v_snippet_3362_){
_start:
{
uint8_t v___x_3363_; 
v___x_3363_ = l_Lean_VersoModuleDocs_canAdd(v_docs_3361_, v_snippet_3362_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; 
lean_dec_ref(v_snippet_3362_);
lean_dec_ref(v_docs_3361_);
v___x_3364_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__1));
return v___x_3364_;
}
else
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = l_Lean_PersistentArray_push___redArg(v_docs_3361_, v_snippet_3362_);
v___x_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
return v___x_3366_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(lean_object* v_msg_3367_){
_start:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3368_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_3369_ = lean_panic_fn_borrowed(v___x_3368_, v_msg_3367_);
return v___x_3369_;
}
}
static lean_object* _init_l_Lean_VersoModuleDocs_add_x21___closed__2(void){
_start:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3372_ = ((lean_object*)(l_Lean_VersoModuleDocs_add___closed__0));
v___x_3373_ = lean_unsigned_to_nat(4u);
v___x_3374_ = lean_unsigned_to_nat(367u);
v___x_3375_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__1));
v___x_3376_ = ((lean_object*)(l_Lean_VersoModuleDocs_add_x21___closed__0));
v___x_3377_ = l_mkPanicMessageWithDecl(v___x_3376_, v___x_3375_, v___x_3374_, v___x_3373_, v___x_3372_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_add_x21(lean_object* v_docs_3378_, lean_object* v_snippet_3379_){
_start:
{
lean_object* v___x_3380_; 
v___x_3380_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_3378_);
if (lean_obj_tag(v___x_3380_) == 1)
{
lean_object* v_val_3381_; uint8_t v___x_3382_; 
v_val_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_val_3381_);
lean_dec_ref_known(v___x_3380_, 1);
v___x_3382_ = l_Lean_VersoModuleDocs_Snippet_canNestIn(v_val_3381_, v_snippet_3379_);
lean_dec(v_val_3381_);
if (v___x_3382_ == 0)
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
lean_dec_ref(v_snippet_3379_);
lean_dec_ref(v_docs_3378_);
v___x_3383_ = lean_obj_once(&l_Lean_VersoModuleDocs_add_x21___closed__2, &l_Lean_VersoModuleDocs_add_x21___closed__2_once, _init_l_Lean_VersoModuleDocs_add_x21___closed__2);
v___x_3384_ = l_panic___at___00Lean_VersoModuleDocs_add_x21_spec__0(v___x_3383_);
return v___x_3384_;
}
else
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_PersistentArray_push___redArg(v_docs_3378_, v_snippet_3379_);
return v___x_3385_;
}
}
else
{
lean_object* v___x_3386_; 
lean_dec(v___x_3380_);
v___x_3386_ = l_Lean_PersistentArray_push___redArg(v_docs_3378_, v_snippet_3379_);
return v___x_3386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(lean_object* v_ctx_3387_){
_start:
{
lean_object* v_context_3388_; lean_object* v___x_3389_; 
v_context_3388_ = lean_ctor_get(v_ctx_3387_, 2);
v___x_3389_ = lean_array_get_size(v_context_3388_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level___boxed(lean_object* v_ctx_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_3390_);
lean_dec_ref(v_ctx_3390_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(lean_object* v_ctx_3395_){
_start:
{
lean_object* v_content_3396_; lean_object* v_priorParts_3397_; lean_object* v_context_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3421_; 
v_content_3396_ = lean_ctor_get(v_ctx_3395_, 0);
v_priorParts_3397_ = lean_ctor_get(v_ctx_3395_, 1);
v_context_3398_ = lean_ctor_get(v_ctx_3395_, 2);
v_isSharedCheck_3421_ = !lean_is_exclusive(v_ctx_3395_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3400_ = v_ctx_3395_;
v_isShared_3401_ = v_isSharedCheck_3421_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_context_3398_);
lean_inc(v_priorParts_3397_);
lean_inc(v_content_3396_);
lean_dec(v_ctx_3395_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3421_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; 
v___x_3402_ = lean_array_get_size(v_context_3398_);
v___x_3403_ = lean_unsigned_to_nat(0u);
v___x_3404_ = lean_nat_dec_eq(v___x_3402_, v___x_3403_);
if (v___x_3404_ == 0)
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v_last_3407_; lean_object* v_content_3408_; lean_object* v_priorParts_3409_; lean_object* v_titleString_3410_; lean_object* v_title_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3405_ = lean_unsigned_to_nat(1u);
v___x_3406_ = lean_nat_sub(v___x_3402_, v___x_3405_);
v_last_3407_ = lean_array_fget_borrowed(v_context_3398_, v___x_3406_);
lean_dec(v___x_3406_);
v_content_3408_ = lean_ctor_get(v_last_3407_, 0);
lean_inc_ref(v_content_3408_);
v_priorParts_3409_ = lean_ctor_get(v_last_3407_, 1);
v_titleString_3410_ = lean_ctor_get(v_last_3407_, 2);
v_title_3411_ = lean_ctor_get(v_last_3407_, 3);
v___x_3412_ = lean_box(0);
lean_inc_ref(v_titleString_3410_);
lean_inc_ref(v_title_3411_);
v___x_3413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3413_, 0, v_title_3411_);
lean_ctor_set(v___x_3413_, 1, v_titleString_3410_);
lean_ctor_set(v___x_3413_, 2, v___x_3412_);
lean_ctor_set(v___x_3413_, 3, v_content_3396_);
lean_ctor_set(v___x_3413_, 4, v_priorParts_3397_);
lean_inc_ref(v_priorParts_3409_);
v___x_3414_ = lean_array_push(v_priorParts_3409_, v___x_3413_);
v___x_3415_ = lean_array_pop(v_context_3398_);
if (v_isShared_3401_ == 0)
{
lean_ctor_set(v___x_3400_, 2, v___x_3415_);
lean_ctor_set(v___x_3400_, 1, v___x_3414_);
lean_ctor_set(v___x_3400_, 0, v_content_3408_);
v___x_3417_ = v___x_3400_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_content_3408_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v___x_3414_);
lean_ctor_set(v_reuseFailAlloc_3419_, 2, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3418_; 
v___x_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
return v___x_3418_;
}
}
else
{
lean_object* v___x_3420_; 
lean_del_object(v___x_3400_);
lean_dec_ref(v_context_3398_);
lean_dec_ref(v_priorParts_3397_);
lean_dec_ref(v_content_3396_);
v___x_3420_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close___closed__1));
return v___x_3420_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(lean_object* v_ctx_3422_){
_start:
{
lean_object* v_context_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v_context_3423_ = lean_ctor_get(v_ctx_3422_, 2);
v___x_3424_ = lean_array_get_size(v_context_3423_);
v___x_3425_ = lean_unsigned_to_nat(0u);
v___x_3426_ = lean_nat_dec_eq(v___x_3424_, v___x_3425_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
v___x_3427_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_3422_);
if (lean_obj_tag(v___x_3427_) == 0)
{
return v___x_3427_;
}
else
{
lean_object* v_a_3428_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref_known(v___x_3427_, 1);
v_ctx_3422_ = v_a_3428_;
goto _start;
}
}
else
{
lean_object* v___x_3430_; 
v___x_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3430_, 0, v_ctx_3422_);
return v___x_3430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(lean_object* v_ctx_3433_, lean_object* v_partLevel_3434_, lean_object* v_part_3435_){
_start:
{
lean_object* v___x_3436_; uint8_t v___x_3437_; 
v___x_3436_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_level(v_ctx_3433_);
v___x_3437_ = lean_nat_dec_lt(v___x_3436_, v_partLevel_3434_);
if (v___x_3437_ == 0)
{
uint8_t v___x_3438_; 
v___x_3438_ = lean_nat_dec_eq(v_partLevel_3434_, v___x_3436_);
lean_dec(v___x_3436_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; 
v___x_3439_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_close(v_ctx_3433_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_dec_ref(v_part_3435_);
lean_dec(v_partLevel_3434_);
return v___x_3439_;
}
else
{
lean_object* v_a_3440_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3440_);
lean_dec_ref_known(v___x_3439_, 1);
v_ctx_3433_ = v_a_3440_;
goto _start;
}
}
else
{
lean_object* v_content_3442_; lean_object* v_priorParts_3443_; lean_object* v_context_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3453_; 
lean_dec(v_partLevel_3434_);
v_content_3442_ = lean_ctor_get(v_ctx_3433_, 0);
v_priorParts_3443_ = lean_ctor_get(v_ctx_3433_, 1);
v_context_3444_ = lean_ctor_get(v_ctx_3433_, 2);
v_isSharedCheck_3453_ = !lean_is_exclusive(v_ctx_3433_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3446_ = v_ctx_3433_;
v_isShared_3447_ = v_isSharedCheck_3453_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_context_3444_);
lean_inc(v_priorParts_3443_);
lean_inc(v_content_3442_);
lean_dec(v_ctx_3433_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3453_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3448_; lean_object* v___x_3450_; 
v___x_3448_ = lean_array_push(v_priorParts_3443_, v_part_3435_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 1, v___x_3448_);
v___x_3450_ = v___x_3446_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_content_3442_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3452_, 2, v_context_3444_);
v___x_3450_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3451_; 
v___x_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
return v___x_3451_;
}
}
}
}
else
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
lean_dec_ref(v_part_3435_);
lean_dec_ref(v_ctx_3433_);
v___x_3454_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__0));
v___x_3455_ = l_Nat_reprFast(v___x_3436_);
v___x_3456_ = lean_string_append(v___x_3454_, v___x_3455_);
lean_dec_ref(v___x_3455_);
v___x_3457_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart___closed__1));
v___x_3458_ = lean_string_append(v___x_3456_, v___x_3457_);
v___x_3459_ = l_Nat_reprFast(v_partLevel_3434_);
v___x_3460_ = lean_string_append(v___x_3458_, v___x_3459_);
lean_dec_ref(v___x_3459_);
v___x_3461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3460_);
return v___x_3461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(lean_object* v_ctx_3465_, lean_object* v_blocks_3466_){
_start:
{
lean_object* v_content_3467_; lean_object* v_priorParts_3468_; lean_object* v_context_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3482_; 
v_content_3467_ = lean_ctor_get(v_ctx_3465_, 0);
v_priorParts_3468_ = lean_ctor_get(v_ctx_3465_, 1);
v_context_3469_ = lean_ctor_get(v_ctx_3465_, 2);
v_isSharedCheck_3482_ = !lean_is_exclusive(v_ctx_3465_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3471_ = v_ctx_3465_;
v_isShared_3472_ = v_isSharedCheck_3482_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_context_3469_);
lean_inc(v_priorParts_3468_);
lean_inc(v_content_3467_);
lean_dec(v_ctx_3465_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3482_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; uint8_t v___x_3475_; 
v___x_3473_ = lean_array_get_size(v_priorParts_3468_);
v___x_3474_ = lean_unsigned_to_nat(0u);
v___x_3475_ = lean_nat_dec_eq(v___x_3473_, v___x_3474_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; 
lean_del_object(v___x_3471_);
lean_dec_ref(v_context_3469_);
lean_dec_ref(v_priorParts_3468_);
lean_dec_ref(v_content_3467_);
v___x_3476_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___closed__1));
return v___x_3476_;
}
else
{
lean_object* v___x_3477_; lean_object* v___x_3479_; 
v___x_3477_ = l_Array_append___redArg(v_content_3467_, v_blocks_3466_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3477_);
v___x_3479_ = v___x_3471_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_priorParts_3468_);
lean_ctor_set(v_reuseFailAlloc_3481_, 2, v_context_3469_);
v___x_3479_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3480_; 
v___x_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3479_);
return v___x_3480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks___boxed(lean_object* v_ctx_3483_, lean_object* v_blocks_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_3483_, v_blocks_3484_);
lean_dec_ref(v_blocks_3484_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(lean_object* v_as_3486_, size_t v_sz_3487_, size_t v_i_3488_, lean_object* v_b_3489_){
_start:
{
uint8_t v___x_3490_; 
v___x_3490_ = lean_usize_dec_lt(v_i_3488_, v_sz_3487_);
if (v___x_3490_ == 0)
{
lean_object* v___x_3491_; 
v___x_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3491_, 0, v_b_3489_);
return v___x_3491_;
}
else
{
lean_object* v_a_3492_; lean_object* v_snd_3493_; lean_object* v_fst_3494_; lean_object* v_snd_3495_; lean_object* v___x_3496_; 
v_a_3492_ = lean_array_uget_borrowed(v_as_3486_, v_i_3488_);
v_snd_3493_ = lean_ctor_get(v_a_3492_, 1);
v_fst_3494_ = lean_ctor_get(v_a_3492_, 0);
v_snd_3495_ = lean_ctor_get(v_snd_3493_, 1);
lean_inc(v_snd_3495_);
lean_inc(v_fst_3494_);
v___x_3496_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addPart(v_b_3489_, v_fst_3494_, v_snd_3495_);
if (lean_obj_tag(v___x_3496_) == 0)
{
return v___x_3496_;
}
else
{
lean_object* v_a_3497_; size_t v___x_3498_; size_t v___x_3499_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3496_, 1);
v___x_3498_ = ((size_t)1ULL);
v___x_3499_ = lean_usize_add(v_i_3488_, v___x_3498_);
v_i_3488_ = v___x_3499_;
v_b_3489_ = v_a_3497_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0___boxed(lean_object* v_as_3501_, lean_object* v_sz_3502_, lean_object* v_i_3503_, lean_object* v_b_3504_){
_start:
{
size_t v_sz_boxed_3505_; size_t v_i_boxed_3506_; lean_object* v_res_3507_; 
v_sz_boxed_3505_ = lean_unbox_usize(v_sz_3502_);
lean_dec(v_sz_3502_);
v_i_boxed_3506_ = lean_unbox_usize(v_i_3503_);
lean_dec(v_i_3503_);
v_res_3507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_as_3501_, v_sz_boxed_3505_, v_i_boxed_3506_, v_b_3504_);
lean_dec_ref(v_as_3501_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(lean_object* v_ctx_3508_, lean_object* v_snippet_3509_){
_start:
{
lean_object* v_text_3510_; lean_object* v_sections_3511_; lean_object* v___x_3512_; 
v_text_3510_ = lean_ctor_get(v_snippet_3509_, 0);
v_sections_3511_ = lean_ctor_get(v_snippet_3509_, 1);
v___x_3512_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addBlocks(v_ctx_3508_, v_text_3510_);
if (lean_obj_tag(v___x_3512_) == 0)
{
return v___x_3512_;
}
else
{
lean_object* v_a_3513_; size_t v_sz_3514_; size_t v___x_3515_; lean_object* v___x_3516_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3513_);
lean_dec_ref_known(v___x_3512_, 1);
v_sz_3514_ = lean_array_size(v_sections_3511_);
v___x_3515_ = ((size_t)0ULL);
v___x_3516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet_spec__0(v_sections_3511_, v_sz_3514_, v___x_3515_, v_a_3513_);
return v___x_3516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet___boxed(lean_object* v_ctx_3517_, lean_object* v_snippet_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_ctx_3517_, v_snippet_3518_);
lean_dec_ref(v_snippet_3518_);
return v_res_3519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(lean_object* v_as_3520_, size_t v_sz_3521_, size_t v_i_3522_, lean_object* v_b_3523_){
_start:
{
uint8_t v___x_3524_; 
v___x_3524_ = lean_usize_dec_lt(v_i_3522_, v_sz_3521_);
if (v___x_3524_ == 0)
{
lean_object* v___x_3525_; 
v___x_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3525_, 0, v_b_3523_);
return v___x_3525_;
}
else
{
lean_object* v_snd_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3548_; 
v_snd_3526_ = lean_ctor_get(v_b_3523_, 1);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_b_3523_);
if (v_isSharedCheck_3548_ == 0)
{
lean_object* v_unused_3549_; 
v_unused_3549_ = lean_ctor_get(v_b_3523_, 0);
lean_dec(v_unused_3549_);
v___x_3528_ = v_b_3523_;
v_isShared_3529_ = v_isSharedCheck_3548_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_snd_3526_);
lean_dec(v_b_3523_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3548_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v_a_3530_; lean_object* v___x_3531_; 
v_a_3530_ = lean_array_uget_borrowed(v_as_3520_, v_i_3522_);
v___x_3531_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_3526_, v_a_3530_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_del_object(v___x_3528_);
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3531_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3531_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3541_; lean_object* v___x_3543_; 
v_a_3540_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3540_);
lean_dec_ref_known(v___x_3531_, 1);
v___x_3541_ = lean_box(0);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 1, v_a_3540_);
lean_ctor_set(v___x_3528_, 0, v___x_3541_);
v___x_3543_ = v___x_3528_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3541_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v_a_3540_);
v___x_3543_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
size_t v___x_3544_; size_t v___x_3545_; 
v___x_3544_ = ((size_t)1ULL);
v___x_3545_ = lean_usize_add(v_i_3522_, v___x_3544_);
v_i_3522_ = v___x_3545_;
v_b_3523_ = v___x_3543_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4___boxed(lean_object* v_as_3550_, lean_object* v_sz_3551_, lean_object* v_i_3552_, lean_object* v_b_3553_){
_start:
{
size_t v_sz_boxed_3554_; size_t v_i_boxed_3555_; lean_object* v_res_3556_; 
v_sz_boxed_3554_ = lean_unbox_usize(v_sz_3551_);
lean_dec(v_sz_3551_);
v_i_boxed_3555_ = lean_unbox_usize(v_i_3552_);
lean_dec(v_i_3552_);
v_res_3556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_3550_, v_sz_boxed_3554_, v_i_boxed_3555_, v_b_3553_);
lean_dec_ref(v_as_3550_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(lean_object* v_as_3557_, size_t v_sz_3558_, size_t v_i_3559_, lean_object* v_b_3560_){
_start:
{
uint8_t v___x_3561_; 
v___x_3561_ = lean_usize_dec_lt(v_i_3559_, v_sz_3558_);
if (v___x_3561_ == 0)
{
lean_object* v___x_3562_; 
v___x_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3562_, 0, v_b_3560_);
return v___x_3562_;
}
else
{
lean_object* v_snd_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3585_; 
v_snd_3563_ = lean_ctor_get(v_b_3560_, 1);
v_isSharedCheck_3585_ = !lean_is_exclusive(v_b_3560_);
if (v_isSharedCheck_3585_ == 0)
{
lean_object* v_unused_3586_; 
v_unused_3586_ = lean_ctor_get(v_b_3560_, 0);
lean_dec(v_unused_3586_);
v___x_3565_ = v_b_3560_;
v_isShared_3566_ = v_isSharedCheck_3585_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_snd_3563_);
lean_dec(v_b_3560_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3585_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v_a_3567_; lean_object* v___x_3568_; 
v_a_3567_ = lean_array_uget_borrowed(v_as_3557_, v_i_3559_);
v___x_3568_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_3563_, v_a_3567_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_del_object(v___x_3565_);
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3568_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3568_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3578_; lean_object* v___x_3580_; 
v_a_3577_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_a_3577_);
lean_dec_ref_known(v___x_3568_, 1);
v___x_3578_ = lean_box(0);
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 1, v_a_3577_);
lean_ctor_set(v___x_3565_, 0, v___x_3578_);
v___x_3580_ = v___x_3565_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3578_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v_a_3577_);
v___x_3580_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
size_t v___x_3581_; size_t v___x_3582_; lean_object* v___x_3583_; 
v___x_3581_ = ((size_t)1ULL);
v___x_3582_ = lean_usize_add(v_i_3559_, v___x_3581_);
v___x_3583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1_spec__4(v_as_3557_, v_sz_3558_, v___x_3582_, v___x_3580_);
return v___x_3583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1___boxed(lean_object* v_as_3587_, lean_object* v_sz_3588_, lean_object* v_i_3589_, lean_object* v_b_3590_){
_start:
{
size_t v_sz_boxed_3591_; size_t v_i_boxed_3592_; lean_object* v_res_3593_; 
v_sz_boxed_3591_ = lean_unbox_usize(v_sz_3588_);
lean_dec(v_sz_3588_);
v_i_boxed_3592_ = lean_unbox_usize(v_i_3589_);
lean_dec(v_i_3589_);
v_res_3593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_as_3587_, v_sz_boxed_3591_, v_i_boxed_3592_, v_b_3590_);
lean_dec_ref(v_as_3587_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_3594_, size_t v_sz_3595_, size_t v_i_3596_, lean_object* v_b_3597_){
_start:
{
uint8_t v___x_3598_; 
v___x_3598_ = lean_usize_dec_lt(v_i_3596_, v_sz_3595_);
if (v___x_3598_ == 0)
{
lean_object* v___x_3599_; 
v___x_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3599_, 0, v_b_3597_);
return v___x_3599_;
}
else
{
lean_object* v_snd_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3622_; 
v_snd_3600_ = lean_ctor_get(v_b_3597_, 1);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_b_3597_);
if (v_isSharedCheck_3622_ == 0)
{
lean_object* v_unused_3623_; 
v_unused_3623_ = lean_ctor_get(v_b_3597_, 0);
lean_dec(v_unused_3623_);
v___x_3602_ = v_b_3597_;
v_isShared_3603_ = v_isSharedCheck_3622_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_snd_3600_);
lean_dec(v_b_3597_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3622_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v_a_3604_; lean_object* v___x_3605_; 
v_a_3604_ = lean_array_uget_borrowed(v_as_3594_, v_i_3596_);
v___x_3605_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_3600_, v_a_3604_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
lean_del_object(v___x_3602_);
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3605_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3605_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3615_; lean_object* v___x_3617_; 
v_a_3614_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3605_, 1);
v___x_3615_ = lean_box(0);
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 1, v_a_3614_);
lean_ctor_set(v___x_3602_, 0, v___x_3615_);
v___x_3617_ = v___x_3602_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3615_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v_a_3614_);
v___x_3617_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
size_t v___x_3618_; size_t v___x_3619_; 
v___x_3618_ = ((size_t)1ULL);
v___x_3619_ = lean_usize_add(v_i_3596_, v___x_3618_);
v_i_3596_ = v___x_3619_;
v_b_3597_ = v___x_3617_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_3624_, lean_object* v_sz_3625_, lean_object* v_i_3626_, lean_object* v_b_3627_){
_start:
{
size_t v_sz_boxed_3628_; size_t v_i_boxed_3629_; lean_object* v_res_3630_; 
v_sz_boxed_3628_ = lean_unbox_usize(v_sz_3625_);
lean_dec(v_sz_3625_);
v_i_boxed_3629_ = lean_unbox_usize(v_i_3626_);
lean_dec(v_i_3626_);
v_res_3630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_3624_, v_sz_boxed_3628_, v_i_boxed_3629_, v_b_3627_);
lean_dec_ref(v_as_3624_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(lean_object* v_as_3631_, size_t v_sz_3632_, size_t v_i_3633_, lean_object* v_b_3634_){
_start:
{
uint8_t v___x_3635_; 
v___x_3635_ = lean_usize_dec_lt(v_i_3633_, v_sz_3632_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; 
v___x_3636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3636_, 0, v_b_3634_);
return v___x_3636_;
}
else
{
lean_object* v_snd_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3659_; 
v_snd_3637_ = lean_ctor_get(v_b_3634_, 1);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_b_3634_);
if (v_isSharedCheck_3659_ == 0)
{
lean_object* v_unused_3660_; 
v_unused_3660_ = lean_ctor_get(v_b_3634_, 0);
lean_dec(v_unused_3660_);
v___x_3639_ = v_b_3634_;
v_isShared_3640_ = v_isSharedCheck_3659_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_snd_3637_);
lean_dec(v_b_3634_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3659_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v_a_3641_; lean_object* v___x_3642_; 
v_a_3641_ = lean_array_uget_borrowed(v_as_3631_, v_i_3633_);
v___x_3642_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_addSnippet(v_snd_3637_, v_a_3641_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3650_; 
lean_del_object(v___x_3639_);
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3645_ = v___x_3642_;
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3642_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_a_3643_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
else
{
lean_object* v_a_3651_; lean_object* v___x_3652_; lean_object* v___x_3654_; 
v_a_3651_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3651_);
lean_dec_ref_known(v___x_3642_, 1);
v___x_3652_ = lean_box(0);
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 1, v_a_3651_);
lean_ctor_set(v___x_3639_, 0, v___x_3652_);
v___x_3654_ = v___x_3639_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3652_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v_a_3651_);
v___x_3654_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
size_t v___x_3655_; size_t v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = ((size_t)1ULL);
v___x_3656_ = lean_usize_add(v_i_3633_, v___x_3655_);
v___x_3657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2_spec__3(v_as_3631_, v_sz_3632_, v___x_3656_, v___x_3654_);
return v___x_3657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2___boxed(lean_object* v_as_3661_, lean_object* v_sz_3662_, lean_object* v_i_3663_, lean_object* v_b_3664_){
_start:
{
size_t v_sz_boxed_3665_; size_t v_i_boxed_3666_; lean_object* v_res_3667_; 
v_sz_boxed_3665_ = lean_unbox_usize(v_sz_3662_);
lean_dec(v_sz_3662_);
v_i_boxed_3666_ = lean_unbox_usize(v_i_3663_);
lean_dec(v_i_3663_);
v_res_3667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_as_3661_, v_sz_boxed_3665_, v_i_boxed_3666_, v_b_3664_);
lean_dec_ref(v_as_3661_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(lean_object* v_init_3668_, lean_object* v_n_3669_, lean_object* v_b_3670_){
_start:
{
if (lean_obj_tag(v_n_3669_) == 0)
{
lean_object* v_cs_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; size_t v_sz_3674_; size_t v___x_3675_; lean_object* v___x_3676_; 
v_cs_3671_ = lean_ctor_get(v_n_3669_, 0);
v___x_3672_ = lean_box(0);
v___x_3673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3672_);
lean_ctor_set(v___x_3673_, 1, v_b_3670_);
v_sz_3674_ = lean_array_size(v_cs_3671_);
v___x_3675_ = ((size_t)0ULL);
v___x_3676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_init_3668_, v_cs_3671_, v_sz_3674_, v___x_3675_, v___x_3673_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3676_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3676_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3699_; 
v_a_3685_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3687_ = v___x_3676_;
v_isShared_3688_ = v_isSharedCheck_3699_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3676_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3699_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v_fst_3689_; 
v_fst_3689_ = lean_ctor_get(v_a_3685_, 0);
if (lean_obj_tag(v_fst_3689_) == 0)
{
lean_object* v_snd_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
v_snd_3690_ = lean_ctor_get(v_a_3685_, 1);
lean_inc(v_snd_3690_);
lean_dec(v_a_3685_);
v___x_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3691_, 0, v_snd_3690_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 0, v___x_3691_);
v___x_3693_ = v___x_3687_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
else
{
lean_object* v_val_3695_; lean_object* v___x_3697_; 
lean_inc_ref(v_fst_3689_);
lean_dec(v_a_3685_);
v_val_3695_ = lean_ctor_get(v_fst_3689_, 0);
lean_inc(v_val_3695_);
lean_dec_ref_known(v_fst_3689_, 1);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 0, v_val_3695_);
v___x_3697_ = v___x_3687_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_val_3695_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
}
else
{
lean_object* v_vs_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; size_t v_sz_3703_; size_t v___x_3704_; lean_object* v___x_3705_; 
v_vs_3700_ = lean_ctor_get(v_n_3669_, 0);
v___x_3701_ = lean_box(0);
v___x_3702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3701_);
lean_ctor_set(v___x_3702_, 1, v_b_3670_);
v_sz_3703_ = lean_array_size(v_vs_3700_);
v___x_3704_ = ((size_t)0ULL);
v___x_3705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__2(v_vs_3700_, v_sz_3703_, v___x_3704_, v___x_3702_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___x_3705_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3705_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3728_; 
v_a_3714_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3716_ = v___x_3705_;
v_isShared_3717_ = v_isSharedCheck_3728_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3705_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3728_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v_fst_3718_; 
v_fst_3718_ = lean_ctor_get(v_a_3714_, 0);
if (lean_obj_tag(v_fst_3718_) == 0)
{
lean_object* v_snd_3719_; lean_object* v___x_3720_; lean_object* v___x_3722_; 
v_snd_3719_ = lean_ctor_get(v_a_3714_, 1);
lean_inc(v_snd_3719_);
lean_dec(v_a_3714_);
v___x_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3720_, 0, v_snd_3719_);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v___x_3720_);
v___x_3722_ = v___x_3716_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3720_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
else
{
lean_object* v_val_3724_; lean_object* v___x_3726_; 
lean_inc_ref(v_fst_3718_);
lean_dec(v_a_3714_);
v_val_3724_ = lean_ctor_get(v_fst_3718_, 0);
lean_inc(v_val_3724_);
lean_dec_ref_known(v_fst_3718_, 1);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v_val_3724_);
v___x_3726_ = v___x_3716_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_val_3724_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(lean_object* v_init_3729_, lean_object* v_as_3730_, size_t v_sz_3731_, size_t v_i_3732_, lean_object* v_b_3733_){
_start:
{
uint8_t v___x_3734_; 
v___x_3734_ = lean_usize_dec_lt(v_i_3732_, v_sz_3731_);
if (v___x_3734_ == 0)
{
lean_object* v___x_3735_; 
v___x_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3735_, 0, v_b_3733_);
return v___x_3735_;
}
else
{
lean_object* v_snd_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3770_; 
v_snd_3736_ = lean_ctor_get(v_b_3733_, 1);
v_isSharedCheck_3770_ = !lean_is_exclusive(v_b_3733_);
if (v_isSharedCheck_3770_ == 0)
{
lean_object* v_unused_3771_; 
v_unused_3771_ = lean_ctor_get(v_b_3733_, 0);
lean_dec(v_unused_3771_);
v___x_3738_ = v_b_3733_;
v_isShared_3739_ = v_isSharedCheck_3770_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_snd_3736_);
lean_dec(v_b_3733_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3770_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v_a_3740_; lean_object* v___x_3741_; 
v_a_3740_ = lean_array_uget_borrowed(v_as_3730_, v_i_3732_);
lean_inc(v_snd_3736_);
v___x_3741_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_3729_, v_a_3740_, v_snd_3736_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_del_object(v___x_3738_);
lean_dec(v_snd_3736_);
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3741_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3741_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3769_; 
v_a_3750_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3752_ = v___x_3741_;
v_isShared_3753_ = v_isSharedCheck_3769_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3741_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3769_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
if (lean_obj_tag(v_a_3750_) == 0)
{
lean_object* v___x_3754_; lean_object* v___x_3756_; 
v___x_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3754_, 0, v_a_3750_);
if (v_isShared_3739_ == 0)
{
lean_ctor_set(v___x_3738_, 0, v___x_3754_);
v___x_3756_ = v___x_3738_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3754_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v_snd_3736_);
v___x_3756_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3758_; 
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v___x_3756_);
v___x_3758_ = v___x_3752_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3762_; lean_object* v___x_3764_; 
lean_del_object(v___x_3752_);
lean_dec(v_snd_3736_);
v_a_3761_ = lean_ctor_get(v_a_3750_, 0);
lean_inc(v_a_3761_);
lean_dec_ref_known(v_a_3750_, 1);
v___x_3762_ = lean_box(0);
if (v_isShared_3739_ == 0)
{
lean_ctor_set(v___x_3738_, 1, v_a_3761_);
lean_ctor_set(v___x_3738_, 0, v___x_3762_);
v___x_3764_ = v___x_3738_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3762_);
lean_ctor_set(v_reuseFailAlloc_3768_, 1, v_a_3761_);
v___x_3764_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
size_t v___x_3765_; size_t v___x_3766_; 
v___x_3765_ = ((size_t)1ULL);
v___x_3766_ = lean_usize_add(v_i_3732_, v___x_3765_);
v_i_3732_ = v___x_3766_;
v_b_3733_ = v___x_3764_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3772_, lean_object* v_as_3773_, lean_object* v_sz_3774_, lean_object* v_i_3775_, lean_object* v_b_3776_){
_start:
{
size_t v_sz_boxed_3777_; size_t v_i_boxed_3778_; lean_object* v_res_3779_; 
v_sz_boxed_3777_ = lean_unbox_usize(v_sz_3774_);
lean_dec(v_sz_3774_);
v_i_boxed_3778_ = lean_unbox_usize(v_i_3775_);
lean_dec(v_i_3775_);
v_res_3779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0_spec__1(v_init_3772_, v_as_3773_, v_sz_boxed_3777_, v_i_boxed_3778_, v_b_3776_);
lean_dec_ref(v_as_3773_);
lean_dec_ref(v_init_3772_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0___boxed(lean_object* v_init_3780_, lean_object* v_n_3781_, lean_object* v_b_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_3780_, v_n_3781_, v_b_3782_);
lean_dec_ref(v_n_3781_);
lean_dec_ref(v_init_3780_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(lean_object* v_t_3784_, lean_object* v_init_3785_){
_start:
{
lean_object* v_root_3786_; lean_object* v_tail_3787_; lean_object* v___x_3788_; 
v_root_3786_ = lean_ctor_get(v_t_3784_, 0);
v_tail_3787_ = lean_ctor_get(v_t_3784_, 1);
lean_inc_ref(v_init_3785_);
v___x_3788_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__0(v_init_3785_, v_root_3786_, v_init_3785_);
lean_dec_ref(v_init_3785_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3788_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3788_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3833_; 
v_a_3797_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3799_ = v___x_3788_;
v_isShared_3800_ = v_isSharedCheck_3833_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3788_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3833_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
if (lean_obj_tag(v_a_3797_) == 0)
{
lean_object* v_a_3801_; lean_object* v___x_3803_; 
v_a_3801_ = lean_ctor_get(v_a_3797_, 0);
lean_inc(v_a_3801_);
lean_dec_ref_known(v_a_3797_, 1);
if (v_isShared_3800_ == 0)
{
lean_ctor_set(v___x_3799_, 0, v_a_3801_);
v___x_3803_ = v___x_3799_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3801_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; size_t v_sz_3808_; size_t v___x_3809_; lean_object* v___x_3810_; 
lean_del_object(v___x_3799_);
v_a_3805_ = lean_ctor_get(v_a_3797_, 0);
lean_inc(v_a_3805_);
lean_dec_ref_known(v_a_3797_, 1);
v___x_3806_ = lean_box(0);
v___x_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3806_);
lean_ctor_set(v___x_3807_, 1, v_a_3805_);
v_sz_3808_ = lean_array_size(v_tail_3787_);
v___x_3809_ = ((size_t)0ULL);
v___x_3810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0_spec__1(v_tail_3787_, v_sz_3808_, v___x_3809_, v___x_3807_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3810_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3810_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3832_; 
v_a_3819_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3821_ = v___x_3810_;
v_isShared_3822_ = v_isSharedCheck_3832_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3810_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3832_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v_fst_3823_; 
v_fst_3823_ = lean_ctor_get(v_a_3819_, 0);
if (lean_obj_tag(v_fst_3823_) == 0)
{
lean_object* v_snd_3824_; lean_object* v___x_3826_; 
v_snd_3824_ = lean_ctor_get(v_a_3819_, 1);
lean_inc(v_snd_3824_);
lean_dec(v_a_3819_);
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 0, v_snd_3824_);
v___x_3826_ = v___x_3821_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_snd_3824_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
else
{
lean_object* v_val_3828_; lean_object* v___x_3830_; 
lean_inc_ref(v_fst_3823_);
lean_dec(v_a_3819_);
v_val_3828_ = lean_ctor_get(v_fst_3823_, 0);
lean_inc(v_val_3828_);
lean_dec_ref_known(v_fst_3823_, 1);
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 0, v_val_3828_);
v___x_3830_ = v___x_3821_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_val_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0___boxed(lean_object* v_t_3834_, lean_object* v_init_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(v_t_3834_, v_init_3835_);
lean_dec_ref(v_t_3834_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble(lean_object* v_docs_3839_){
_start:
{
lean_object* v_ctx_3840_; lean_object* v___x_3841_; 
v_ctx_3840_ = ((lean_object*)(l_Lean_VersoModuleDocs_assemble___closed__0));
v___x_3841_ = l_Lean_PersistentArray_forIn___at___00Lean_VersoModuleDocs_assemble_spec__0(v_docs_3839_, v_ctx_3840_);
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
v_a_3842_ = lean_ctor_get(v___x_3841_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3841_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3841_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3851_; 
v_a_3850_ = lean_ctor_get(v___x_3841_, 0);
lean_inc(v_a_3850_);
lean_dec_ref_known(v___x_3841_, 1);
v___x_3851_ = l___private_Lean_DocString_Extension_0__Lean_VersoModuleDocs_DocContext_closeAll(v_a_3850_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3851_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3851_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3870_; 
v_a_3860_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3862_ = v___x_3851_;
v_isShared_3863_ = v_isSharedCheck_3870_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3851_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3870_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v_content_3864_; lean_object* v_priorParts_3865_; lean_object* v___x_3866_; lean_object* v___x_3868_; 
v_content_3864_ = lean_ctor_get(v_a_3860_, 0);
lean_inc_ref(v_content_3864_);
v_priorParts_3865_ = lean_ctor_get(v_a_3860_, 1);
lean_inc_ref(v_priorParts_3865_);
lean_dec(v_a_3860_);
v___x_3866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3866_, 0, v_content_3864_);
lean_ctor_set(v___x_3866_, 1, v_priorParts_3865_);
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 0, v___x_3866_);
v___x_3868_ = v___x_3862_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3866_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoModuleDocs_assemble___boxed(lean_object* v_docs_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Lean_VersoModuleDocs_assemble(v_docs_3871_);
lean_dec_ref(v_docs_3871_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v_es_3873_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = lean_array_mk(v_es_3873_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v_x_3877_, lean_object* v_x_3878_, lean_object* v_es_3879_){
_start:
{
lean_object* v_ents_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v_ents_3880_ = lean_array_mk(v_es_3879_);
v___x_3881_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_));
lean_inc_ref(v_ents_3880_);
v___x_3882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
lean_ctor_set(v___x_3882_, 1, v_ents_3880_);
lean_ctor_set(v___x_3882_, 2, v_ents_3880_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v_x_3883_, lean_object* v_x_3884_, lean_object* v_es_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__1_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(v_x_3883_, v_x_3884_, v_es_3885_);
lean_dec_ref(v_x_3884_);
lean_dec_ref(v_x_3883_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(lean_object* v___x_3887_, lean_object* v_x_3888_){
_start:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; size_t v___x_3892_; lean_object* v___x_3893_; 
v___x_3889_ = lean_unsigned_to_nat(32u);
v___x_3890_ = lean_mk_empty_array_with_capacity(v___x_3889_);
v___x_3891_ = lean_obj_once(&l_Lean_instInhabitedVersoModuleDocs_default___closed__0, &l_Lean_instInhabitedVersoModuleDocs_default___closed__0_once, _init_l_Lean_instInhabitedVersoModuleDocs_default___closed__0);
v___x_3892_ = ((size_t)5ULL);
lean_inc(v___x_3887_);
v___x_3893_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3893_, 0, v___x_3891_);
lean_ctor_set(v___x_3893_, 1, v___x_3890_);
lean_ctor_set(v___x_3893_, 2, v___x_3887_);
lean_ctor_set(v___x_3893_, 3, v___x_3887_);
lean_ctor_set_usize(v___x_3893_, 4, v___x_3892_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v___x_3894_, lean_object* v_x_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l___private_Lean_DocString_Extension_0__Lean_initFn___lam__2_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(v___x_3894_, v_x_3895_);
lean_dec_ref(v_x_3895_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3918_ = ((lean_object*)(l___private_Lean_DocString_Extension_0__Lean_initFn___closed__7_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_));
v___x_3919_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2____boxed(lean_object* v_a_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l___private_Lean_DocString_Extension_0__Lean_initFn_00___x40_Lean_DocString_Extension_1795461544____hygCtx___hyg_2_();
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainVersoModuleDocs(lean_object* v_env_3922_){
_start:
{
lean_object* v___x_3923_; lean_object* v_toEnvExtension_3924_; lean_object* v_asyncMode_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3923_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_3924_ = lean_ctor_get(v___x_3923_, 0);
v_asyncMode_3925_ = lean_ctor_get(v_toEnvExtension_3924_, 2);
v___x_3926_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_3927_ = lean_box(0);
v___x_3928_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3926_, v___x_3923_, v_env_3922_, v_asyncMode_3925_, v___x_3927_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDocs(lean_object* v_env_3929_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l_Lean_getMainVersoModuleDocs(v_env_3929_);
return v___x_3930_;
}
}
static lean_object* _init_l_Lean_getVersoModuleDoc_x3f___closed__0(void){
_start:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3931_ = l_Lean_instInhabitedVersoModuleDocs_default;
v___x_3932_ = lean_box(0);
v___x_3933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
lean_ctor_set(v___x_3933_, 1, v___x_3931_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f(lean_object* v_env_3934_, lean_object* v_moduleName_3935_){
_start:
{
lean_object* v___x_3936_; 
v___x_3936_ = l_Lean_Environment_getModuleIdx_x3f(v_env_3934_, v_moduleName_3935_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v___x_3937_; 
v___x_3937_ = lean_box(0);
return v___x_3937_;
}
else
{
lean_object* v_val_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3949_; 
v_val_3938_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3940_ = v___x_3936_;
v_isShared_3941_ = v_isSharedCheck_3949_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_val_3938_);
lean_dec(v___x_3936_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3949_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; uint8_t v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3947_; 
v___x_3942_ = lean_obj_once(&l_Lean_getVersoModuleDoc_x3f___closed__0, &l_Lean_getVersoModuleDoc_x3f___closed__0_once, _init_l_Lean_getVersoModuleDoc_x3f___closed__0);
v___x_3943_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v___x_3944_ = 1;
v___x_3945_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3942_, v___x_3943_, v_env_3934_, v_val_3938_, v___x_3944_);
lean_dec(v_val_3938_);
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 0, v___x_3945_);
v___x_3947_ = v___x_3940_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3945_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getVersoModuleDoc_x3f___boxed(lean_object* v_env_3950_, lean_object* v_moduleName_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l_Lean_getVersoModuleDoc_x3f(v_env_3950_, v_moduleName_3951_);
lean_dec(v_moduleName_3951_);
lean_dec_ref(v_env_3950_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet___lam__0(lean_object* v_addEntryFn_3953_, lean_object* v_snippet_3954_, lean_object* v_s_3955_){
_start:
{
lean_object* v_importedEntries_3956_; lean_object* v_state_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3965_; 
v_importedEntries_3956_ = lean_ctor_get(v_s_3955_, 0);
v_state_3957_ = lean_ctor_get(v_s_3955_, 1);
v_isSharedCheck_3965_ = !lean_is_exclusive(v_s_3955_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3959_ = v_s_3955_;
v_isShared_3960_ = v_isSharedCheck_3965_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_state_3957_);
lean_inc(v_importedEntries_3956_);
lean_dec(v_s_3955_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3965_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v_state_3961_; lean_object* v___x_3963_; 
v_state_3961_ = lean_apply_2(v_addEntryFn_3953_, v_state_3957_, v_snippet_3954_);
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 1, v_state_3961_);
v___x_3963_ = v___x_3959_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_importedEntries_3956_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_state_3961_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModuleDocSnippet(lean_object* v_env_3968_, lean_object* v_snippet_3969_){
_start:
{
lean_object* v_docs_3970_; uint8_t v___x_3971_; 
lean_inc_ref(v_env_3968_);
v_docs_3970_ = l_Lean_getMainVersoModuleDocs(v_env_3968_);
v___x_3971_ = l_Lean_VersoModuleDocs_canAdd(v_docs_3970_, v_snippet_3969_);
if (v___x_3971_ == 0)
{
lean_object* v___x_3972_; lean_object* v___y_3974_; lean_object* v___x_3979_; 
lean_dec_ref(v_snippet_3969_);
lean_dec_ref(v_env_3968_);
v___x_3972_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__0));
v___x_3979_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_VersoModuleDocs_terminalNesting_spec__0(v_docs_3970_);
lean_dec_ref(v_docs_3970_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v___x_3980_; 
v___x_3980_ = ((lean_object*)(l_Lean_throwIfHasDocString___redArg___closed__0));
v___y_3974_ = v___x_3980_;
goto v___jp_3973_;
}
else
{
lean_object* v_val_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v_val_3981_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_val_3981_);
lean_dec_ref_known(v___x_3979_, 1);
v___x_3982_ = ((lean_object*)(l_Lean_addVersoModuleDocSnippet___closed__1));
v___x_3983_ = l_Nat_reprFast(v_val_3981_);
v___x_3984_ = lean_string_append(v___x_3982_, v___x_3983_);
lean_dec_ref(v___x_3983_);
v___x_3985_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1));
v___x_3986_ = lean_string_append(v___x_3984_, v___x_3985_);
v___y_3974_ = v___x_3986_;
goto v___jp_3973_;
}
v___jp_3973_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3975_ = lean_string_append(v___x_3972_, v___y_3974_);
lean_dec_ref(v___y_3974_);
v___x_3976_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Lean_VersoModuleDocs_instReprSnippet_repr_spec__1_spec__3___redArg___closed__1));
v___x_3977_ = lean_string_append(v___x_3975_, v___x_3976_);
v___x_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3977_);
return v___x_3978_;
}
}
else
{
lean_object* v___x_3987_; lean_object* v_toEnvExtension_3988_; lean_object* v_addEntryFn_3989_; lean_object* v_asyncMode_3990_; uint8_t v_logWrites_3991_; lean_object* v___f_3992_; lean_object* v___x_3993_; 
lean_dec_ref(v_docs_3970_);
v___x_3987_ = l___private_Lean_DocString_Extension_0__Lean_versoModuleDocExt;
v_toEnvExtension_3988_ = lean_ctor_get(v___x_3987_, 0);
v_addEntryFn_3989_ = lean_ctor_get(v___x_3987_, 3);
v_asyncMode_3990_ = lean_ctor_get(v_toEnvExtension_3988_, 2);
v_logWrites_3991_ = lean_ctor_get_uint8(v_toEnvExtension_3988_, sizeof(void*)*6);
lean_inc(v_addEntryFn_3989_);
v___f_3992_ = lean_alloc_closure((void*)(l_Lean_addVersoModuleDocSnippet___lam__0), 3, 2);
lean_closure_set(v___f_3992_, 0, v_addEntryFn_3989_);
lean_closure_set(v___f_3992_, 1, v_snippet_3969_);
v___x_3993_ = lean_box(0);
if (v_logWrites_3991_ == 0)
{
lean_object* v___x_3994_; lean_object* v___x_3995_; 
lean_inc_ref(v_toEnvExtension_3988_);
v___x_3994_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3988_, v_env_3968_, v___f_3992_, v_asyncMode_3990_, v___x_3993_, v___x_3971_);
v___x_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3994_);
return v___x_3995_;
}
else
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
lean_inc_ref_n(v_toEnvExtension_3988_, 2);
v___x_3996_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3988_, v_env_3968_);
lean_dec_ref(v_env_3968_);
v___x_3997_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3988_, v___x_3996_, v___f_3992_, v_asyncMode_3990_, v___x_3993_, v___x_3971_);
v___x_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
return v___x_3998_;
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
