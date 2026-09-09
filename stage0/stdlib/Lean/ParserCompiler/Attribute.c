// Lean compiler output
// Module: Lean.ParserCompiler.Attribute
// Imports: public import Lean.Compiler.InitAttr import Lean.ExtraModUses
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* l_Lean_MessageData_ofName(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
extern lean_object* l_Lean_instInhabitedAttributeImpl_default;
static const lean_string_object l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___closed__0 = (const lean_object*)&l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___closed__0_value)}};
static const lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___closed__1 = (const lean_object*)&l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__0 = (const lean_object*)&l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__0_value),((lean_object*)&l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__0_value)}};
static const lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__1 = (const lean_object*)&l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__0 = (const lean_object*)&l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__0_value;
static const lean_closure_object l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__1 = (const lean_object*)&l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__1_value;
static const lean_closure_object l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__2 = (const lean_object*)&l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__2_value;
static const lean_closure_object l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__3 = (const lean_object*)&l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__3_value;
static lean_once_cell_t l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__4;
static lean_once_cell_t l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__5;
static lean_once_cell_t l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__6;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute;
static const lean_string_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__0 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__0_value;
static const lean_string_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__1 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__1_value;
static const lean_string_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__2 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__2_value;
static const lean_string_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__3 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__3_value;
static const lean_ctor_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4_value;
static const lean_array_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__5 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__5_value;
static const lean_string_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__6 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7_value;
static const lean_string_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__8 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__9 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__9_value;
static const lean_string_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__10 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11_value_aux_1),((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11_value_aux_2),((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11_value;
static lean_once_cell_t l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__12;
static lean_once_cell_t l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__13;
static const lean_string_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__14 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__14_value;
static const lean_string_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__15 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__15_value;
static const lean_ctor_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16_value_aux_0),((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16_value_aux_1),((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16_value_aux_2),((lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16_value;
static const lean_string_object l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__17 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__17_value;
static lean_once_cell_t l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__18;
static lean_once_cell_t l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__19;
static lean_once_cell_t l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__20;
static lean_once_cell_t l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__21;
static lean_once_cell_t l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__22;
static lean_once_cell_t l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__23;
static lean_once_cell_t l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__24;
static lean_once_cell_t l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__25;
static lean_once_cell_t l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__26;
static lean_once_cell_t l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__27;
static lean_once_cell_t l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__28;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__1(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__0 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__1;
static const lean_string_object l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__2 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__10_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_ParserCompiler_registerCombinatorAttribute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___closed__0 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___closed__0_value;
static const lean_closure_object l_Lean_ParserCompiler_registerCombinatorAttribute___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ParserCompiler_registerCombinatorAttribute___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___closed__1 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___closed__1_value;
static const lean_closure_object l_Lean_ParserCompiler_registerCombinatorAttribute___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___closed__2 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "no declaration of attribute ["};
static const lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__0 = (const lean_object*)&l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__0_value;
static lean_once_cell_t l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__1;
static const lean_string_object l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "] found for `"};
static const lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__2 = (const lean_object*)&l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__2_value;
static lean_once_cell_t l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__3;
static const lean_string_object l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__4 = (const lean_object*)&l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__4_value;
static lean_once_cell_t l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0(lean_object* v_x_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = ((lean_object*)(l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___closed__1));
v___x_8_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0___boxed(lean_object* v_x_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__0(v_x_9_, v___y_10_);
lean_dec_ref(v___y_10_);
lean_dec_ref(v_x_9_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__1(lean_object* v_s_13_, lean_object* v_x_14_){
_start:
{
lean_inc_ref(v_s_13_);
return v_s_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__1___boxed(lean_object* v_s_15_, lean_object* v_x_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__1(v_s_15_, v_x_16_);
lean_dec_ref(v_x_16_);
lean_dec_ref(v_s_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2(lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = ((lean_object*)(l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___closed__1));
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2___boxed(lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__2(v_x_25_, v_x_26_);
lean_dec_ref(v_x_26_);
lean_dec_ref(v_x_25_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__3(lean_object* v_x_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_box(0);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__3___boxed(lean_object* v_x_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___lam__3(v_x_30_);
lean_dec_ref(v_x_30_);
return v_res_31_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_36_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_37_; lean_object* v___f_38_; lean_object* v___f_39_; lean_object* v___f_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___f_37_ = ((lean_object*)(l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__3));
v___f_38_ = ((lean_object*)(l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__2));
v___f_39_ = ((lean_object*)(l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__1));
v___f_40_ = ((lean_object*)(l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__0));
v___x_41_ = lean_box(0);
v___x_42_ = lean_obj_once(&l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__4, &l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__4_once, _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__4);
v___x_43_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_41_);
lean_ctor_set(v___x_43_, 2, v___f_40_);
lean_ctor_set(v___x_43_, 3, v___f_39_);
lean_ctor_set(v___x_43_, 4, v___f_38_);
lean_ctor_set(v___x_43_, 5, v___f_37_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_obj_once(&l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__5, &l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__5_once, _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__5);
v___x_45_ = l_Lean_instInhabitedAttributeImpl_default;
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
lean_ctor_set(v___x_46_, 1, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default(void){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_obj_once(&l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__6, &l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__6_once, _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default___closed__6);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default;
return v___x_48_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__12(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__10));
v___x_76_ = l_Lean_mkAtom(v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__13(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_obj_once(&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__12, &l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__12_once, _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__12);
v___x_78_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__5));
v___x_79_ = lean_array_push(v___x_78_, v___x_77_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__18(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__17));
v___x_89_ = l_Lean_mkAtom(v___x_88_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__19(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_obj_once(&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__18, &l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__18_once, _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__18);
v___x_91_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__5));
v___x_92_ = lean_array_push(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__20(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_93_ = lean_obj_once(&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__19, &l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__19_once, _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__19);
v___x_94_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__16));
v___x_95_ = lean_box(2);
v___x_96_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_94_);
lean_ctor_set(v___x_96_, 2, v___x_93_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__21(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_obj_once(&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__20, &l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__20_once, _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__20);
v___x_98_ = lean_obj_once(&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__13, &l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__13_once, _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__13);
v___x_99_ = lean_array_push(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__22(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_100_ = lean_obj_once(&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__21, &l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__21_once, _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__21);
v___x_101_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__11));
v___x_102_ = lean_box(2);
v___x_103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_101_);
lean_ctor_set(v___x_103_, 2, v___x_100_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__23(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_obj_once(&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__22, &l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__22_once, _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__22);
v___x_105_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__5));
v___x_106_ = lean_array_push(v___x_105_, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__24(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_107_ = lean_obj_once(&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__23, &l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__23_once, _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__23);
v___x_108_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__9));
v___x_109_ = lean_box(2);
v___x_110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v___x_108_);
lean_ctor_set(v___x_110_, 2, v___x_107_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__25(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = lean_obj_once(&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__24, &l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__24_once, _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__24);
v___x_112_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__5));
v___x_113_ = lean_array_push(v___x_112_, v___x_111_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__26(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_114_ = lean_obj_once(&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__25, &l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__25_once, _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__25);
v___x_115_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__7));
v___x_116_ = lean_box(2);
v___x_117_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
lean_ctor_set(v___x_117_, 2, v___x_114_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__27(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = lean_obj_once(&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__26, &l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__26_once, _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__26);
v___x_119_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__5));
v___x_120_ = lean_array_push(v___x_119_, v___x_118_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__28(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_121_ = lean_obj_once(&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__27, &l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__27_once, _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__27);
v___x_122_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__4));
v___x_123_ = lean_box(2);
v___x_124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v___x_122_);
lean_ctor_set(v___x_124_, 2, v___x_121_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_obj_once(&l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__28, &l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__28_once, _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1___closed__28);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_126_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__0, &l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__0);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__1, &l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__1);
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg(lean_object* v_env_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; lean_object* v_nextMacroScope_135_; lean_object* v_ngen_136_; lean_object* v_auxDeclNGen_137_; lean_object* v_traceState_138_; lean_object* v_messages_139_; lean_object* v_infoState_140_; lean_object* v_snapshotTasks_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_152_; 
v___x_134_ = lean_st_ref_take(v___y_132_);
v_nextMacroScope_135_ = lean_ctor_get(v___x_134_, 1);
v_ngen_136_ = lean_ctor_get(v___x_134_, 2);
v_auxDeclNGen_137_ = lean_ctor_get(v___x_134_, 3);
v_traceState_138_ = lean_ctor_get(v___x_134_, 4);
v_messages_139_ = lean_ctor_get(v___x_134_, 6);
v_infoState_140_ = lean_ctor_get(v___x_134_, 7);
v_snapshotTasks_141_ = lean_ctor_get(v___x_134_, 8);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_152_ == 0)
{
lean_object* v_unused_153_; lean_object* v_unused_154_; 
v_unused_153_ = lean_ctor_get(v___x_134_, 5);
lean_dec(v_unused_153_);
v_unused_154_ = lean_ctor_get(v___x_134_, 0);
lean_dec(v_unused_154_);
v___x_143_ = v___x_134_;
v_isShared_144_ = v_isSharedCheck_152_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_snapshotTasks_141_);
lean_inc(v_infoState_140_);
lean_inc(v_messages_139_);
lean_inc(v_traceState_138_);
lean_inc(v_auxDeclNGen_137_);
lean_inc(v_ngen_136_);
lean_inc(v_nextMacroScope_135_);
lean_dec(v___x_134_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_152_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_145_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 5, v___x_145_);
lean_ctor_set(v___x_143_, 0, v_env_131_);
v___x_147_ = v___x_143_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_env_131_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_nextMacroScope_135_);
lean_ctor_set(v_reuseFailAlloc_151_, 2, v_ngen_136_);
lean_ctor_set(v_reuseFailAlloc_151_, 3, v_auxDeclNGen_137_);
lean_ctor_set(v_reuseFailAlloc_151_, 4, v_traceState_138_);
lean_ctor_set(v_reuseFailAlloc_151_, 5, v___x_145_);
lean_ctor_set(v_reuseFailAlloc_151_, 6, v_messages_139_);
lean_ctor_set(v_reuseFailAlloc_151_, 7, v_infoState_140_);
lean_ctor_set(v_reuseFailAlloc_151_, 8, v_snapshotTasks_141_);
v___x_147_ = v_reuseFailAlloc_151_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_st_ref_put(v___y_132_, v___x_147_);
v___x_149_ = lean_box(0);
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___boxed(lean_object* v_env_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg(v_env_155_, v___y_156_);
lean_dec(v___y_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3(lean_object* v_env_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg(v_env_159_, v___y_161_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___boxed(lean_object* v_env_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3(v_env_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0(lean_object* v_es_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_array_mk(v_es_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__1(lean_object* v_s_171_, lean_object* v_p_172_){
_start:
{
lean_object* v_fst_173_; lean_object* v_snd_174_; lean_object* v___x_175_; 
v_fst_173_ = lean_ctor_get(v_p_172_, 0);
lean_inc(v_fst_173_);
v_snd_174_ = lean_ctor_get(v_p_172_, 1);
lean_inc(v_snd_174_);
lean_dec_ref(v_p_172_);
v___x_175_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_173_, v_snd_174_, v_s_171_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_176_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0);
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1);
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
lean_ctor_set(v___x_181_, 2, v___x_180_);
lean_ctor_set(v___x_181_, 3, v___x_180_);
lean_ctor_set(v___x_181_, 4, v___x_179_);
lean_ctor_set(v___x_181_, 5, v___x_179_);
lean_ctor_set(v___x_181_, 6, v___x_179_);
lean_ctor_set(v___x_181_, 7, v___x_179_);
lean_ctor_set(v___x_181_, 8, v___x_179_);
lean_ctor_set(v___x_181_, 9, v___x_179_);
lean_ctor_set(v___x_181_, 10, v___x_179_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_unsigned_to_nat(32u);
v___x_183_ = lean_mk_empty_array_with_capacity(v___x_182_);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_185_ = ((size_t)5ULL);
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = lean_unsigned_to_nat(32u);
v___x_188_ = lean_mk_empty_array_with_capacity(v___x_187_);
v___x_189_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__3);
v___x_190_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v___x_188_);
lean_ctor_set(v___x_190_, 2, v___x_186_);
lean_ctor_set(v___x_190_, 3, v___x_186_);
lean_ctor_set_usize(v___x_190_, 4, v___x_185_);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_191_ = lean_box(1);
v___x_192_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__4);
v___x_193_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1);
v___x_194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v___x_192_);
lean_ctor_set(v___x_194_, 2, v___x_191_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0(lean_object* v_msgData_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; lean_object* v_env_200_; lean_object* v_options_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_199_ = lean_st_ref_get(v___y_197_);
v_env_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc_ref(v_env_200_);
lean_dec(v___x_199_);
v_options_201_ = lean_ctor_get(v___y_196_, 1);
v___x_202_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__2);
v___x_203_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_201_);
v___x_204_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_204_, 0, v_env_200_);
lean_ctor_set(v___x_204_, 1, v___x_202_);
lean_ctor_set(v___x_204_, 2, v___x_203_);
lean_ctor_set(v___x_204_, 3, v_options_201_);
v___x_205_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v_msgData_195_);
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___boxed(lean_object* v_msgData_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0(v_msgData_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(lean_object* v_msg_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_ref_216_; lean_object* v___x_217_; lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_226_; 
v_ref_216_ = lean_ctor_get(v___y_213_, 4);
v___x_217_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0(v_msg_212_, v___y_213_, v___y_214_);
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_226_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
lean_inc(v_ref_216_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v_ref_216_);
lean_ctor_set(v___x_222_, 1, v_a_218_);
if (v_isShared_221_ == 0)
{
lean_ctor_set_tag(v___x_220_, 1);
lean_ctor_set(v___x_220_, 0, v___x_222_);
v___x_224_ = v___x_220_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg___boxed(lean_object* v_msg_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(v_msg_227_, v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
return v_res_231_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__1(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__0));
v___x_234_ = l_Lean_stringToMessageData(v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__3(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__2));
v___x_237_ = l_Lean_stringToMessageData(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2(lean_object* v_name_238_, lean_object* v_decl_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_243_ = lean_obj_once(&l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__1, &l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__1_once, _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__1);
v___x_244_ = l_Lean_MessageData_ofName(v_name_238_);
v___x_245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = lean_obj_once(&l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__3, &l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__3_once, _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___closed__3);
v___x_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(v___x_247_, v___y_240_, v___y_241_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___boxed(lean_object* v_name_249_, lean_object* v_decl_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2(v_name_249_, v_decl_250_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v_decl_250_);
return v_res_254_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__0(void){
_start:
{
lean_object* v___x_255_; double v___x_256_; 
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = lean_float_of_nat(v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8(lean_object* v_cls_260_, lean_object* v_msg_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_ref_265_; lean_object* v___x_266_; lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_311_; 
v_ref_265_ = lean_ctor_get(v___y_262_, 4);
v___x_266_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0(v_msg_261_, v___y_262_, v___y_263_);
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_311_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_311_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_311_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v_traceState_272_; lean_object* v_env_273_; lean_object* v_nextMacroScope_274_; lean_object* v_ngen_275_; lean_object* v_auxDeclNGen_276_; lean_object* v_cache_277_; lean_object* v_messages_278_; lean_object* v_infoState_279_; lean_object* v_snapshotTasks_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_310_; 
v___x_271_ = lean_st_ref_take(v___y_263_);
v_traceState_272_ = lean_ctor_get(v___x_271_, 4);
v_env_273_ = lean_ctor_get(v___x_271_, 0);
v_nextMacroScope_274_ = lean_ctor_get(v___x_271_, 1);
v_ngen_275_ = lean_ctor_get(v___x_271_, 2);
v_auxDeclNGen_276_ = lean_ctor_get(v___x_271_, 3);
v_cache_277_ = lean_ctor_get(v___x_271_, 5);
v_messages_278_ = lean_ctor_get(v___x_271_, 6);
v_infoState_279_ = lean_ctor_get(v___x_271_, 7);
v_snapshotTasks_280_ = lean_ctor_get(v___x_271_, 8);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_310_ == 0)
{
v___x_282_ = v___x_271_;
v_isShared_283_ = v_isSharedCheck_310_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_snapshotTasks_280_);
lean_inc(v_infoState_279_);
lean_inc(v_messages_278_);
lean_inc(v_cache_277_);
lean_inc(v_traceState_272_);
lean_inc(v_auxDeclNGen_276_);
lean_inc(v_ngen_275_);
lean_inc(v_nextMacroScope_274_);
lean_inc(v_env_273_);
lean_dec(v___x_271_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_310_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
uint64_t v_tid_284_; lean_object* v_traces_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_309_; 
v_tid_284_ = lean_ctor_get_uint64(v_traceState_272_, sizeof(void*)*1);
v_traces_285_ = lean_ctor_get(v_traceState_272_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v_traceState_272_);
if (v_isSharedCheck_309_ == 0)
{
v___x_287_ = v_traceState_272_;
v_isShared_288_ = v_isSharedCheck_309_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_traces_285_);
lean_dec(v_traceState_272_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_309_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; double v___x_290_; uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_289_ = lean_box(0);
v___x_290_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__0);
v___x_291_ = 0;
v___x_292_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__1));
v___x_293_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_293_, 0, v_cls_260_);
lean_ctor_set(v___x_293_, 1, v___x_289_);
lean_ctor_set(v___x_293_, 2, v___x_292_);
lean_ctor_set_float(v___x_293_, sizeof(void*)*3, v___x_290_);
lean_ctor_set_float(v___x_293_, sizeof(void*)*3 + 8, v___x_290_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*3 + 16, v___x_291_);
v___x_294_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__2));
v___x_295_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v_a_267_);
lean_ctor_set(v___x_295_, 2, v___x_294_);
lean_inc(v_ref_265_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v_ref_265_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = l_Lean_PersistentArray_push___redArg(v_traces_285_, v___x_296_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_297_);
v___x_299_ = v___x_287_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_297_);
lean_ctor_set_uint64(v_reuseFailAlloc_308_, sizeof(void*)*1, v_tid_284_);
v___x_299_ = v_reuseFailAlloc_308_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_301_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 4, v___x_299_);
v___x_301_ = v___x_282_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_env_273_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_nextMacroScope_274_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v_ngen_275_);
lean_ctor_set(v_reuseFailAlloc_307_, 3, v_auxDeclNGen_276_);
lean_ctor_set(v_reuseFailAlloc_307_, 4, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_307_, 5, v_cache_277_);
lean_ctor_set(v_reuseFailAlloc_307_, 6, v_messages_278_);
lean_ctor_set(v_reuseFailAlloc_307_, 7, v_infoState_279_);
lean_ctor_set(v_reuseFailAlloc_307_, 8, v_snapshotTasks_280_);
v___x_301_ = v_reuseFailAlloc_307_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_302_ = lean_st_ref_put(v___y_263_, v___x_301_);
v___x_303_ = lean_box(0);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_303_);
v___x_305_ = v___x_269_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_303_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___boxed(lean_object* v_cls_312_, lean_object* v_msg_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8(v_cls_312_, v_msg_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_317_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___redArg(lean_object* v_keys_318_, lean_object* v_i_319_, lean_object* v_k_320_){
_start:
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = lean_array_get_size(v_keys_318_);
v___x_322_ = lean_nat_dec_lt(v_i_319_, v___x_321_);
if (v___x_322_ == 0)
{
lean_dec(v_i_319_);
return v___x_322_;
}
else
{
lean_object* v_k_x27_323_; uint8_t v___x_324_; 
v_k_x27_323_ = lean_array_fget_borrowed(v_keys_318_, v_i_319_);
v___x_324_ = l_Lean_instBEqExtraModUse_beq(v_k_320_, v_k_x27_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_unsigned_to_nat(1u);
v___x_326_ = lean_nat_add(v_i_319_, v___x_325_);
lean_dec(v_i_319_);
v_i_319_ = v___x_326_;
goto _start;
}
else
{
lean_dec(v_i_319_);
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_keys_328_, lean_object* v_i_329_, lean_object* v_k_330_){
_start:
{
uint8_t v_res_331_; lean_object* v_r_332_; 
v_res_331_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___redArg(v_keys_328_, v_i_329_, v_k_330_);
lean_dec_ref(v_k_330_);
lean_dec_ref(v_keys_328_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg(lean_object* v_x_333_, size_t v_x_334_, lean_object* v_x_335_){
_start:
{
if (lean_obj_tag(v_x_333_) == 0)
{
lean_object* v_es_336_; lean_object* v___x_337_; size_t v___x_338_; size_t v___x_339_; lean_object* v_j_340_; lean_object* v___x_341_; 
v_es_336_ = lean_ctor_get(v_x_333_, 0);
v___x_337_ = lean_box(2);
v___x_338_ = ((size_t)31ULL);
v___x_339_ = lean_usize_land(v_x_334_, v___x_338_);
v_j_340_ = lean_usize_to_nat(v___x_339_);
v___x_341_ = lean_array_get_borrowed(v___x_337_, v_es_336_, v_j_340_);
lean_dec(v_j_340_);
switch(lean_obj_tag(v___x_341_))
{
case 0:
{
lean_object* v_key_342_; uint8_t v___x_343_; 
v_key_342_ = lean_ctor_get(v___x_341_, 0);
v___x_343_ = l_Lean_instBEqExtraModUse_beq(v_x_335_, v_key_342_);
return v___x_343_;
}
case 1:
{
lean_object* v_node_344_; size_t v___x_345_; size_t v___x_346_; 
v_node_344_ = lean_ctor_get(v___x_341_, 0);
v___x_345_ = ((size_t)5ULL);
v___x_346_ = lean_usize_shift_right(v_x_334_, v___x_345_);
v_x_333_ = v_node_344_;
v_x_334_ = v___x_346_;
goto _start;
}
default: 
{
uint8_t v___x_348_; 
v___x_348_ = 0;
return v___x_348_;
}
}
}
else
{
lean_object* v_ks_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v_ks_349_ = lean_ctor_get(v_x_333_, 0);
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___redArg(v_ks_349_, v___x_350_, v_x_335_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg___boxed(lean_object* v_x_352_, lean_object* v_x_353_, lean_object* v_x_354_){
_start:
{
size_t v_x_5202__boxed_355_; uint8_t v_res_356_; lean_object* v_r_357_; 
v_x_5202__boxed_355_ = lean_unbox_usize(v_x_353_);
lean_dec(v_x_353_);
v_res_356_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg(v_x_352_, v_x_5202__boxed_355_, v_x_354_);
lean_dec_ref(v_x_354_);
lean_dec_ref(v_x_352_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___redArg(lean_object* v_x_358_, lean_object* v_x_359_){
_start:
{
uint64_t v___x_360_; size_t v___x_361_; uint8_t v___x_362_; 
v___x_360_ = l_Lean_instHashableExtraModUse_hash(v_x_359_);
v___x_361_ = lean_uint64_to_usize(v___x_360_);
v___x_362_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg(v_x_358_, v___x_361_, v_x_359_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
uint8_t v_res_365_; lean_object* v_r_366_; 
v_res_365_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___redArg(v_x_363_, v_x_364_);
lean_dec_ref(v_x_364_);
lean_dec_ref(v_x_363_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__2(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_369_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__1));
v___x_370_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__0));
v___x_371_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_370_, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__5));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__8(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__7));
v___x_380_ = l_Lean_stringToMessageData(v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__9(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__1));
v___x_382_ = l_Lean_stringToMessageData(v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12(void){
_start:
{
lean_object* v_cls_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_cls_386_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__4));
v___x_387_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__11));
v___x_388_ = l_Lean_Name_append(v___x_387_, v_cls_386_);
return v___x_388_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__13));
v___x_391_ = l_Lean_stringToMessageData(v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__16(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__15));
v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5(lean_object* v_mod_399_, uint8_t v_isMeta_400_, lean_object* v_hint_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; lean_object* v_env_406_; uint8_t v_isExporting_407_; lean_object* v___x_408_; lean_object* v_env_409_; lean_object* v___x_410_; lean_object* v_entry_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___y_416_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_405_ = lean_st_ref_get(v___y_403_);
v_env_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc_ref(v_env_406_);
lean_dec(v___x_405_);
v_isExporting_407_ = lean_ctor_get_uint8(v_env_406_, sizeof(void*)*8);
lean_dec_ref(v_env_406_);
v___x_408_ = lean_st_ref_get(v___y_403_);
v_env_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc_ref(v_env_409_);
lean_dec(v___x_408_);
v___x_410_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__2);
lean_inc(v_mod_399_);
v_entry_411_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_411_, 0, v_mod_399_);
lean_ctor_set_uint8(v_entry_411_, sizeof(void*)*1, v_isExporting_407_);
lean_ctor_set_uint8(v_entry_411_, sizeof(void*)*1 + 1, v_isMeta_400_);
v___x_412_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_413_ = lean_box(1);
v___x_414_ = lean_box(0);
v___x_441_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_410_, v___x_412_, v_env_409_, v___x_413_, v___x_414_);
v___x_442_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___redArg(v___x_441_, v_entry_411_);
lean_dec(v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v_options_443_; uint8_t v_hasTrace_444_; 
v_options_443_ = lean_ctor_get(v___y_402_, 1);
v_hasTrace_444_ = lean_ctor_get_uint8(v_options_443_, sizeof(void*)*1);
if (v_hasTrace_444_ == 0)
{
lean_dec(v_hint_401_);
lean_dec(v_mod_399_);
v___y_416_ = v___y_403_;
goto v___jp_415_;
}
else
{
lean_object* v_toCold_445_; lean_object* v_inheritedTraceOptions_446_; lean_object* v_cls_447_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___x_467_; uint8_t v___x_468_; 
v_toCold_445_ = lean_ctor_get(v___y_402_, 0);
v_inheritedTraceOptions_446_ = lean_ctor_get(v_toCold_445_, 4);
v_cls_447_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__4));
v___x_467_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12);
v___x_468_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_446_, v_options_443_, v___x_467_);
if (v___x_468_ == 0)
{
lean_dec(v_hint_401_);
lean_dec(v_mod_399_);
v___y_416_ = v___y_403_;
goto v___jp_415_;
}
else
{
lean_object* v___x_469_; lean_object* v___y_471_; 
v___x_469_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14);
if (v_isExporting_407_ == 0)
{
lean_object* v___x_478_; 
v___x_478_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__19));
v___y_471_ = v___x_478_;
goto v___jp_470_;
}
else
{
lean_object* v___x_479_; 
v___x_479_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__20));
v___y_471_ = v___x_479_;
goto v___jp_470_;
}
v___jp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
lean_inc_ref(v___y_471_);
v___x_472_ = l_Lean_stringToMessageData(v___y_471_);
v___x_473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_469_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__16);
v___x_475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_473_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
if (v_isMeta_400_ == 0)
{
lean_object* v___x_476_; 
v___x_476_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__17));
v___y_454_ = v___x_475_;
v___y_455_ = v___x_476_;
goto v___jp_453_;
}
else
{
lean_object* v___x_477_; 
v___x_477_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__18));
v___y_454_ = v___x_475_;
v___y_455_ = v___x_477_;
goto v___jp_453_;
}
}
}
v___jp_448_:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_451_, 0, v___y_449_);
lean_ctor_set(v___x_451_, 1, v___y_450_);
v___x_452_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8(v_cls_447_, v___x_451_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_dec_ref_known(v___x_452_, 1);
v___y_416_ = v___y_403_;
goto v___jp_415_;
}
else
{
lean_dec_ref_known(v_entry_411_, 1);
return v___x_452_;
}
}
v___jp_453_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
lean_inc_ref(v___y_455_);
v___x_456_ = l_Lean_stringToMessageData(v___y_455_);
v___x_457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_457_, 0, v___y_454_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6);
v___x_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = l_Lean_MessageData_ofName(v_mod_399_);
v___x_461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = l_Lean_Name_isAnonymous(v_hint_401_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__8);
v___x_464_ = l_Lean_MessageData_ofName(v_hint_401_);
v___x_465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___y_449_ = v___x_461_;
v___y_450_ = v___x_465_;
goto v___jp_448_;
}
else
{
lean_object* v___x_466_; 
lean_dec(v_hint_401_);
v___x_466_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__9);
v___y_449_ = v___x_461_;
v___y_450_ = v___x_466_;
goto v___jp_448_;
}
}
}
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec_ref_known(v_entry_411_, 1);
lean_dec(v_hint_401_);
lean_dec(v_mod_399_);
v___x_480_ = lean_box(0);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
v___jp_415_:
{
lean_object* v___x_417_; lean_object* v_toEnvExtension_418_; lean_object* v_env_419_; lean_object* v_nextMacroScope_420_; lean_object* v_ngen_421_; lean_object* v_auxDeclNGen_422_; lean_object* v_traceState_423_; lean_object* v_messages_424_; lean_object* v_infoState_425_; lean_object* v_snapshotTasks_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_439_; 
v___x_417_ = lean_st_ref_take(v___y_416_);
v_toEnvExtension_418_ = lean_ctor_get(v___x_412_, 0);
v_env_419_ = lean_ctor_get(v___x_417_, 0);
v_nextMacroScope_420_ = lean_ctor_get(v___x_417_, 1);
v_ngen_421_ = lean_ctor_get(v___x_417_, 2);
v_auxDeclNGen_422_ = lean_ctor_get(v___x_417_, 3);
v_traceState_423_ = lean_ctor_get(v___x_417_, 4);
v_messages_424_ = lean_ctor_get(v___x_417_, 6);
v_infoState_425_ = lean_ctor_get(v___x_417_, 7);
v_snapshotTasks_426_ = lean_ctor_get(v___x_417_, 8);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; 
v_unused_440_ = lean_ctor_get(v___x_417_, 5);
lean_dec(v_unused_440_);
v___x_428_ = v___x_417_;
v_isShared_429_ = v_isSharedCheck_439_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_snapshotTasks_426_);
lean_inc(v_infoState_425_);
lean_inc(v_messages_424_);
lean_inc(v_traceState_423_);
lean_inc(v_auxDeclNGen_422_);
lean_inc(v_ngen_421_);
lean_inc(v_nextMacroScope_420_);
lean_inc(v_env_419_);
lean_dec(v___x_417_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_439_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v_asyncMode_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
v_asyncMode_430_ = lean_ctor_get(v_toEnvExtension_418_, 2);
v___x_431_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_412_, v_env_419_, v_entry_411_, v_asyncMode_430_, v___x_414_);
v___x_432_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 5, v___x_432_);
lean_ctor_set(v___x_428_, 0, v___x_431_);
v___x_434_ = v___x_428_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_nextMacroScope_420_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_ngen_421_);
lean_ctor_set(v_reuseFailAlloc_438_, 3, v_auxDeclNGen_422_);
lean_ctor_set(v_reuseFailAlloc_438_, 4, v_traceState_423_);
lean_ctor_set(v_reuseFailAlloc_438_, 5, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_438_, 6, v_messages_424_);
lean_ctor_set(v_reuseFailAlloc_438_, 7, v_infoState_425_);
lean_ctor_set(v_reuseFailAlloc_438_, 8, v_snapshotTasks_426_);
v___x_434_ = v_reuseFailAlloc_438_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_st_ref_put(v___y_416_, v___x_434_);
v___x_436_ = lean_box(0);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___boxed(lean_object* v_mod_482_, lean_object* v_isMeta_483_, lean_object* v_hint_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
uint8_t v_isMeta_boxed_488_; lean_object* v_res_489_; 
v_isMeta_boxed_488_ = lean_unbox(v_isMeta_483_);
v_res_489_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5(v_mod_482_, v_isMeta_boxed_488_, v_hint_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__6(lean_object* v___x_490_, lean_object* v_declName_491_, lean_object* v_as_492_, size_t v_sz_493_, size_t v_i_494_, lean_object* v_b_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
uint8_t v___x_499_; 
v___x_499_ = lean_usize_dec_lt(v_i_494_, v_sz_493_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; 
lean_dec(v_declName_491_);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v_b_495_);
return v___x_500_;
}
else
{
lean_object* v___x_501_; lean_object* v_modules_502_; lean_object* v___x_503_; lean_object* v_a_504_; lean_object* v___x_505_; lean_object* v_toImport_506_; lean_object* v_module_507_; uint8_t v___x_508_; lean_object* v___x_509_; 
v___x_501_ = l_Lean_Environment_header(v___x_490_);
v_modules_502_ = lean_ctor_get(v___x_501_, 3);
lean_inc_ref(v_modules_502_);
lean_dec_ref(v___x_501_);
v___x_503_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_504_ = lean_array_uget_borrowed(v_as_492_, v_i_494_);
v___x_505_ = lean_array_get(v___x_503_, v_modules_502_, v_a_504_);
lean_dec_ref(v_modules_502_);
v_toImport_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc_ref(v_toImport_506_);
lean_dec(v___x_505_);
v_module_507_ = lean_ctor_get(v_toImport_506_, 0);
lean_inc(v_module_507_);
lean_dec_ref(v_toImport_506_);
v___x_508_ = 0;
lean_inc(v_declName_491_);
v___x_509_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5(v_module_507_, v___x_508_, v_declName_491_, v___y_496_, v___y_497_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v___x_510_; size_t v___x_511_; size_t v___x_512_; 
lean_dec_ref_known(v___x_509_, 1);
v___x_510_ = lean_box(0);
v___x_511_ = ((size_t)1ULL);
v___x_512_ = lean_usize_add(v_i_494_, v___x_511_);
v_i_494_ = v___x_512_;
v_b_495_ = v___x_510_;
goto _start;
}
else
{
lean_dec(v_declName_491_);
return v___x_509_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__6___boxed(lean_object* v___x_514_, lean_object* v_declName_515_, lean_object* v_as_516_, lean_object* v_sz_517_, lean_object* v_i_518_, lean_object* v_b_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
size_t v_sz_boxed_523_; size_t v_i_boxed_524_; lean_object* v_res_525_; 
v_sz_boxed_523_ = lean_unbox_usize(v_sz_517_);
lean_dec(v_sz_517_);
v_i_boxed_524_ = lean_unbox_usize(v_i_518_);
lean_dec(v_i_518_);
v_res_525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__6(v___x_514_, v_declName_515_, v_as_516_, v_sz_boxed_523_, v_i_boxed_524_, v_b_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec_ref(v_as_516_);
lean_dec_ref(v___x_514_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg(lean_object* v_a_526_, lean_object* v_x_527_){
_start:
{
if (lean_obj_tag(v_x_527_) == 0)
{
lean_object* v___x_528_; 
v___x_528_ = lean_box(0);
return v___x_528_;
}
else
{
lean_object* v_key_529_; lean_object* v_value_530_; lean_object* v_tail_531_; uint8_t v___x_532_; 
v_key_529_ = lean_ctor_get(v_x_527_, 0);
v_value_530_ = lean_ctor_get(v_x_527_, 1);
v_tail_531_ = lean_ctor_get(v_x_527_, 2);
v___x_532_ = lean_name_eq(v_key_529_, v_a_526_);
if (v___x_532_ == 0)
{
v_x_527_ = v_tail_531_;
goto _start;
}
else
{
lean_object* v___x_534_; 
lean_inc(v_value_530_);
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v_value_530_);
return v___x_534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg___boxed(lean_object* v_a_535_, lean_object* v_x_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg(v_a_535_, v_x_536_);
lean_dec(v_x_536_);
lean_dec(v_a_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg(lean_object* v_m_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_buckets_540_; lean_object* v___x_541_; uint64_t v___y_543_; 
v_buckets_540_ = lean_ctor_get(v_m_538_, 1);
v___x_541_ = lean_array_get_size(v_buckets_540_);
if (lean_obj_tag(v_a_539_) == 0)
{
uint64_t v___x_557_; 
v___x_557_ = 1723ULL;
v___y_543_ = v___x_557_;
goto v___jp_542_;
}
else
{
uint64_t v_hash_558_; 
v_hash_558_ = lean_ctor_get_uint64(v_a_539_, sizeof(void*)*2);
v___y_543_ = v_hash_558_;
goto v___jp_542_;
}
v___jp_542_:
{
uint64_t v___x_544_; uint64_t v___x_545_; uint64_t v_fold_546_; uint64_t v___x_547_; uint64_t v___x_548_; uint64_t v___x_549_; size_t v___x_550_; size_t v___x_551_; size_t v___x_552_; size_t v___x_553_; size_t v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_544_ = 32ULL;
v___x_545_ = lean_uint64_shift_right(v___y_543_, v___x_544_);
v_fold_546_ = lean_uint64_xor(v___y_543_, v___x_545_);
v___x_547_ = 16ULL;
v___x_548_ = lean_uint64_shift_right(v_fold_546_, v___x_547_);
v___x_549_ = lean_uint64_xor(v_fold_546_, v___x_548_);
v___x_550_ = lean_uint64_to_usize(v___x_549_);
v___x_551_ = lean_usize_of_nat(v___x_541_);
v___x_552_ = ((size_t)1ULL);
v___x_553_ = lean_usize_sub(v___x_551_, v___x_552_);
v___x_554_ = lean_usize_land(v___x_550_, v___x_553_);
v___x_555_ = lean_array_uget_borrowed(v_buckets_540_, v___x_554_);
v___x_556_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg(v_a_539_, v___x_555_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg___boxed(lean_object* v_m_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg(v_m_559_, v_a_560_);
lean_dec(v_a_560_);
lean_dec_ref(v_m_559_);
return v_res_561_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__2(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_564_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__1));
v___x_565_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__0));
v___x_566_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_565_, v___x_564_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2(lean_object* v_declName_569_, uint8_t v_isMeta_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; lean_object* v_env_578_; lean_object* v___y_580_; lean_object* v___x_593_; 
v___x_574_ = lean_st_ref_get(v___y_572_);
v_env_578_ = lean_ctor_get(v___x_574_, 0);
lean_inc_ref(v_env_578_);
lean_dec(v___x_574_);
v___x_593_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_578_, v_declName_569_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_dec_ref(v_env_578_);
lean_dec(v_declName_569_);
goto v___jp_575_;
}
else
{
lean_object* v_val_594_; lean_object* v___x_595_; lean_object* v_modules_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v_val_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_val_594_);
lean_dec_ref_known(v___x_593_, 1);
v___x_595_ = l_Lean_Environment_header(v_env_578_);
v_modules_596_ = lean_ctor_get(v___x_595_, 3);
lean_inc_ref(v_modules_596_);
lean_dec_ref(v___x_595_);
v___x_597_ = lean_array_get_size(v_modules_596_);
v___x_598_ = lean_nat_dec_lt(v_val_594_, v___x_597_);
if (v___x_598_ == 0)
{
lean_dec_ref(v_modules_596_);
lean_dec(v_val_594_);
lean_dec_ref(v_env_578_);
lean_dec(v_declName_569_);
goto v___jp_575_;
}
else
{
lean_object* v___x_599_; lean_object* v_env_600_; lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___y_604_; 
v___x_599_ = lean_st_ref_get(v___y_572_);
v_env_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc_ref(v_env_600_);
lean_dec(v___x_599_);
v___x_601_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__2);
v___x_602_ = lean_array_fget(v_modules_596_, v_val_594_);
lean_dec(v_val_594_);
lean_dec_ref(v_modules_596_);
if (v_isMeta_570_ == 0)
{
lean_dec_ref(v_env_600_);
v___y_604_ = v_isMeta_570_;
goto v___jp_603_;
}
else
{
uint8_t v___x_615_; 
lean_inc(v_declName_569_);
v___x_615_ = l_Lean_isMarkedMeta(v_env_600_, v_declName_569_);
if (v___x_615_ == 0)
{
v___y_604_ = v_isMeta_570_;
goto v___jp_603_;
}
else
{
uint8_t v___x_616_; 
v___x_616_ = 0;
v___y_604_ = v___x_616_;
goto v___jp_603_;
}
}
v___jp_603_:
{
lean_object* v_toImport_605_; lean_object* v_module_606_; lean_object* v___x_607_; 
v_toImport_605_ = lean_ctor_get(v___x_602_, 0);
lean_inc_ref(v_toImport_605_);
lean_dec(v___x_602_);
v_module_606_ = lean_ctor_get(v_toImport_605_, 0);
lean_inc(v_module_606_);
lean_dec_ref(v_toImport_605_);
lean_inc(v_declName_569_);
v___x_607_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5(v_module_606_, v___y_604_, v_declName_569_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
lean_dec_ref_known(v___x_607_, 1);
v___x_608_ = l_Lean_indirectModUseExt;
v___x_609_ = lean_box(1);
v___x_610_ = lean_box(0);
lean_inc_ref(v_env_578_);
v___x_611_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_601_, v___x_608_, v_env_578_, v___x_609_, v___x_610_);
v___x_612_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg(v___x_611_, v_declName_569_);
lean_dec(v___x_611_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v___x_613_; 
v___x_613_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__3));
v___y_580_ = v___x_613_;
goto v___jp_579_;
}
else
{
lean_object* v_val_614_; 
v_val_614_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_val_614_);
lean_dec_ref_known(v___x_612_, 1);
v___y_580_ = v_val_614_;
goto v___jp_579_;
}
}
else
{
lean_dec_ref(v_env_578_);
lean_dec(v_declName_569_);
return v___x_607_;
}
}
}
}
v___jp_575_:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_box(0);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
v___jp_579_:
{
lean_object* v___x_581_; size_t v_sz_582_; size_t v___x_583_; lean_object* v___x_584_; 
v___x_581_ = lean_box(0);
v_sz_582_ = lean_array_size(v___y_580_);
v___x_583_ = ((size_t)0ULL);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__6(v_env_578_, v_declName_569_, v___y_580_, v_sz_582_, v___x_583_, v___x_581_, v___y_571_, v___y_572_);
lean_dec_ref(v___y_580_);
lean_dec_ref(v_env_578_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v___x_584_, 0);
lean_dec(v_unused_592_);
v___x_586_ = v___x_584_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_dec(v___x_584_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_581_);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_581_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
return v___x_584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___boxed(lean_object* v_declName_617_, lean_object* v_isMeta_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
uint8_t v_isMeta_boxed_622_; lean_object* v_res_623_; 
v_isMeta_boxed_622_ = lean_unbox(v_isMeta_618_);
v_res_623_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2(v_declName_617_, v_isMeta_boxed_622_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__3(lean_object* v_a_624_, lean_object* v_decl_625_, lean_object* v_stx_626_, uint8_t v_x_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_st_ref_get(v___y_629_);
v___x_632_ = l_Lean_Attribute_Builtin_getIdent(v_stx_626_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_634_ = lean_box(0);
v___x_635_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_633_, v___x_634_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; uint8_t v___x_637_; lean_object* v___x_638_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc_n(v_a_636_, 2);
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = 0;
v___x_638_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2(v_a_636_, v___x_637_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_toEnvExtension_639_; lean_object* v_env_640_; lean_object* v_asyncMode_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec_ref_known(v___x_638_, 1);
v_toEnvExtension_639_ = lean_ctor_get(v_a_624_, 0);
v_env_640_ = lean_ctor_get(v___x_631_, 0);
lean_inc_ref(v_env_640_);
lean_dec(v___x_631_);
v_asyncMode_641_ = lean_ctor_get(v_toEnvExtension_639_, 2);
lean_inc(v_asyncMode_641_);
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v_a_636_);
lean_ctor_set(v___x_642_, 1, v_decl_625_);
v___x_643_ = lean_box(0);
v___x_644_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_624_, v_env_640_, v___x_642_, v_asyncMode_641_, v___x_643_);
lean_dec(v_asyncMode_641_);
v___x_645_ = l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg(v___x_644_, v___y_629_);
return v___x_645_;
}
else
{
lean_dec(v_a_636_);
lean_dec(v___x_631_);
lean_dec(v_decl_625_);
lean_dec_ref(v_a_624_);
return v___x_638_;
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v___x_631_);
lean_dec(v_decl_625_);
lean_dec_ref(v_a_624_);
v_a_646_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_635_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_635_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
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
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec(v___x_631_);
lean_dec(v_decl_625_);
lean_dec_ref(v_a_624_);
v_a_654_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_632_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_632_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__3___boxed(lean_object* v_a_662_, lean_object* v_decl_663_, lean_object* v_stx_664_, lean_object* v_x_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
uint8_t v_x_5683__boxed_669_; lean_object* v_res_670_; 
v_x_5683__boxed_669_ = lean_unbox(v_x_665_);
v_res_670_ = l_Lean_ParserCompiler_registerCombinatorAttribute___lam__3(v_a_662_, v_decl_663_, v_stx_664_, v_x_5683__boxed_669_, v___y_666_, v___y_667_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__2(lean_object* v_as_671_, size_t v_i_672_, size_t v_stop_673_, lean_object* v_b_674_){
_start:
{
uint8_t v___x_675_; 
v___x_675_ = lean_usize_dec_eq(v_i_672_, v_stop_673_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v_fst_677_; lean_object* v_snd_678_; lean_object* v___x_679_; size_t v___x_680_; size_t v___x_681_; 
v___x_676_ = lean_array_uget_borrowed(v_as_671_, v_i_672_);
v_fst_677_ = lean_ctor_get(v___x_676_, 0);
v_snd_678_ = lean_ctor_get(v___x_676_, 1);
lean_inc(v_snd_678_);
lean_inc(v_fst_677_);
v___x_679_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_677_, v_snd_678_, v_b_674_);
v___x_680_ = ((size_t)1ULL);
v___x_681_ = lean_usize_add(v_i_672_, v___x_680_);
v_i_672_ = v___x_681_;
v_b_674_ = v___x_679_;
goto _start;
}
else
{
return v_b_674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__2___boxed(lean_object* v_as_683_, lean_object* v_i_684_, lean_object* v_stop_685_, lean_object* v_b_686_){
_start:
{
size_t v_i_boxed_687_; size_t v_stop_boxed_688_; lean_object* v_res_689_; 
v_i_boxed_687_ = lean_unbox_usize(v_i_684_);
lean_dec(v_i_684_);
v_stop_boxed_688_ = lean_unbox_usize(v_stop_685_);
lean_dec(v_stop_685_);
v_res_689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__2(v_as_683_, v_i_boxed_687_, v_stop_boxed_688_, v_b_686_);
lean_dec_ref(v_as_683_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__3(lean_object* v_as_690_, size_t v_i_691_, size_t v_stop_692_, lean_object* v_b_693_){
_start:
{
lean_object* v___y_695_; uint8_t v___x_699_; 
v___x_699_ = lean_usize_dec_eq(v_i_691_, v_stop_692_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_700_ = lean_array_uget_borrowed(v_as_690_, v_i_691_);
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = lean_array_get_size(v___x_700_);
v___x_703_ = lean_nat_dec_lt(v___x_701_, v___x_702_);
if (v___x_703_ == 0)
{
v___y_695_ = v_b_693_;
goto v___jp_694_;
}
else
{
size_t v___x_704_; size_t v___x_705_; lean_object* v___x_706_; 
v___x_704_ = ((size_t)0ULL);
v___x_705_ = lean_usize_of_nat(v___x_702_);
v___x_706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__2(v___x_700_, v___x_704_, v___x_705_, v_b_693_);
v___y_695_ = v___x_706_;
goto v___jp_694_;
}
}
else
{
return v_b_693_;
}
v___jp_694_:
{
size_t v___x_696_; size_t v___x_697_; 
v___x_696_ = ((size_t)1ULL);
v___x_697_ = lean_usize_add(v_i_691_, v___x_696_);
v_i_691_ = v___x_697_;
v_b_693_ = v___y_695_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__3___boxed(lean_object* v_as_707_, lean_object* v_i_708_, lean_object* v_stop_709_, lean_object* v_b_710_){
_start:
{
size_t v_i_boxed_711_; size_t v_stop_boxed_712_; lean_object* v_res_713_; 
v_i_boxed_711_ = lean_unbox_usize(v_i_708_);
lean_dec(v_i_708_);
v_stop_boxed_712_ = lean_unbox_usize(v_stop_709_);
lean_dec(v_stop_709_);
v_res_713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__3(v_as_707_, v_i_boxed_711_, v_stop_boxed_712_, v_b_710_);
lean_dec_ref(v_as_707_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1(lean_object* v_initState_714_, lean_object* v_as_715_){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = lean_array_get_size(v_as_715_);
v___x_718_ = lean_nat_dec_lt(v___x_716_, v___x_717_);
if (v___x_718_ == 0)
{
return v_initState_714_;
}
else
{
size_t v___x_719_; size_t v___x_720_; lean_object* v___x_721_; 
v___x_719_ = ((size_t)0ULL);
v___x_720_ = lean_usize_of_nat(v___x_717_);
v___x_721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__3(v_as_715_, v___x_719_, v___x_720_, v_initState_714_);
return v___x_721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1___boxed(lean_object* v_initState_722_, lean_object* v_as_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1(v_initState_722_, v_as_723_);
lean_dec_ref(v_as_723_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute(lean_object* v_name_729_, lean_object* v_descr_730_, lean_object* v_ref_731_){
_start:
{
lean_object* v___f_733_; lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___f_733_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___closed__0));
v___f_734_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___closed__1));
v___x_735_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___closed__2));
v___x_736_ = lean_box(0);
v___x_737_ = lean_box(2);
lean_inc(v_ref_731_);
v___x_738_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_738_, 0, v_ref_731_);
lean_ctor_set(v___x_738_, 1, v___f_734_);
lean_ctor_set(v___x_738_, 2, v___x_735_);
lean_ctor_set(v___x_738_, 3, v___f_733_);
lean_ctor_set(v___x_738_, 4, v___x_736_);
lean_ctor_set(v___x_738_, 5, v___x_737_);
lean_ctor_set(v___x_738_, 6, v___x_736_);
v___x_739_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_738_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___f_741_; lean_object* v___f_742_; uint8_t v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc_n(v_a_740_, 2);
lean_dec_ref_known(v___x_739_, 1);
lean_inc(v_name_729_);
v___f_741_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2___boxed), 5, 1);
lean_closure_set(v___f_741_, 0, v_name_729_);
v___f_742_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerCombinatorAttribute___lam__3___boxed), 7, 1);
lean_closure_set(v___f_742_, 0, v_a_740_);
v___x_743_ = 0;
v___x_744_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_744_, 0, v_ref_731_);
lean_ctor_set(v___x_744_, 1, v_name_729_);
lean_ctor_set(v___x_744_, 2, v_descr_730_);
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*3, v___x_743_);
v___x_745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
lean_ctor_set(v___x_745_, 1, v___f_742_);
lean_ctor_set(v___x_745_, 2, v___f_741_);
lean_inc_ref(v___x_745_);
v___x_746_ = l_Lean_registerBuiltinAttribute(v___x_745_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_754_; 
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v___x_746_, 0);
lean_dec(v_unused_755_);
v___x_748_ = v___x_746_;
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
else
{
lean_dec(v___x_746_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_745_);
lean_ctor_set(v___x_750_, 1, v_a_740_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref_known(v___x_745_, 3);
lean_dec(v_a_740_);
v_a_756_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_746_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_746_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
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
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec(v_ref_731_);
lean_dec_ref(v_descr_730_);
lean_dec(v_name_729_);
v_a_764_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_739_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_739_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___boxed(lean_object* v_name_772_, lean_object* v_descr_773_, lean_object* v_ref_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_ParserCompiler_registerCombinatorAttribute(v_name_772_, v_descr_773_, v_ref_774_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0(lean_object* v_00_u03b1_777_, lean_object* v_msg_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(v_msg_778_, v___y_779_, v___y_780_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___boxed(lean_object* v_00_u03b1_783_, lean_object* v_msg_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0(v_00_u03b1_783_, v_msg_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7(lean_object* v_00_u03b2_789_, lean_object* v_m_790_, lean_object* v_a_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg(v_m_790_, v_a_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___boxed(lean_object* v_00_u03b2_793_, lean_object* v_m_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7(v_00_u03b2_793_, v_m_794_, v_a_795_);
lean_dec(v_a_795_);
lean_dec_ref(v_m_794_);
return v_res_796_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
uint8_t v___x_800_; 
v___x_800_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___redArg(v_x_798_, v_x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b2_801_, lean_object* v_x_802_, lean_object* v_x_803_){
_start:
{
uint8_t v_res_804_; lean_object* v_r_805_; 
v_res_804_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7(v_00_u03b2_801_, v_x_802_, v_x_803_);
lean_dec_ref(v_x_803_);
lean_dec_ref(v_x_802_);
v_r_805_ = lean_box(v_res_804_);
return v_r_805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11(lean_object* v_00_u03b2_806_, lean_object* v_a_807_, lean_object* v_x_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg(v_a_807_, v_x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___boxed(lean_object* v_00_u03b2_810_, lean_object* v_a_811_, lean_object* v_x_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11(v_00_u03b2_810_, v_a_811_, v_x_812_);
lean_dec(v_x_812_);
lean_dec(v_a_811_);
return v_res_813_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_814_, lean_object* v_x_815_, size_t v_x_816_, lean_object* v_x_817_){
_start:
{
uint8_t v___x_818_; 
v___x_818_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg(v_x_815_, v_x_816_, v_x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_00_u03b2_819_, lean_object* v_x_820_, lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
size_t v_x_5925__boxed_823_; uint8_t v_res_824_; lean_object* v_r_825_; 
v_x_5925__boxed_823_ = lean_unbox_usize(v_x_821_);
lean_dec(v_x_821_);
v_res_824_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8(v_00_u03b2_819_, v_x_820_, v_x_5925__boxed_823_, v_x_822_);
lean_dec_ref(v_x_822_);
lean_dec_ref(v_x_820_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11(lean_object* v_00_u03b2_826_, lean_object* v_keys_827_, lean_object* v_vals_828_, lean_object* v_heq_829_, lean_object* v_i_830_, lean_object* v_k_831_){
_start:
{
uint8_t v___x_832_; 
v___x_832_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___redArg(v_keys_827_, v_i_830_, v_k_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03b2_833_, lean_object* v_keys_834_, lean_object* v_vals_835_, lean_object* v_heq_836_, lean_object* v_i_837_, lean_object* v_k_838_){
_start:
{
uint8_t v_res_839_; lean_object* v_r_840_; 
v_res_839_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11(v_00_u03b2_833_, v_keys_834_, v_vals_835_, v_heq_836_, v_i_837_, v_k_838_);
lean_dec_ref(v_k_838_);
lean_dec_ref(v_vals_835_);
lean_dec_ref(v_keys_834_);
v_r_840_ = lean_box(v_res_839_);
return v_r_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(lean_object* v_attr_841_, lean_object* v_env_842_, lean_object* v_parserDecl_843_){
_start:
{
lean_object* v_ext_844_; lean_object* v_toEnvExtension_845_; lean_object* v_asyncMode_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_ext_844_ = lean_ctor_get(v_attr_841_, 1);
v_toEnvExtension_845_ = lean_ctor_get(v_ext_844_, 0);
v_asyncMode_846_ = lean_ctor_get(v_toEnvExtension_845_, 2);
v___x_847_ = lean_box(1);
v___x_848_ = lean_box(0);
v___x_849_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_847_, v_ext_844_, v_env_842_, v_asyncMode_846_, v___x_848_);
v___x_850_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_849_, v_parserDecl_843_);
lean_dec(v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f___boxed(lean_object* v_attr_851_, lean_object* v_env_852_, lean_object* v_parserDecl_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(v_attr_851_, v_env_852_, v_parserDecl_853_);
lean_dec(v_parserDecl_853_);
lean_dec_ref(v_attr_851_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(lean_object* v_attr_855_, lean_object* v_env_856_, lean_object* v_parserDecl_857_, lean_object* v_decl_858_){
_start:
{
lean_object* v_ext_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_870_; 
v_ext_859_ = lean_ctor_get(v_attr_855_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v_attr_855_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v_attr_855_, 0);
lean_dec(v_unused_871_);
v___x_861_ = v_attr_855_;
v_isShared_862_ = v_isSharedCheck_870_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_ext_859_);
lean_dec(v_attr_855_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_870_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_toEnvExtension_863_; lean_object* v_asyncMode_864_; lean_object* v___x_866_; 
v_toEnvExtension_863_ = lean_ctor_get(v_ext_859_, 0);
v_asyncMode_864_ = lean_ctor_get(v_toEnvExtension_863_, 2);
lean_inc(v_asyncMode_864_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 1, v_decl_858_);
lean_ctor_set(v___x_861_, 0, v_parserDecl_857_);
v___x_866_ = v___x_861_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_parserDecl_857_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_decl_858_);
v___x_866_ = v_reuseFailAlloc_869_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = lean_box(0);
v___x_868_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_859_, v_env_856_, v___x_866_, v_asyncMode_864_, v___x_867_);
lean_dec(v_asyncMode_864_);
return v___x_868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg(lean_object* v_x_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
if (lean_obj_tag(v_x_872_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_a_876_ = lean_ctor_get(v_x_872_, 0);
lean_inc(v_a_876_);
lean_dec_ref_known(v_x_872_, 1);
v___x_877_ = l_Lean_stringToMessageData(v_a_876_);
v___x_878_ = l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(v___x_877_, v___y_873_, v___y_874_);
return v___x_878_;
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_a_879_ = lean_ctor_get(v_x_872_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v_x_872_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v_x_872_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v_x_872_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
lean_ctor_set_tag(v___x_881_, 0);
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg___boxed(lean_object* v_x_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg(v_x_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
return v_res_891_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_box(0);
v___x_893_ = l_Lean_Elab_abortCommandExceptionId;
v___x_894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v___x_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___closed__0);
v___x_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___boxed(lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg();
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___redArg(lean_object* v_constName_900_, uint8_t v_checkMeta_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v___x_905_; lean_object* v_env_906_; uint8_t v___x_907_; 
v___x_905_ = lean_st_ref_get(v___y_903_);
v_env_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc_ref(v_env_906_);
lean_dec(v___x_905_);
lean_inc(v_constName_900_);
v___x_907_ = lean_has_compile_error(v_env_906_, v_constName_900_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; lean_object* v_env_909_; lean_object* v_options_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_908_ = lean_st_ref_get(v___y_903_);
v_env_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc_ref(v_env_909_);
lean_dec(v___x_908_);
v_options_910_ = lean_ctor_get(v___y_902_, 1);
v___x_911_ = l_Lean_Environment_evalConst___redArg(v_env_909_, v_options_910_, v_constName_900_, v_checkMeta_901_);
lean_dec(v_constName_900_);
lean_dec_ref(v_env_909_);
v___x_912_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg(v___x_911_, v___y_902_, v___y_903_);
return v___x_912_;
}
else
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v___x_914_; lean_object* v_env_915_; lean_object* v_options_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec_ref_known(v___x_913_, 1);
v___x_914_ = lean_st_ref_get(v___y_903_);
v_env_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc_ref(v_env_915_);
lean_dec(v___x_914_);
v_options_916_ = lean_ctor_get(v___y_902_, 1);
v___x_917_ = l_Lean_Environment_evalConst___redArg(v_env_915_, v_options_916_, v_constName_900_, v_checkMeta_901_);
lean_dec(v_constName_900_);
lean_dec_ref(v_env_915_);
v___x_918_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg(v___x_917_, v___y_902_, v___y_903_);
return v___x_918_;
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec(v_constName_900_);
v_a_919_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_913_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_913_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___redArg___boxed(lean_object* v_constName_927_, lean_object* v_checkMeta_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
uint8_t v_checkMeta_boxed_932_; lean_object* v_res_933_; 
v_checkMeta_boxed_932_ = lean_unbox(v_checkMeta_928_);
v_res_933_ = l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___redArg(v_constName_927_, v_checkMeta_boxed_932_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
return v_res_933_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__1(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = ((lean_object*)(l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__0));
v___x_936_ = l_Lean_stringToMessageData(v___x_935_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__3(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = ((lean_object*)(l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__2));
v___x_939_ = l_Lean_stringToMessageData(v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__5(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = ((lean_object*)(l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__4));
v___x_942_ = l_Lean_stringToMessageData(v___x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(lean_object* v_attr_943_, lean_object* v_parserDecl_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_948_; lean_object* v_env_949_; lean_object* v___x_950_; 
v___x_948_ = lean_st_ref_get(v_a_946_);
v_env_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc_ref(v_env_949_);
lean_dec(v___x_948_);
v___x_950_ = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(v_attr_943_, v_env_949_, v_parserDecl_944_);
if (lean_obj_tag(v___x_950_) == 1)
{
lean_object* v_val_951_; uint8_t v___x_952_; lean_object* v___x_953_; 
lean_dec(v_parserDecl_944_);
lean_dec_ref(v_attr_943_);
v_val_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_val_951_);
lean_dec_ref_known(v___x_950_, 1);
v___x_952_ = 1;
v___x_953_ = l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___redArg(v_val_951_, v___x_952_, v_a_945_, v_a_946_);
return v___x_953_;
}
else
{
lean_object* v_impl_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_972_; 
lean_dec(v___x_950_);
v_impl_954_ = lean_ctor_get(v_attr_943_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v_attr_943_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; 
v_unused_973_ = lean_ctor_get(v_attr_943_, 1);
lean_dec(v_unused_973_);
v___x_956_ = v_attr_943_;
v_isShared_957_ = v_isSharedCheck_972_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_impl_954_);
lean_dec(v_attr_943_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_972_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_toAttributeImplCore_958_; lean_object* v_name_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v_toAttributeImplCore_958_ = lean_ctor_get(v_impl_954_, 0);
lean_inc_ref(v_toAttributeImplCore_958_);
lean_dec_ref(v_impl_954_);
v_name_959_ = lean_ctor_get(v_toAttributeImplCore_958_, 1);
lean_inc(v_name_959_);
lean_dec_ref(v_toAttributeImplCore_958_);
v___x_960_ = lean_obj_once(&l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__1, &l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__1_once, _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__1);
v___x_961_ = l_Lean_MessageData_ofName(v_name_959_);
if (v_isShared_957_ == 0)
{
lean_ctor_set_tag(v___x_956_, 7);
lean_ctor_set(v___x_956_, 1, v___x_961_);
lean_ctor_set(v___x_956_, 0, v___x_960_);
v___x_963_ = v___x_956_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v___x_961_);
v___x_963_ = v_reuseFailAlloc_971_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_964_ = lean_obj_once(&l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__3, &l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__3_once, _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__3);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = l_Lean_MessageData_ofName(v_parserDecl_944_);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = lean_obj_once(&l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__5, &l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__5_once, _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__5);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(v___x_969_, v_a_945_, v_a_946_);
return v___x_970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___boxed(lean_object* v_attr_974_, lean_object* v_parserDecl_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(v_attr_974_, v_parserDecl_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor(lean_object* v_00_u03b1_980_, lean_object* v_attr_981_, lean_object* v_parserDecl_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(v_attr_981_, v_parserDecl_982_, v_a_983_, v_a_984_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___boxed(lean_object* v_00_u03b1_987_, lean_object* v_attr_988_, lean_object* v_parserDecl_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor(v_00_u03b1_987_, v_attr_988_, v_parserDecl_989_, v_a_990_, v_a_991_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1(lean_object* v_00_u03b1_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg();
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___boxed(lean_object* v_00_u03b1_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1(v_00_u03b1_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0(lean_object* v_00_u03b1_1004_, lean_object* v_constName_1005_, uint8_t v_checkMeta_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___redArg(v_constName_1005_, v_checkMeta_1006_, v___y_1007_, v___y_1008_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___boxed(lean_object* v_00_u03b1_1011_, lean_object* v_constName_1012_, lean_object* v_checkMeta_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
uint8_t v_checkMeta_boxed_1017_; lean_object* v_res_1018_; 
v_checkMeta_boxed_1017_ = lean_unbox(v_checkMeta_1013_);
v_res_1018_ = l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0(v_00_u03b1_1011_, v_constName_1012_, v_checkMeta_boxed_1017_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0(lean_object* v_00_u03b1_1019_, lean_object* v_x_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg(v_x_1020_, v___y_1021_, v___y_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1025_, lean_object* v_x_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0(v_00_u03b1_1025_, v_x_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
return v_res_1030_;
}
}
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ParserCompiler_Attribute(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default = _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default();
lean_mark_persistent(l_Lean_ParserCompiler_instInhabitedCombinatorAttribute_default);
l_Lean_ParserCompiler_instInhabitedCombinatorAttribute = _init_l_Lean_ParserCompiler_instInhabitedCombinatorAttribute();
lean_mark_persistent(l_Lean_ParserCompiler_instInhabitedCombinatorAttribute);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_ParserCompiler_Attribute(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1 = _init_l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1();
lean_mark_persistent(l_Lean_ParserCompiler_registerCombinatorAttribute___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ParserCompiler_Attribute(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ParserCompiler_Attribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_ParserCompiler_Attribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_ParserCompiler_Attribute(builtin);
}
#ifdef __cplusplus
}
#endif
