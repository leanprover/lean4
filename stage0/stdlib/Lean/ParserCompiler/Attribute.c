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
lean_object* l_Lean_instInhabitedEnvExtension_default___redArg();
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__0 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__1;
static const lean_string_object l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__2 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__3(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__0;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__1_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__2_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__3_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__7;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__8_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_ParserCompiler_registerCombinatorAttribute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ParserCompiler_registerCombinatorAttribute___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___closed__0 = (const lean_object*)&l_Lean_ParserCompiler_registerCombinatorAttribute___closed__0_value;
static const lean_closure_object l_Lean_ParserCompiler_registerCombinatorAttribute___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
v___x_36_ = l_Lean_instInhabitedEnvExtension_default___redArg();
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
v___x_126_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_134_; lean_object* v_nextMacroScope_135_; lean_object* v_ngen_136_; lean_object* v_auxDeclNGen_137_; lean_object* v_traceState_138_; lean_object* v_recordedDeps_139_; lean_object* v_messages_140_; lean_object* v_infoState_141_; lean_object* v_snapshotTasks_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_153_; 
v___x_134_ = lean_st_ref_take(v___y_132_);
v_nextMacroScope_135_ = lean_ctor_get(v___x_134_, 1);
v_ngen_136_ = lean_ctor_get(v___x_134_, 2);
v_auxDeclNGen_137_ = lean_ctor_get(v___x_134_, 3);
v_traceState_138_ = lean_ctor_get(v___x_134_, 4);
v_recordedDeps_139_ = lean_ctor_get(v___x_134_, 6);
v_messages_140_ = lean_ctor_get(v___x_134_, 7);
v_infoState_141_ = lean_ctor_get(v___x_134_, 8);
v_snapshotTasks_142_ = lean_ctor_get(v___x_134_, 9);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_153_ == 0)
{
lean_object* v_unused_154_; lean_object* v_unused_155_; 
v_unused_154_ = lean_ctor_get(v___x_134_, 5);
lean_dec(v_unused_154_);
v_unused_155_ = lean_ctor_get(v___x_134_, 0);
lean_dec(v_unused_155_);
v___x_144_ = v___x_134_;
v_isShared_145_ = v_isSharedCheck_153_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_snapshotTasks_142_);
lean_inc(v_infoState_141_);
lean_inc(v_messages_140_);
lean_inc(v_recordedDeps_139_);
lean_inc(v_traceState_138_);
lean_inc(v_auxDeclNGen_137_);
lean_inc(v_ngen_136_);
lean_inc(v_nextMacroScope_135_);
lean_dec(v___x_134_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_153_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_146_ = lean_box(0);
v___x_147_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 5, v___x_147_);
lean_ctor_set(v___x_144_, 0, v_env_131_);
v___x_149_ = v___x_144_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_env_131_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_nextMacroScope_135_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_ngen_136_);
lean_ctor_set(v_reuseFailAlloc_152_, 3, v_auxDeclNGen_137_);
lean_ctor_set(v_reuseFailAlloc_152_, 4, v_traceState_138_);
lean_ctor_set(v_reuseFailAlloc_152_, 5, v___x_147_);
lean_ctor_set(v_reuseFailAlloc_152_, 6, v_recordedDeps_139_);
lean_ctor_set(v_reuseFailAlloc_152_, 7, v_messages_140_);
lean_ctor_set(v_reuseFailAlloc_152_, 8, v_infoState_141_);
lean_ctor_set(v_reuseFailAlloc_152_, 9, v_snapshotTasks_142_);
v___x_149_ = v_reuseFailAlloc_152_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_st_ref_put(v___y_132_, v___x_149_);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_146_);
return v___x_151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___boxed(lean_object* v_env_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg(v_env_156_, v___y_157_);
lean_dec(v___y_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3(lean_object* v_env_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg(v_env_160_, v___y_162_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___boxed(lean_object* v_env_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3(v_env_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
return v_res_169_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__0, &l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__0);
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_173_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0);
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
lean_ctor_set(v___x_175_, 2, v___x_174_);
lean_ctor_set(v___x_175_, 3, v___x_174_);
lean_ctor_set(v___x_175_, 4, v___x_173_);
lean_ctor_set(v___x_175_, 5, v___x_173_);
lean_ctor_set(v___x_175_, 6, v___x_173_);
lean_ctor_set(v___x_175_, 7, v___x_173_);
lean_ctor_set(v___x_175_, 8, v___x_173_);
lean_ctor_set(v___x_175_, 9, v___x_173_);
lean_ctor_set(v___x_175_, 10, v___x_173_);
lean_ctor_set(v___x_175_, 11, v___x_172_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_unsigned_to_nat(32u);
v___x_177_ = lean_mk_empty_array_with_capacity(v___x_176_);
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_179_ = ((size_t)5ULL);
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = lean_unsigned_to_nat(32u);
v___x_182_ = lean_mk_empty_array_with_capacity(v___x_181_);
v___x_183_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__2);
v___x_184_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
lean_ctor_set(v___x_184_, 2, v___x_180_);
lean_ctor_set(v___x_184_, 3, v___x_180_);
lean_ctor_set_usize(v___x_184_, 4, v___x_179_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_185_ = lean_box(1);
v___x_186_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__3);
v___x_187_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__0);
v___x_188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
lean_ctor_set(v___x_188_, 2, v___x_185_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0(lean_object* v_msgData_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; lean_object* v_toCold_194_; lean_object* v_env_195_; lean_object* v_options_196_; uint8_t v___x_197_; lean_object* v_env_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_193_ = lean_st_ref_get(v___y_191_);
v_toCold_194_ = lean_ctor_get(v___y_190_, 0);
v_env_195_ = lean_ctor_get(v___x_193_, 0);
lean_inc_ref(v_env_195_);
lean_dec(v___x_193_);
v_options_196_ = lean_ctor_get(v_toCold_194_, 2);
v___x_197_ = 0;
v_env_198_ = l_Lean_Environment_setRecordingDeps(v_env_195_, v___x_197_);
v___x_199_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__1);
v___x_200_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___closed__4);
lean_inc_ref(v_options_196_);
v___x_201_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_201_, 0, v_env_198_);
lean_ctor_set(v___x_201_, 1, v___x_199_);
lean_ctor_set(v___x_201_, 2, v___x_200_);
lean_ctor_set(v___x_201_, 3, v_options_196_);
v___x_202_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v_msgData_189_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0___boxed(lean_object* v_msgData_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0(v_msgData_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(lean_object* v_msg_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_ref_213_; lean_object* v___x_214_; lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_223_; 
v_ref_213_ = lean_ctor_get(v___y_210_, 2);
v___x_214_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0(v_msg_209_, v___y_210_, v___y_211_);
v_a_215_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_223_ == 0)
{
v___x_217_ = v___x_214_;
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
lean_inc(v_ref_213_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v_ref_213_);
lean_ctor_set(v___x_219_, 1, v_a_215_);
if (v_isShared_218_ == 0)
{
lean_ctor_set_tag(v___x_217_, 1);
lean_ctor_set(v___x_217_, 0, v___x_219_);
v___x_221_ = v___x_217_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg___boxed(lean_object* v_msg_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(v_msg_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
return v_res_228_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__1(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__0));
v___x_231_ = l_Lean_stringToMessageData(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__3(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__2));
v___x_234_ = l_Lean_stringToMessageData(v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0(lean_object* v_name_235_, lean_object* v_decl_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_240_ = lean_obj_once(&l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__1, &l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__1_once, _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__1);
v___x_241_ = l_Lean_MessageData_ofName(v_name_235_);
v___x_242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = lean_obj_once(&l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__3, &l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__3_once, _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___closed__3);
v___x_244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(v___x_244_, v___y_237_, v___y_238_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___boxed(lean_object* v_name_246_, lean_object* v_decl_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0(v_name_246_, v_decl_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v_decl_247_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__1(lean_object* v_es_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lean_array_mk(v_es_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__2(lean_object* v_s_254_, lean_object* v_p_255_){
_start:
{
lean_object* v_fst_256_; lean_object* v_snd_257_; lean_object* v___x_258_; 
v_fst_256_ = lean_ctor_get(v_p_255_, 0);
lean_inc(v_fst_256_);
v_snd_257_ = lean_ctor_get(v_p_255_, 1);
lean_inc(v_snd_257_);
lean_dec_ref(v_p_255_);
v___x_258_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_256_, v_snd_257_, v_s_254_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__3(lean_object* v_addEntryFn_259_, lean_object* v___x_260_, lean_object* v_s_261_){
_start:
{
lean_object* v_importedEntries_262_; lean_object* v_state_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_271_; 
v_importedEntries_262_ = lean_ctor_get(v_s_261_, 0);
v_state_263_ = lean_ctor_get(v_s_261_, 1);
v_isSharedCheck_271_ = !lean_is_exclusive(v_s_261_);
if (v_isSharedCheck_271_ == 0)
{
v___x_265_ = v_s_261_;
v_isShared_266_ = v_isSharedCheck_271_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_state_263_);
lean_inc(v_importedEntries_262_);
lean_dec(v_s_261_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_271_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v_state_267_; lean_object* v___x_269_; 
v_state_267_ = lean_apply_2(v_addEntryFn_259_, v_state_263_, v___x_260_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v_state_267_);
v___x_269_ = v___x_265_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_importedEntries_262_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_state_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__0(void){
_start:
{
lean_object* v___x_272_; double v___x_273_; 
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_float_of_nat(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8(lean_object* v_cls_277_, lean_object* v_msg_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_ref_282_; lean_object* v___x_283_; lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_329_; 
v_ref_282_ = lean_ctor_get(v___y_279_, 2);
v___x_283_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0_spec__0(v_msg_278_, v___y_279_, v___y_280_);
v_a_284_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_329_ == 0)
{
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_329_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_329_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v_traceState_289_; lean_object* v_env_290_; lean_object* v_nextMacroScope_291_; lean_object* v_ngen_292_; lean_object* v_auxDeclNGen_293_; lean_object* v_cache_294_; lean_object* v_recordedDeps_295_; lean_object* v_messages_296_; lean_object* v_infoState_297_; lean_object* v_snapshotTasks_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_328_; 
v___x_288_ = lean_st_ref_take(v___y_280_);
v_traceState_289_ = lean_ctor_get(v___x_288_, 4);
v_env_290_ = lean_ctor_get(v___x_288_, 0);
v_nextMacroScope_291_ = lean_ctor_get(v___x_288_, 1);
v_ngen_292_ = lean_ctor_get(v___x_288_, 2);
v_auxDeclNGen_293_ = lean_ctor_get(v___x_288_, 3);
v_cache_294_ = lean_ctor_get(v___x_288_, 5);
v_recordedDeps_295_ = lean_ctor_get(v___x_288_, 6);
v_messages_296_ = lean_ctor_get(v___x_288_, 7);
v_infoState_297_ = lean_ctor_get(v___x_288_, 8);
v_snapshotTasks_298_ = lean_ctor_get(v___x_288_, 9);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_328_ == 0)
{
v___x_300_ = v___x_288_;
v_isShared_301_ = v_isSharedCheck_328_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_snapshotTasks_298_);
lean_inc(v_infoState_297_);
lean_inc(v_messages_296_);
lean_inc(v_recordedDeps_295_);
lean_inc(v_cache_294_);
lean_inc(v_traceState_289_);
lean_inc(v_auxDeclNGen_293_);
lean_inc(v_ngen_292_);
lean_inc(v_nextMacroScope_291_);
lean_inc(v_env_290_);
lean_dec(v___x_288_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_328_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
uint64_t v_tid_302_; lean_object* v_traces_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_327_; 
v_tid_302_ = lean_ctor_get_uint64(v_traceState_289_, sizeof(void*)*1);
v_traces_303_ = lean_ctor_get(v_traceState_289_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v_traceState_289_);
if (v_isSharedCheck_327_ == 0)
{
v___x_305_ = v_traceState_289_;
v_isShared_306_ = v_isSharedCheck_327_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_traces_303_);
lean_dec(v_traceState_289_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_327_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; double v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_307_ = lean_box(0);
v___x_308_ = lean_box(0);
v___x_309_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__0);
v___x_310_ = 0;
v___x_311_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__1));
v___x_312_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_312_, 0, v_cls_277_);
lean_ctor_set(v___x_312_, 1, v___x_308_);
lean_ctor_set(v___x_312_, 2, v___x_311_);
lean_ctor_set_float(v___x_312_, sizeof(void*)*3, v___x_309_);
lean_ctor_set_float(v___x_312_, sizeof(void*)*3 + 8, v___x_309_);
lean_ctor_set_uint8(v___x_312_, sizeof(void*)*3 + 16, v___x_310_);
v___x_313_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__2));
v___x_314_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v_a_284_);
lean_ctor_set(v___x_314_, 2, v___x_313_);
lean_inc(v_ref_282_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v_ref_282_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = l_Lean_PersistentArray_push___redArg(v_traces_303_, v___x_315_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_316_);
v___x_318_ = v___x_305_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_316_);
lean_ctor_set_uint64(v_reuseFailAlloc_326_, sizeof(void*)*1, v_tid_302_);
v___x_318_ = v_reuseFailAlloc_326_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_320_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 4, v___x_318_);
v___x_320_ = v___x_300_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_env_290_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_nextMacroScope_291_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v_ngen_292_);
lean_ctor_set(v_reuseFailAlloc_325_, 3, v_auxDeclNGen_293_);
lean_ctor_set(v_reuseFailAlloc_325_, 4, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_325_, 5, v_cache_294_);
lean_ctor_set(v_reuseFailAlloc_325_, 6, v_recordedDeps_295_);
lean_ctor_set(v_reuseFailAlloc_325_, 7, v_messages_296_);
lean_ctor_set(v_reuseFailAlloc_325_, 8, v_infoState_297_);
lean_ctor_set(v_reuseFailAlloc_325_, 9, v_snapshotTasks_298_);
v___x_320_ = v_reuseFailAlloc_325_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_321_ = lean_st_ref_put(v___y_280_, v___x_320_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_307_);
v___x_323_ = v___x_286_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_307_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___boxed(lean_object* v_cls_330_, lean_object* v_msg_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8(v_cls_330_, v_msg_331_, v___y_332_, v___y_333_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
return v_res_335_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___redArg(lean_object* v_keys_336_, lean_object* v_i_337_, lean_object* v_k_338_){
_start:
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = lean_array_get_size(v_keys_336_);
v___x_340_ = lean_nat_dec_lt(v_i_337_, v___x_339_);
if (v___x_340_ == 0)
{
lean_dec(v_i_337_);
return v___x_340_;
}
else
{
lean_object* v_k_x27_341_; uint8_t v___x_342_; 
v_k_x27_341_ = lean_array_fget_borrowed(v_keys_336_, v_i_337_);
v___x_342_ = l_Lean_instBEqExtraModUse_beq(v_k_338_, v_k_x27_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = lean_nat_add(v_i_337_, v___x_343_);
lean_dec(v_i_337_);
v_i_337_ = v___x_344_;
goto _start;
}
else
{
lean_dec(v_i_337_);
return v___x_340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_keys_346_, lean_object* v_i_347_, lean_object* v_k_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___redArg(v_keys_346_, v_i_347_, v_k_348_);
lean_dec_ref(v_k_348_);
lean_dec_ref(v_keys_346_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg(lean_object* v_x_351_, size_t v_x_352_, lean_object* v_x_353_){
_start:
{
if (lean_obj_tag(v_x_351_) == 0)
{
lean_object* v_es_354_; lean_object* v___x_355_; size_t v___x_356_; size_t v___x_357_; lean_object* v_j_358_; lean_object* v___x_359_; 
v_es_354_ = lean_ctor_get(v_x_351_, 0);
v___x_355_ = lean_box(2);
v___x_356_ = ((size_t)31ULL);
v___x_357_ = lean_usize_land(v_x_352_, v___x_356_);
v_j_358_ = lean_usize_to_nat(v___x_357_);
v___x_359_ = lean_array_get_borrowed(v___x_355_, v_es_354_, v_j_358_);
lean_dec(v_j_358_);
switch(lean_obj_tag(v___x_359_))
{
case 0:
{
lean_object* v_key_360_; uint8_t v___x_361_; 
v_key_360_ = lean_ctor_get(v___x_359_, 0);
v___x_361_ = l_Lean_instBEqExtraModUse_beq(v_x_353_, v_key_360_);
return v___x_361_;
}
case 1:
{
lean_object* v_node_362_; size_t v___x_363_; size_t v___x_364_; 
v_node_362_ = lean_ctor_get(v___x_359_, 0);
v___x_363_ = ((size_t)5ULL);
v___x_364_ = lean_usize_shift_right(v_x_352_, v___x_363_);
v_x_351_ = v_node_362_;
v_x_352_ = v___x_364_;
goto _start;
}
default: 
{
uint8_t v___x_366_; 
v___x_366_ = 0;
return v___x_366_;
}
}
}
else
{
lean_object* v_ks_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v_ks_367_ = lean_ctor_get(v_x_351_, 0);
v___x_368_ = lean_unsigned_to_nat(0u);
v___x_369_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___redArg(v_ks_367_, v___x_368_, v_x_353_);
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg___boxed(lean_object* v_x_370_, lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
size_t v_x_5493__boxed_373_; uint8_t v_res_374_; lean_object* v_r_375_; 
v_x_5493__boxed_373_ = lean_unbox_usize(v_x_371_);
lean_dec(v_x_371_);
v_res_374_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg(v_x_370_, v_x_5493__boxed_373_, v_x_372_);
lean_dec_ref(v_x_372_);
lean_dec_ref(v_x_370_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___redArg(lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
uint64_t v___x_378_; size_t v___x_379_; uint8_t v___x_380_; 
v___x_378_ = l_Lean_instHashableExtraModUse_hash(v_x_377_);
v___x_379_ = lean_uint64_to_usize(v___x_378_);
v___x_380_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg(v_x_376_, v___x_379_, v_x_377_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___redArg___boxed(lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
uint8_t v_res_383_; lean_object* v_r_384_; 
v_res_383_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___redArg(v_x_381_, v_x_382_);
lean_dec_ref(v_x_382_);
lean_dec_ref(v_x_381_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___lam__0(lean_object* v___x_385_, lean_object* v_entry_386_, lean_object* v_s_387_){
_start:
{
lean_object* v_addEntryFn_388_; lean_object* v_importedEntries_389_; lean_object* v_state_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_398_; 
v_addEntryFn_388_ = lean_ctor_get(v___x_385_, 3);
lean_inc(v_addEntryFn_388_);
lean_dec_ref(v___x_385_);
v_importedEntries_389_ = lean_ctor_get(v_s_387_, 0);
v_state_390_ = lean_ctor_get(v_s_387_, 1);
v_isSharedCheck_398_ = !lean_is_exclusive(v_s_387_);
if (v_isSharedCheck_398_ == 0)
{
v___x_392_ = v_s_387_;
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_state_390_);
lean_inc(v_importedEntries_389_);
lean_dec(v_s_387_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_398_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v_state_394_; lean_object* v___x_396_; 
v_state_394_ = lean_apply_2(v_addEntryFn_388_, v_state_390_, v_entry_386_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v_state_394_);
v___x_396_ = v___x_392_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_importedEntries_389_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_state_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_399_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__4(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__3));
v___x_405_ = l_Lean_stringToMessageData(v___x_404_);
return v___x_405_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__5));
v___x_408_ = l_Lean_stringToMessageData(v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__7(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8___closed__1));
v___x_410_ = l_Lean_stringToMessageData(v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__10(void){
_start:
{
lean_object* v_cls_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_cls_414_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__2));
v___x_415_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__9));
v___x_416_ = l_Lean_Name_append(v___x_415_, v_cls_414_);
return v___x_416_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__11));
v___x_419_ = l_Lean_stringToMessageData(v___x_418_);
return v___x_419_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__13));
v___x_422_ = l_Lean_stringToMessageData(v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5(lean_object* v_mod_427_, uint8_t v_isMeta_428_, lean_object* v_hint_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v_env_451_; uint8_t v_isExporting_452_; lean_object* v_entry_453_; lean_object* v___x_454_; lean_object* v_env_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_449_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__0);
v___x_450_ = lean_st_ref_get(v___y_431_);
v_env_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc_ref(v_env_451_);
lean_dec(v___x_450_);
v_isExporting_452_ = lean_ctor_get_uint8(v_env_451_, sizeof(void*)*13);
lean_dec_ref(v_env_451_);
lean_inc(v_mod_427_);
v_entry_453_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_453_, 0, v_mod_427_);
lean_ctor_set_uint8(v_entry_453_, sizeof(void*)*1, v_isExporting_452_);
lean_ctor_set_uint8(v_entry_453_, sizeof(void*)*1 + 1, v_isMeta_428_);
v___x_454_ = lean_st_ref_get(v___y_431_);
v_env_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc_ref(v_env_455_);
lean_dec(v___x_454_);
v___x_456_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_457_ = lean_box(1);
v___x_458_ = lean_box(0);
v___x_459_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_449_, v___x_456_, v_env_455_, v___x_457_, v___x_458_);
v___x_460_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___redArg(v___x_459_, v_entry_453_);
lean_dec(v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v_toCold_461_; lean_object* v_options_462_; lean_object* v_inheritedTraceOptions_463_; uint8_t v_hasTrace_464_; lean_object* v___f_465_; uint8_t v___x_466_; lean_object* v___y_468_; 
v_toCold_461_ = lean_ctor_get(v___y_430_, 0);
v_options_462_ = lean_ctor_get(v_toCold_461_, 2);
v_inheritedTraceOptions_463_ = lean_ctor_get(v_toCold_461_, 11);
v_hasTrace_464_ = lean_ctor_get_uint8(v_options_462_, sizeof(void*)*1);
v___f_465_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___lam__0), 3, 2);
lean_closure_set(v___f_465_, 0, v___x_456_);
lean_closure_set(v___f_465_, 1, v_entry_453_);
v___x_466_ = 1;
if (v_hasTrace_464_ == 0)
{
lean_dec(v_hint_429_);
lean_dec(v_mod_427_);
v___y_468_ = v___y_431_;
goto v___jp_467_;
}
else
{
lean_object* v_cls_486_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___x_506_; uint8_t v___x_507_; 
v_cls_486_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__2));
v___x_506_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__10);
v___x_507_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_463_, v_options_462_, v___x_506_);
if (v___x_507_ == 0)
{
lean_dec(v_hint_429_);
lean_dec(v_mod_427_);
v___y_468_ = v___y_431_;
goto v___jp_467_;
}
else
{
lean_object* v___x_508_; lean_object* v___y_510_; 
v___x_508_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__12);
if (v_isExporting_452_ == 0)
{
lean_object* v___x_517_; 
v___x_517_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__17));
v___y_510_ = v___x_517_;
goto v___jp_509_;
}
else
{
lean_object* v___x_518_; 
v___x_518_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__18));
v___y_510_ = v___x_518_;
goto v___jp_509_;
}
v___jp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
lean_inc_ref(v___y_510_);
v___x_511_ = l_Lean_stringToMessageData(v___y_510_);
v___x_512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_508_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__14);
v___x_514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
if (v_isMeta_428_ == 0)
{
lean_object* v___x_515_; 
v___x_515_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__15));
v___y_493_ = v___x_514_;
v___y_494_ = v___x_515_;
goto v___jp_492_;
}
else
{
lean_object* v___x_516_; 
v___x_516_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__16));
v___y_493_ = v___x_514_;
v___y_494_ = v___x_516_;
goto v___jp_492_;
}
}
}
v___jp_487_:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_490_, 0, v___y_488_);
lean_ctor_set(v___x_490_, 1, v___y_489_);
v___x_491_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__8(v_cls_486_, v___x_490_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_dec_ref_known(v___x_491_, 1);
v___y_468_ = v___y_431_;
goto v___jp_467_;
}
else
{
lean_dec_ref(v___f_465_);
return v___x_491_;
}
}
v___jp_492_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
lean_inc_ref(v___y_494_);
v___x_495_ = l_Lean_stringToMessageData(v___y_494_);
v___x_496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_496_, 0, v___y_493_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__4);
v___x_498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = l_Lean_MessageData_ofName(v_mod_427_);
v___x_500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = l_Lean_Name_isAnonymous(v_hint_429_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__6);
v___x_503_ = l_Lean_MessageData_ofName(v_hint_429_);
v___x_504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_502_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___y_488_ = v___x_500_;
v___y_489_ = v___x_504_;
goto v___jp_487_;
}
else
{
lean_object* v___x_505_; 
lean_dec(v_hint_429_);
v___x_505_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___closed__7);
v___y_488_ = v___x_500_;
v___y_489_ = v___x_505_;
goto v___jp_487_;
}
}
}
v___jp_467_:
{
lean_object* v___x_469_; lean_object* v_toEnvExtension_470_; lean_object* v_env_471_; lean_object* v_nextMacroScope_472_; lean_object* v_ngen_473_; lean_object* v_auxDeclNGen_474_; lean_object* v_traceState_475_; lean_object* v_recordedDeps_476_; lean_object* v_messages_477_; lean_object* v_infoState_478_; lean_object* v_snapshotTasks_479_; lean_object* v_asyncMode_480_; uint8_t v_logWrites_481_; lean_object* v___x_482_; 
v___x_469_ = lean_st_ref_take(v___y_468_);
v_toEnvExtension_470_ = lean_ctor_get(v___x_456_, 0);
v_env_471_ = lean_ctor_get(v___x_469_, 0);
lean_inc_ref(v_env_471_);
v_nextMacroScope_472_ = lean_ctor_get(v___x_469_, 1);
lean_inc(v_nextMacroScope_472_);
v_ngen_473_ = lean_ctor_get(v___x_469_, 2);
lean_inc_ref(v_ngen_473_);
v_auxDeclNGen_474_ = lean_ctor_get(v___x_469_, 3);
lean_inc_ref(v_auxDeclNGen_474_);
v_traceState_475_ = lean_ctor_get(v___x_469_, 4);
lean_inc_ref(v_traceState_475_);
v_recordedDeps_476_ = lean_ctor_get(v___x_469_, 6);
lean_inc_ref(v_recordedDeps_476_);
v_messages_477_ = lean_ctor_get(v___x_469_, 7);
lean_inc_ref(v_messages_477_);
v_infoState_478_ = lean_ctor_get(v___x_469_, 8);
lean_inc_ref(v_infoState_478_);
v_snapshotTasks_479_ = lean_ctor_get(v___x_469_, 9);
lean_inc_ref(v_snapshotTasks_479_);
lean_dec(v___x_469_);
v_asyncMode_480_ = lean_ctor_get(v_toEnvExtension_470_, 2);
v_logWrites_481_ = lean_ctor_get_uint8(v_toEnvExtension_470_, sizeof(void*)*6);
v___x_482_ = lean_box(0);
if (v_logWrites_481_ == 0)
{
lean_object* v___x_483_; 
lean_inc_ref(v_toEnvExtension_470_);
v___x_483_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_470_, v_env_471_, v___f_465_, v_asyncMode_480_, v___x_458_, v___x_466_);
v___y_434_ = v_infoState_478_;
v___y_435_ = v___x_482_;
v___y_436_ = v_ngen_473_;
v___y_437_ = v_traceState_475_;
v___y_438_ = v_messages_477_;
v___y_439_ = v_auxDeclNGen_474_;
v___y_440_ = v_recordedDeps_476_;
v___y_441_ = v___y_468_;
v___y_442_ = v_snapshotTasks_479_;
v___y_443_ = v_nextMacroScope_472_;
v___y_444_ = v___x_483_;
goto v___jp_433_;
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_inc_ref_n(v_toEnvExtension_470_, 2);
v___x_484_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_470_, v_env_471_);
lean_dec_ref(v_env_471_);
v___x_485_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_470_, v___x_484_, v___f_465_, v_asyncMode_480_, v___x_458_, v___x_466_);
v___y_434_ = v_infoState_478_;
v___y_435_ = v___x_482_;
v___y_436_ = v_ngen_473_;
v___y_437_ = v_traceState_475_;
v___y_438_ = v_messages_477_;
v___y_439_ = v_auxDeclNGen_474_;
v___y_440_ = v_recordedDeps_476_;
v___y_441_ = v___y_468_;
v___y_442_ = v_snapshotTasks_479_;
v___y_443_ = v_nextMacroScope_472_;
v___y_444_ = v___x_485_;
goto v___jp_433_;
}
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec_ref_known(v_entry_453_, 1);
lean_dec(v_hint_429_);
lean_dec(v_mod_427_);
v___x_519_ = lean_box(0);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
v___jp_433_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_445_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2, &l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg___closed__2);
v___x_446_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_446_, 0, v___y_444_);
lean_ctor_set(v___x_446_, 1, v___y_443_);
lean_ctor_set(v___x_446_, 2, v___y_436_);
lean_ctor_set(v___x_446_, 3, v___y_439_);
lean_ctor_set(v___x_446_, 4, v___y_437_);
lean_ctor_set(v___x_446_, 5, v___x_445_);
lean_ctor_set(v___x_446_, 6, v___y_440_);
lean_ctor_set(v___x_446_, 7, v___y_438_);
lean_ctor_set(v___x_446_, 8, v___y_434_);
lean_ctor_set(v___x_446_, 9, v___y_442_);
v___x_447_ = lean_st_ref_put(v___y_441_, v___x_446_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___y_435_);
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5___boxed(lean_object* v_mod_521_, lean_object* v_isMeta_522_, lean_object* v_hint_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
uint8_t v_isMeta_boxed_527_; lean_object* v_res_528_; 
v_isMeta_boxed_527_ = lean_unbox(v_isMeta_522_);
v_res_528_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5(v_mod_521_, v_isMeta_boxed_527_, v_hint_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__6(lean_object* v___x_529_, lean_object* v_declName_530_, lean_object* v_as_531_, size_t v_sz_532_, size_t v_i_533_, lean_object* v_b_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
uint8_t v___x_538_; 
v___x_538_ = lean_usize_dec_lt(v_i_533_, v_sz_532_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; 
lean_dec(v_declName_530_);
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v_b_534_);
return v___x_539_;
}
else
{
lean_object* v___x_540_; lean_object* v_modules_541_; lean_object* v___x_542_; lean_object* v_a_543_; lean_object* v___x_544_; lean_object* v_toImport_545_; lean_object* v_module_546_; lean_object* v___x_547_; uint8_t v___x_548_; lean_object* v___x_549_; 
v___x_540_ = l_Lean_Environment_header(v___x_529_);
v_modules_541_ = lean_ctor_get(v___x_540_, 3);
lean_inc_ref(v_modules_541_);
lean_dec_ref(v___x_540_);
v___x_542_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_543_ = lean_array_uget_borrowed(v_as_531_, v_i_533_);
v___x_544_ = lean_array_get(v___x_542_, v_modules_541_, v_a_543_);
lean_dec_ref(v_modules_541_);
v_toImport_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc_ref(v_toImport_545_);
lean_dec(v___x_544_);
v_module_546_ = lean_ctor_get(v_toImport_545_, 0);
lean_inc(v_module_546_);
lean_dec_ref(v_toImport_545_);
v___x_547_ = lean_box(0);
v___x_548_ = 0;
lean_inc(v_declName_530_);
v___x_549_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5(v_module_546_, v___x_548_, v_declName_530_, v___y_535_, v___y_536_);
if (lean_obj_tag(v___x_549_) == 0)
{
size_t v___x_550_; size_t v___x_551_; 
lean_dec_ref_known(v___x_549_, 1);
v___x_550_ = ((size_t)1ULL);
v___x_551_ = lean_usize_add(v_i_533_, v___x_550_);
v_i_533_ = v___x_551_;
v_b_534_ = v___x_547_;
goto _start;
}
else
{
lean_dec(v_declName_530_);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__6___boxed(lean_object* v___x_553_, lean_object* v_declName_554_, lean_object* v_as_555_, lean_object* v_sz_556_, lean_object* v_i_557_, lean_object* v_b_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
size_t v_sz_boxed_562_; size_t v_i_boxed_563_; lean_object* v_res_564_; 
v_sz_boxed_562_ = lean_unbox_usize(v_sz_556_);
lean_dec(v_sz_556_);
v_i_boxed_563_ = lean_unbox_usize(v_i_557_);
lean_dec(v_i_557_);
v_res_564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__6(v___x_553_, v_declName_554_, v_as_555_, v_sz_boxed_562_, v_i_boxed_563_, v_b_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec_ref(v_as_555_);
lean_dec_ref(v___x_553_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg(lean_object* v_a_565_, lean_object* v_x_566_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
lean_object* v___x_567_; 
v___x_567_ = lean_box(0);
return v___x_567_;
}
else
{
lean_object* v_key_568_; lean_object* v_value_569_; lean_object* v_tail_570_; uint8_t v___x_571_; 
v_key_568_ = lean_ctor_get(v_x_566_, 0);
v_value_569_ = lean_ctor_get(v_x_566_, 1);
v_tail_570_ = lean_ctor_get(v_x_566_, 2);
v___x_571_ = lean_name_eq(v_key_568_, v_a_565_);
if (v___x_571_ == 0)
{
v_x_566_ = v_tail_570_;
goto _start;
}
else
{
lean_object* v___x_573_; 
lean_inc(v_value_569_);
v___x_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_573_, 0, v_value_569_);
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg___boxed(lean_object* v_a_574_, lean_object* v_x_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg(v_a_574_, v_x_575_);
lean_dec(v_x_575_);
lean_dec(v_a_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg(lean_object* v_m_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_buckets_579_; lean_object* v___x_580_; uint64_t v___y_582_; 
v_buckets_579_ = lean_ctor_get(v_m_577_, 1);
v___x_580_ = lean_array_get_size(v_buckets_579_);
if (lean_obj_tag(v_a_578_) == 0)
{
uint64_t v___x_596_; 
v___x_596_ = 1723ULL;
v___y_582_ = v___x_596_;
goto v___jp_581_;
}
else
{
uint64_t v_hash_597_; 
v_hash_597_ = lean_ctor_get_uint64(v_a_578_, sizeof(void*)*2);
v___y_582_ = v_hash_597_;
goto v___jp_581_;
}
v___jp_581_:
{
uint64_t v___x_583_; uint64_t v___x_584_; uint64_t v_fold_585_; uint64_t v___x_586_; uint64_t v___x_587_; uint64_t v___x_588_; size_t v___x_589_; size_t v___x_590_; size_t v___x_591_; size_t v___x_592_; size_t v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_583_ = 32ULL;
v___x_584_ = lean_uint64_shift_right(v___y_582_, v___x_583_);
v_fold_585_ = lean_uint64_xor(v___y_582_, v___x_584_);
v___x_586_ = 16ULL;
v___x_587_ = lean_uint64_shift_right(v_fold_585_, v___x_586_);
v___x_588_ = lean_uint64_xor(v_fold_585_, v___x_587_);
v___x_589_ = lean_uint64_to_usize(v___x_588_);
v___x_590_ = lean_usize_of_nat(v___x_580_);
v___x_591_ = ((size_t)1ULL);
v___x_592_ = lean_usize_sub(v___x_590_, v___x_591_);
v___x_593_ = lean_usize_land(v___x_589_, v___x_592_);
v___x_594_ = lean_array_uget_borrowed(v_buckets_579_, v___x_593_);
v___x_595_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg(v_a_578_, v___x_594_);
return v___x_595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg___boxed(lean_object* v_m_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg(v_m_598_, v_a_599_);
lean_dec(v_a_599_);
lean_dec_ref(v_m_598_);
return v_res_600_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__0(void){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Std_HashMap_instInhabited___redArg();
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2(lean_object* v_declName_604_, uint8_t v_isMeta_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v_env_614_; lean_object* v___y_616_; lean_object* v___x_629_; 
v___x_609_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__0);
v___x_610_ = lean_st_ref_get(v___y_607_);
v_env_614_ = lean_ctor_get(v___x_610_, 0);
lean_inc_ref(v_env_614_);
lean_dec(v___x_610_);
v___x_629_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_614_, v_declName_604_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_dec_ref(v_env_614_);
lean_dec(v_declName_604_);
goto v___jp_611_;
}
else
{
lean_object* v_val_630_; lean_object* v___x_631_; lean_object* v_modules_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_val_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_val_630_);
lean_dec_ref_known(v___x_629_, 1);
v___x_631_ = l_Lean_Environment_header(v_env_614_);
v_modules_632_ = lean_ctor_get(v___x_631_, 3);
lean_inc_ref(v_modules_632_);
lean_dec_ref(v___x_631_);
v___x_633_ = lean_array_get_size(v_modules_632_);
v___x_634_ = lean_nat_dec_lt(v_val_630_, v___x_633_);
if (v___x_634_ == 0)
{
lean_dec_ref(v_modules_632_);
lean_dec(v_val_630_);
lean_dec_ref(v_env_614_);
lean_dec(v_declName_604_);
goto v___jp_611_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___y_638_; 
v___x_635_ = lean_array_fget(v_modules_632_, v_val_630_);
lean_dec(v_val_630_);
lean_dec_ref(v_modules_632_);
v___x_636_ = lean_st_ref_get(v___y_607_);
if (v_isMeta_605_ == 0)
{
lean_dec(v___x_636_);
v___y_638_ = v_isMeta_605_;
goto v___jp_637_;
}
else
{
lean_object* v_env_649_; uint8_t v___x_650_; 
v_env_649_ = lean_ctor_get(v___x_636_, 0);
lean_inc_ref(v_env_649_);
lean_dec(v___x_636_);
lean_inc(v_declName_604_);
v___x_650_ = l_Lean_isMarkedMeta(v_env_649_, v_declName_604_);
if (v___x_650_ == 0)
{
v___y_638_ = v_isMeta_605_;
goto v___jp_637_;
}
else
{
uint8_t v___x_651_; 
v___x_651_ = 0;
v___y_638_ = v___x_651_;
goto v___jp_637_;
}
}
v___jp_637_:
{
lean_object* v_toImport_639_; lean_object* v_module_640_; lean_object* v___x_641_; 
v_toImport_639_ = lean_ctor_get(v___x_635_, 0);
lean_inc_ref(v_toImport_639_);
lean_dec(v___x_635_);
v_module_640_ = lean_ctor_get(v_toImport_639_, 0);
lean_inc(v_module_640_);
lean_dec_ref(v_toImport_639_);
lean_inc(v_declName_604_);
v___x_641_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5(v_module_640_, v___y_638_, v_declName_604_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec_ref_known(v___x_641_, 1);
v___x_642_ = l_Lean_indirectModUseExt;
v___x_643_ = lean_box(1);
v___x_644_ = lean_box(0);
lean_inc_ref(v_env_614_);
v___x_645_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_609_, v___x_642_, v_env_614_, v___x_643_, v___x_644_);
v___x_646_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg(v___x_645_, v_declName_604_);
lean_dec(v___x_645_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v___x_647_; 
v___x_647_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___closed__1));
v___y_616_ = v___x_647_;
goto v___jp_615_;
}
else
{
lean_object* v_val_648_; 
v_val_648_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_val_648_);
lean_dec_ref_known(v___x_646_, 1);
v___y_616_ = v_val_648_;
goto v___jp_615_;
}
}
else
{
lean_dec_ref(v_env_614_);
lean_dec(v_declName_604_);
return v___x_641_;
}
}
}
}
v___jp_611_:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_box(0);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
v___jp_615_:
{
lean_object* v___x_617_; size_t v_sz_618_; size_t v___x_619_; lean_object* v___x_620_; 
v___x_617_ = lean_box(0);
v_sz_618_ = lean_array_size(v___y_616_);
v___x_619_ = ((size_t)0ULL);
v___x_620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__6(v_env_614_, v_declName_604_, v___y_616_, v_sz_618_, v___x_619_, v___x_617_, v___y_606_, v___y_607_);
lean_dec_ref(v___y_616_);
lean_dec_ref(v_env_614_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v___x_620_, 0);
lean_dec(v_unused_628_);
v___x_622_ = v___x_620_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_dec(v___x_620_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_617_);
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_617_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
else
{
return v___x_620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2___boxed(lean_object* v_declName_652_, lean_object* v_isMeta_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
uint8_t v_isMeta_boxed_657_; lean_object* v_res_658_; 
v_isMeta_boxed_657_ = lean_unbox(v_isMeta_653_);
v_res_658_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2(v_declName_652_, v_isMeta_boxed_657_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__4(uint8_t v___x_659_, lean_object* v_a_660_, lean_object* v_decl_661_, lean_object* v_stx_662_, uint8_t v_x_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_667_; lean_object* v_env_668_; lean_object* v___x_669_; 
v___x_667_ = lean_st_ref_get(v___y_665_);
v_env_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc_ref(v_env_668_);
lean_dec(v___x_667_);
v___x_669_ = l_Lean_Attribute_Builtin_getIdent(v_stx_662_, v___y_664_, v___y_665_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
v___x_671_ = lean_box(0);
v___x_672_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_670_, v___x_671_, v___y_664_, v___y_665_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_674_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc_n(v_a_673_, 2);
lean_dec_ref_known(v___x_672_, 1);
v___x_674_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2(v_a_673_, v___x_659_, v___y_664_, v___y_665_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_toEnvExtension_675_; lean_object* v_addEntryFn_676_; lean_object* v_asyncMode_677_; uint8_t v_logWrites_678_; lean_object* v___x_679_; lean_object* v___f_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
lean_dec_ref_known(v___x_674_, 1);
v_toEnvExtension_675_ = lean_ctor_get(v_a_660_, 0);
lean_inc_ref(v_toEnvExtension_675_);
v_addEntryFn_676_ = lean_ctor_get(v_a_660_, 3);
lean_inc(v_addEntryFn_676_);
lean_dec_ref(v_a_660_);
v_asyncMode_677_ = lean_ctor_get(v_toEnvExtension_675_, 2);
lean_inc(v_asyncMode_677_);
v_logWrites_678_ = lean_ctor_get_uint8(v_toEnvExtension_675_, sizeof(void*)*6);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v_a_673_);
lean_ctor_set(v___x_679_, 1, v_decl_661_);
v___f_680_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerCombinatorAttribute___lam__3), 3, 2);
lean_closure_set(v___f_680_, 0, v_addEntryFn_676_);
lean_closure_set(v___f_680_, 1, v___x_679_);
v___x_681_ = lean_box(0);
v___x_682_ = 1;
if (v_logWrites_678_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_675_, v_env_668_, v___f_680_, v_asyncMode_677_, v___x_681_, v___x_682_);
lean_dec(v_asyncMode_677_);
v___x_684_ = l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg(v___x_683_, v___y_665_);
return v___x_684_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_inc_ref(v_toEnvExtension_675_);
v___x_685_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_675_, v_env_668_);
lean_dec_ref(v_env_668_);
v___x_686_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_675_, v___x_685_, v___f_680_, v_asyncMode_677_, v___x_681_, v___x_682_);
lean_dec(v_asyncMode_677_);
v___x_687_ = l_Lean_setEnv___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__3___redArg(v___x_686_, v___y_665_);
return v___x_687_;
}
}
else
{
lean_dec(v_a_673_);
lean_dec_ref(v_env_668_);
lean_dec(v_decl_661_);
lean_dec_ref(v_a_660_);
return v___x_674_;
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec_ref(v_env_668_);
lean_dec(v_decl_661_);
lean_dec_ref(v_a_660_);
v_a_688_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_672_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_672_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v_env_668_);
lean_dec(v_decl_661_);
lean_dec_ref(v_a_660_);
v_a_696_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_669_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_669_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lam__4___boxed(lean_object* v___x_704_, lean_object* v_a_705_, lean_object* v_decl_706_, lean_object* v_stx_707_, lean_object* v_x_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
uint8_t v___x_5983__boxed_712_; uint8_t v_x_5985__boxed_713_; lean_object* v_res_714_; 
v___x_5983__boxed_712_ = lean_unbox(v___x_704_);
v_x_5985__boxed_713_ = lean_unbox(v_x_708_);
v_res_714_ = l_Lean_ParserCompiler_registerCombinatorAttribute___lam__4(v___x_5983__boxed_712_, v_a_705_, v_decl_706_, v_stx_707_, v_x_5985__boxed_713_, v___y_709_, v___y_710_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__2(lean_object* v_as_715_, size_t v_i_716_, size_t v_stop_717_, lean_object* v_b_718_){
_start:
{
uint8_t v___x_719_; 
v___x_719_ = lean_usize_dec_eq(v_i_716_, v_stop_717_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v_fst_721_; lean_object* v_snd_722_; lean_object* v___x_723_; size_t v___x_724_; size_t v___x_725_; 
v___x_720_ = lean_array_uget_borrowed(v_as_715_, v_i_716_);
v_fst_721_ = lean_ctor_get(v___x_720_, 0);
v_snd_722_ = lean_ctor_get(v___x_720_, 1);
lean_inc(v_snd_722_);
lean_inc(v_fst_721_);
v___x_723_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_721_, v_snd_722_, v_b_718_);
v___x_724_ = ((size_t)1ULL);
v___x_725_ = lean_usize_add(v_i_716_, v___x_724_);
v_i_716_ = v___x_725_;
v_b_718_ = v___x_723_;
goto _start;
}
else
{
return v_b_718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__2___boxed(lean_object* v_as_727_, lean_object* v_i_728_, lean_object* v_stop_729_, lean_object* v_b_730_){
_start:
{
size_t v_i_boxed_731_; size_t v_stop_boxed_732_; lean_object* v_res_733_; 
v_i_boxed_731_ = lean_unbox_usize(v_i_728_);
lean_dec(v_i_728_);
v_stop_boxed_732_ = lean_unbox_usize(v_stop_729_);
lean_dec(v_stop_729_);
v_res_733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__2(v_as_727_, v_i_boxed_731_, v_stop_boxed_732_, v_b_730_);
lean_dec_ref(v_as_727_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__3(lean_object* v_as_734_, size_t v_i_735_, size_t v_stop_736_, lean_object* v_b_737_){
_start:
{
lean_object* v___y_739_; uint8_t v___x_743_; 
v___x_743_ = lean_usize_dec_eq(v_i_735_, v_stop_736_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_744_ = lean_array_uget_borrowed(v_as_734_, v_i_735_);
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = lean_array_get_size(v___x_744_);
v___x_747_ = lean_nat_dec_lt(v___x_745_, v___x_746_);
if (v___x_747_ == 0)
{
v___y_739_ = v_b_737_;
goto v___jp_738_;
}
else
{
size_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; 
v___x_748_ = ((size_t)0ULL);
v___x_749_ = lean_usize_of_nat(v___x_746_);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__2(v___x_744_, v___x_748_, v___x_749_, v_b_737_);
v___y_739_ = v___x_750_;
goto v___jp_738_;
}
}
else
{
return v_b_737_;
}
v___jp_738_:
{
size_t v___x_740_; size_t v___x_741_; 
v___x_740_ = ((size_t)1ULL);
v___x_741_ = lean_usize_add(v_i_735_, v___x_740_);
v_i_735_ = v___x_741_;
v_b_737_ = v___y_739_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__3___boxed(lean_object* v_as_751_, lean_object* v_i_752_, lean_object* v_stop_753_, lean_object* v_b_754_){
_start:
{
size_t v_i_boxed_755_; size_t v_stop_boxed_756_; lean_object* v_res_757_; 
v_i_boxed_755_ = lean_unbox_usize(v_i_752_);
lean_dec(v_i_752_);
v_stop_boxed_756_ = lean_unbox_usize(v_stop_753_);
lean_dec(v_stop_753_);
v_res_757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__3(v_as_751_, v_i_boxed_755_, v_stop_boxed_756_, v_b_754_);
lean_dec_ref(v_as_751_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1(lean_object* v_initState_758_, lean_object* v_as_759_){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = lean_array_get_size(v_as_759_);
v___x_762_ = lean_nat_dec_lt(v___x_760_, v___x_761_);
if (v___x_762_ == 0)
{
return v_initState_758_;
}
else
{
size_t v___x_763_; size_t v___x_764_; lean_object* v___x_765_; 
v___x_763_ = ((size_t)0ULL);
v___x_764_ = lean_usize_of_nat(v___x_761_);
v___x_765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1_spec__3(v_as_759_, v___x_763_, v___x_764_, v_initState_758_);
return v___x_765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1___boxed(lean_object* v_initState_766_, lean_object* v_as_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_mkStateFromImportedEntries___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__1(v_initState_766_, v_as_767_);
lean_dec_ref(v_as_767_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute(lean_object* v_name_773_, lean_object* v_descr_774_, lean_object* v_ref_775_){
_start:
{
lean_object* v___f_777_; lean_object* v___f_778_; lean_object* v___f_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
lean_inc(v_name_773_);
v___f_777_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerCombinatorAttribute___lam__0___boxed), 5, 1);
lean_closure_set(v___f_777_, 0, v_name_773_);
v___f_778_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___closed__0));
v___f_779_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___closed__1));
v___x_780_ = ((lean_object*)(l_Lean_ParserCompiler_registerCombinatorAttribute___closed__2));
v___x_781_ = lean_box(0);
v___x_782_ = lean_box(2);
v___x_783_ = 0;
lean_inc(v_ref_775_);
v___x_784_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_784_, 0, v_ref_775_);
lean_ctor_set(v___x_784_, 1, v___f_779_);
lean_ctor_set(v___x_784_, 2, v___x_780_);
lean_ctor_set(v___x_784_, 3, v___f_778_);
lean_ctor_set(v___x_784_, 4, v___x_781_);
lean_ctor_set(v___x_784_, 5, v___x_782_);
lean_ctor_set(v___x_784_, 6, v___x_781_);
lean_ctor_set_uint8(v___x_784_, sizeof(void*)*7, v___x_783_);
v___x_785_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_784_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_787_; lean_object* v___f_788_; uint8_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc_n(v_a_786_, 2);
lean_dec_ref_known(v___x_785_, 1);
v___x_787_ = lean_box(v___x_783_);
v___f_788_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerCombinatorAttribute___lam__4___boxed), 8, 2);
lean_closure_set(v___f_788_, 0, v___x_787_);
lean_closure_set(v___f_788_, 1, v_a_786_);
v___x_789_ = 0;
v___x_790_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_790_, 0, v_ref_775_);
lean_ctor_set(v___x_790_, 1, v_name_773_);
lean_ctor_set(v___x_790_, 2, v_descr_774_);
lean_ctor_set_uint8(v___x_790_, sizeof(void*)*3, v___x_789_);
v___x_791_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___f_788_);
lean_ctor_set(v___x_791_, 2, v___f_777_);
lean_inc_ref(v___x_791_);
v___x_792_ = l_Lean_registerBuiltinAttribute(v___x_791_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_800_; 
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v___x_792_, 0);
lean_dec(v_unused_801_);
v___x_794_ = v___x_792_;
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
else
{
lean_dec(v___x_792_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_791_);
lean_ctor_set(v___x_796_, 1, v_a_786_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_796_);
v___x_798_ = v___x_794_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref_known(v___x_791_, 3);
lean_dec(v_a_786_);
v_a_802_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_792_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_792_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v___f_777_);
lean_dec(v_ref_775_);
lean_dec_ref(v_descr_774_);
lean_dec(v_name_773_);
v_a_810_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_785_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_785_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
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
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___boxed(lean_object* v_name_818_, lean_object* v_descr_819_, lean_object* v_ref_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_ParserCompiler_registerCombinatorAttribute(v_name_818_, v_descr_819_, v_ref_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0(lean_object* v_00_u03b1_823_, lean_object* v_msg_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(v_msg_824_, v___y_825_, v___y_826_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___boxed(lean_object* v_00_u03b1_829_, lean_object* v_msg_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0(v_00_u03b1_829_, v_msg_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7(lean_object* v_00_u03b2_835_, lean_object* v_m_836_, lean_object* v_a_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___redArg(v_m_836_, v_a_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7___boxed(lean_object* v_00_u03b2_839_, lean_object* v_m_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7(v_00_u03b2_839_, v_m_840_, v_a_841_);
lean_dec(v_a_841_);
lean_dec_ref(v_m_840_);
return v_res_842_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
uint8_t v___x_846_; 
v___x_846_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___redArg(v_x_844_, v_x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7___boxed(lean_object* v_00_u03b2_847_, lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
uint8_t v_res_850_; lean_object* v_r_851_; 
v_res_850_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7(v_00_u03b2_847_, v_x_848_, v_x_849_);
lean_dec_ref(v_x_849_);
lean_dec_ref(v_x_848_);
v_r_851_ = lean_box(v_res_850_);
return v_r_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11(lean_object* v_00_u03b2_852_, lean_object* v_a_853_, lean_object* v_x_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___redArg(v_a_853_, v_x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11___boxed(lean_object* v_00_u03b2_856_, lean_object* v_a_857_, lean_object* v_x_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__7_spec__11(v_00_u03b2_856_, v_a_857_, v_x_858_);
lean_dec(v_x_858_);
lean_dec(v_a_857_);
return v_res_859_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_860_, lean_object* v_x_861_, size_t v_x_862_, lean_object* v_x_863_){
_start:
{
uint8_t v___x_864_; 
v___x_864_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___redArg(v_x_861_, v_x_862_, v_x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8___boxed(lean_object* v_00_u03b2_865_, lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_){
_start:
{
size_t v_x_6241__boxed_869_; uint8_t v_res_870_; lean_object* v_r_871_; 
v_x_6241__boxed_869_ = lean_unbox_usize(v_x_867_);
lean_dec(v_x_867_);
v_res_870_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8(v_00_u03b2_865_, v_x_866_, v_x_6241__boxed_869_, v_x_868_);
lean_dec_ref(v_x_868_);
lean_dec_ref(v_x_866_);
v_r_871_ = lean_box(v_res_870_);
return v_r_871_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11(lean_object* v_00_u03b2_872_, lean_object* v_keys_873_, lean_object* v_vals_874_, lean_object* v_heq_875_, lean_object* v_i_876_, lean_object* v_k_877_){
_start:
{
uint8_t v___x_878_; 
v___x_878_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___redArg(v_keys_873_, v_i_876_, v_k_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03b2_879_, lean_object* v_keys_880_, lean_object* v_vals_881_, lean_object* v_heq_882_, lean_object* v_i_883_, lean_object* v_k_884_){
_start:
{
uint8_t v_res_885_; lean_object* v_r_886_; 
v_res_885_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__2_spec__5_spec__7_spec__8_spec__11(v_00_u03b2_879_, v_keys_880_, v_vals_881_, v_heq_882_, v_i_883_, v_k_884_);
lean_dec_ref(v_k_884_);
lean_dec_ref(v_vals_881_);
lean_dec_ref(v_keys_880_);
v_r_886_ = lean_box(v_res_885_);
return v_r_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(lean_object* v_attr_887_, lean_object* v_env_888_, lean_object* v_parserDecl_889_){
_start:
{
lean_object* v_ext_890_; lean_object* v_toEnvExtension_891_; lean_object* v_asyncMode_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_ext_890_ = lean_ctor_get(v_attr_887_, 1);
v_toEnvExtension_891_ = lean_ctor_get(v_ext_890_, 0);
v_asyncMode_892_ = lean_ctor_get(v_toEnvExtension_891_, 2);
v___x_893_ = lean_box(1);
v___x_894_ = lean_box(0);
v___x_895_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_893_, v_ext_890_, v_env_888_, v_asyncMode_892_, v___x_894_);
v___x_896_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_895_, v_parserDecl_889_);
lean_dec(v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f___boxed(lean_object* v_attr_897_, lean_object* v_env_898_, lean_object* v_parserDecl_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(v_attr_897_, v_env_898_, v_parserDecl_899_);
lean_dec(v_parserDecl_899_);
lean_dec_ref(v_attr_897_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(lean_object* v_attr_901_, lean_object* v_env_902_, lean_object* v_parserDecl_903_, lean_object* v_decl_904_){
_start:
{
lean_object* v_ext_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_922_; 
v_ext_905_ = lean_ctor_get(v_attr_901_, 1);
v_isSharedCheck_922_ = !lean_is_exclusive(v_attr_901_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; 
v_unused_923_ = lean_ctor_get(v_attr_901_, 0);
lean_dec(v_unused_923_);
v___x_907_ = v_attr_901_;
v_isShared_908_ = v_isSharedCheck_922_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_ext_905_);
lean_dec(v_attr_901_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_922_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v_toEnvExtension_909_; lean_object* v_addEntryFn_910_; lean_object* v_asyncMode_911_; uint8_t v_logWrites_912_; lean_object* v___x_914_; 
v_toEnvExtension_909_ = lean_ctor_get(v_ext_905_, 0);
lean_inc_ref(v_toEnvExtension_909_);
v_addEntryFn_910_ = lean_ctor_get(v_ext_905_, 3);
lean_inc(v_addEntryFn_910_);
lean_dec_ref(v_ext_905_);
v_asyncMode_911_ = lean_ctor_get(v_toEnvExtension_909_, 2);
lean_inc(v_asyncMode_911_);
v_logWrites_912_ = lean_ctor_get_uint8(v_toEnvExtension_909_, sizeof(void*)*6);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 1, v_decl_904_);
lean_ctor_set(v___x_907_, 0, v_parserDecl_903_);
v___x_914_ = v___x_907_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_parserDecl_903_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_decl_904_);
v___x_914_ = v_reuseFailAlloc_921_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___f_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v___f_915_ = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerCombinatorAttribute___lam__3), 3, 2);
lean_closure_set(v___f_915_, 0, v_addEntryFn_910_);
lean_closure_set(v___f_915_, 1, v___x_914_);
v___x_916_ = lean_box(0);
v___x_917_ = 1;
if (v_logWrites_912_ == 0)
{
lean_object* v___x_918_; 
v___x_918_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_909_, v_env_902_, v___f_915_, v_asyncMode_911_, v___x_916_, v___x_917_);
lean_dec(v_asyncMode_911_);
return v___x_918_;
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_inc_ref(v_toEnvExtension_909_);
v___x_919_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_909_, v_env_902_);
lean_dec_ref(v_env_902_);
v___x_920_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_909_, v___x_919_, v___f_915_, v_asyncMode_911_, v___x_916_, v___x_917_);
lean_dec(v_asyncMode_911_);
return v___x_920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg(lean_object* v_x_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
if (lean_obj_tag(v_x_924_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_a_928_ = lean_ctor_get(v_x_924_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v_x_924_, 1);
v___x_929_ = l_Lean_stringToMessageData(v_a_928_);
v___x_930_ = l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(v___x_929_, v___y_925_, v___y_926_);
return v___x_930_;
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
v_a_931_ = lean_ctor_get(v_x_924_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v_x_924_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v_x_924_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v_x_924_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set_tag(v___x_933_, 0);
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg___boxed(lean_object* v_x_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg(v_x_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
return v_res_943_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = lean_box(0);
v___x_945_ = l_Lean_Elab_abortCommandExceptionId;
v___x_946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___closed__0);
v___x_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg___boxed(lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg();
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___redArg(lean_object* v_constName_952_, uint8_t v_checkMeta_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; lean_object* v_env_958_; uint8_t v___x_959_; 
v___x_957_ = lean_st_ref_get(v___y_955_);
v_env_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc_ref(v_env_958_);
lean_dec(v___x_957_);
lean_inc(v_constName_952_);
v___x_959_ = lean_has_compile_error(v_env_958_, v_constName_952_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v_env_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_960_ = lean_st_ref_get(v___y_955_);
v_env_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc_ref(v_env_961_);
lean_dec(v___x_960_);
v___x_962_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_954_);
v___x_963_ = l_Lean_Environment_evalConst___redArg(v_env_961_, v___x_962_, v_constName_952_, v_checkMeta_953_);
lean_dec(v_constName_952_);
lean_dec_ref(v___x_962_);
lean_dec_ref(v_env_961_);
v___x_964_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg(v___x_963_, v___y_954_, v___y_955_);
return v___x_964_;
}
else
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v___x_966_; lean_object* v_env_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
lean_dec_ref_known(v___x_965_, 1);
v___x_966_ = lean_st_ref_get(v___y_955_);
v_env_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc_ref(v_env_967_);
lean_dec(v___x_966_);
v___x_968_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_954_);
v___x_969_ = l_Lean_Environment_evalConst___redArg(v_env_967_, v___x_968_, v_constName_952_, v_checkMeta_953_);
lean_dec(v_constName_952_);
lean_dec_ref(v___x_968_);
lean_dec_ref(v_env_967_);
v___x_970_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg(v___x_969_, v___y_954_, v___y_955_);
return v___x_970_;
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec(v_constName_952_);
v_a_971_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_965_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_965_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___redArg___boxed(lean_object* v_constName_979_, lean_object* v_checkMeta_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
uint8_t v_checkMeta_boxed_984_; lean_object* v_res_985_; 
v_checkMeta_boxed_984_ = lean_unbox(v_checkMeta_980_);
v_res_985_ = l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___redArg(v_constName_979_, v_checkMeta_boxed_984_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
return v_res_985_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__1(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__0));
v___x_988_ = l_Lean_stringToMessageData(v___x_987_);
return v___x_988_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__3(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__2));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__5(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__4));
v___x_994_ = l_Lean_stringToMessageData(v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(lean_object* v_attr_995_, lean_object* v_parserDecl_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_1000_; lean_object* v_env_1001_; lean_object* v___x_1002_; 
v___x_1000_ = lean_st_ref_get(v_a_998_);
v_env_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc_ref(v_env_1001_);
lean_dec(v___x_1000_);
v___x_1002_ = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor_x3f(v_attr_995_, v_env_1001_, v_parserDecl_996_);
if (lean_obj_tag(v___x_1002_) == 1)
{
lean_object* v_val_1003_; uint8_t v___x_1004_; lean_object* v___x_1005_; 
lean_dec(v_parserDecl_996_);
lean_dec_ref(v_attr_995_);
v_val_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_val_1003_);
lean_dec_ref_known(v___x_1002_, 1);
v___x_1004_ = 1;
v___x_1005_ = l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___redArg(v_val_1003_, v___x_1004_, v_a_997_, v_a_998_);
return v___x_1005_;
}
else
{
lean_object* v_impl_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1024_; 
lean_dec(v___x_1002_);
v_impl_1006_ = lean_ctor_get(v_attr_995_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_attr_995_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v_attr_995_, 1);
lean_dec(v_unused_1025_);
v___x_1008_ = v_attr_995_;
v_isShared_1009_ = v_isSharedCheck_1024_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_impl_1006_);
lean_dec(v_attr_995_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1024_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v_toAttributeImplCore_1010_; lean_object* v_name_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v_toAttributeImplCore_1010_ = lean_ctor_get(v_impl_1006_, 0);
lean_inc_ref(v_toAttributeImplCore_1010_);
lean_dec_ref(v_impl_1006_);
v_name_1011_ = lean_ctor_get(v_toAttributeImplCore_1010_, 1);
lean_inc(v_name_1011_);
lean_dec_ref(v_toAttributeImplCore_1010_);
v___x_1012_ = lean_obj_once(&l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__1, &l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__1_once, _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__1);
v___x_1013_ = l_Lean_MessageData_ofName(v_name_1011_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set_tag(v___x_1008_, 7);
lean_ctor_set(v___x_1008_, 1, v___x_1013_);
lean_ctor_set(v___x_1008_, 0, v___x_1012_);
v___x_1015_ = v___x_1008_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1016_ = lean_obj_once(&l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__3, &l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__3_once, _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__3);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = l_Lean_MessageData_ofName(v_parserDecl_996_);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_obj_once(&l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__5, &l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__5_once, _init_l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___closed__5);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = l_Lean_throwError___at___00Lean_ParserCompiler_registerCombinatorAttribute_spec__0___redArg(v___x_1021_, v_a_997_, v_a_998_);
return v___x_1022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg___boxed(lean_object* v_attr_1026_, lean_object* v_parserDecl_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(v_attr_1026_, v_parserDecl_1027_, v_a_1028_, v_a_1029_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor(lean_object* v_00_u03b1_1032_, lean_object* v_attr_1033_, lean_object* v_parserDecl_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(v_attr_1033_, v_parserDecl_1034_, v_a_1035_, v_a_1036_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___boxed(lean_object* v_00_u03b1_1039_, lean_object* v_attr_1040_, lean_object* v_parserDecl_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor(v_00_u03b1_1039_, v_attr_1040_, v_parserDecl_1041_, v_a_1042_, v_a_1043_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1(lean_object* v_00_u03b1_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___redArg();
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__1(v_00_u03b1_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0(lean_object* v_00_u03b1_1056_, lean_object* v_constName_1057_, uint8_t v_checkMeta_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___redArg(v_constName_1057_, v_checkMeta_1058_, v___y_1059_, v___y_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0___boxed(lean_object* v_00_u03b1_1063_, lean_object* v_constName_1064_, lean_object* v_checkMeta_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
uint8_t v_checkMeta_boxed_1069_; lean_object* v_res_1070_; 
v_checkMeta_boxed_1069_ = lean_unbox(v_checkMeta_1065_);
v_res_1070_ = l_Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0(v_00_u03b1_1063_, v_constName_1064_, v_checkMeta_boxed_1069_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0(lean_object* v_00_u03b1_1071_, lean_object* v_x_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___redArg(v_x_1072_, v___y_1073_, v___y_1074_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1077_, lean_object* v_x_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_ParserCompiler_CombinatorAttribute_runDeclFor_spec__0_spec__0(v_00_u03b1_1077_, v_x_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
return v_res_1082_;
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
