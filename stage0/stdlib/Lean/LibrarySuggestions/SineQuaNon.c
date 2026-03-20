// Lean compiler output
// Module: Lean.LibrarySuggestions.SineQuaNon
// Imports: import all Lean.LibrarySuggestions.SymbolFrequency public import Lean.LibrarySuggestions.Basic
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_LibrarySuggestions_symbolFrequency___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
double log2(double);
double lean_float_mul(double, double);
double lean_float_add(double, double);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_float_decLe(double, double);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
uint8_t l_Lean_Name_cmp(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_LibrarySuggestions_localSymbolFrequency(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Expr_relevantConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_NameSet_ofList(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
double lean_float_div(double, double);
extern double l_instInhabitedFloat;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LibrarySuggestions_isDeniedPremise(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_wasOriginallyTheorem(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Std_TreeSet_ofList___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
lean_object* lean_float_to_string(double);
lean_object* l_Lean_MessageData_paren(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_MVarId_getRelevantConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "sineQuaNon"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(122, 185, 152, 73, 17, 171, 191, 97)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "LibrarySuggestions"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 41, 69, 6, 132, 216, 128, 143)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "SineQuaNon"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(254, 236, 141, 171, 37, 237, 130, 23)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(71, 138, 216, 27, 188, 215, 0, 227)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__11_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 163, 215, 161, 139, 219, 70, 207)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__11_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__11_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__12_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__11_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 92, 188, 202, 182, 14, 162, 68)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__12_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__12_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__13_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__12_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(222, 75, 41, 251, 122, 192, 198, 247)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__13_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__13_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__14_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__14_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__14_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__15_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__13_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__14_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(147, 202, 192, 175, 252, 76, 110, 228)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__15_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__15_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__16_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__16_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__16_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__17_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__15_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__16_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 207, 10, 35, 144, 86, 172, 144)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__17_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__17_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__18_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__17_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 78, 188, 222, 71, 65, 95, 208)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__18_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__18_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__19_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__18_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 225, 145, 21, 9, 28, 253, 246)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__19_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__19_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__20_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__19_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 141, 194, 71, 28, 184, 49, 203)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__20_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__20_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__21_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__21_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__22_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__22_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__22_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__23_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__23_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__24_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__24_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__24_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__25_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__25_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__26_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__26_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "triggerDenyListExt"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 203, 221, 11, 114, 77, 246, 64)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 163, 76, 234, 183, 187, 142, 99)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__11_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__11_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__11_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__12_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__12_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__12_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__11_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__12_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__12_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__13_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__13_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__13_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__14_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__14_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__14_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__15_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__13_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__15_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__15_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__14_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__15_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__15_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__16_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GE"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__16_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__16_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__17_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__17_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__17_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__18_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__16_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 169, 4, 72, 62, 21, 91, 24)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__18_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__18_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__17_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(71, 88, 92, 156, 129, 215, 23, 77)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__18_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__18_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__19_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__19_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__19_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__20_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__20_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__20_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__21_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__19_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__21_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__21_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__20_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__21_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__21_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__22_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__22_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__22_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__23_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__23_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__23_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__24_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__22_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__24_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__24_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__23_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__24_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__24_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__25_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__25_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__25_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__26_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__22_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__26_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__26_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__25_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 26, 8, 228, 104, 32, 82, 85)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__26_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__26_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__27_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__27_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__27_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__28_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__22_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__28_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__28_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__27_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 191, 239, 225, 113, 224, 109, 182)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__28_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__28_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__29_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "xor"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__29_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__29_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__30_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__22_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__30_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__30_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__29_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(159, 35, 146, 118, 24, 65, 174, 144)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__30_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__30_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__31_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__31_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__31_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__32_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__22_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__32_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__32_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__31_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__32_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__32_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__33_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__33_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__33_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__34_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__22_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__34_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__34_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__33_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__34_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__34_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__35_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__35_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__35_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__36_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__35_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__36_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__36_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__37_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__37_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__37_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__38_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__37_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__38_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__38_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__39_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__39_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__39_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__40_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__39_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__40_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__40_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__41_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Xor"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__41_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__41_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__42_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__41_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 232, 165, 211, 128, 35, 249, 51)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__42_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__42_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__43_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__43_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__43_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__44_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__43_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__44_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__44_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__45_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__45_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__45_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__46_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__45_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__46_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__46_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__47_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__47_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__47_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__48_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__47_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__48_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__48_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__49_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__49_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__49_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__50_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__49_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__50_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__50_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__51_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__51_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__51_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__52_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__49_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__52_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__52_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__51_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__52_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__52_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__53_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "SizeOf"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__53_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__53_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__54_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__53_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(65, 190, 244, 45, 165, 196, 61, 198)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__54_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__54_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__55_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "sizeOf"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__55_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__55_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__56_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__53_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(65, 190, 244, 45, 165, 196, 61, 198)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__56_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__56_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__55_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 205, 72, 249, 57, 72, 20, 171)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__56_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__56_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__57_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__56_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__57_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__57_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__58_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__54_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__57_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__58_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__58_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__59_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__52_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__58_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__59_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__59_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__60_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__50_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__59_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__60_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__60_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__61_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__48_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__60_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__61_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__61_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__62_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__46_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__61_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__62_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__62_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__63_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__44_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__62_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__63_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__63_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__64_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__42_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__63_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__64_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__64_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__65_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__40_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__64_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__65_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__65_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__66_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__38_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__65_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__66_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__66_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__67_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__36_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__66_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__67_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__67_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__68_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__34_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__67_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__68_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__68_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__69_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__32_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__68_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__69_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__69_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__70_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__30_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__69_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__70_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__70_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__71_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__28_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__70_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__71_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__71_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__72_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__26_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__71_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__72_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__72_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__73_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__24_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__72_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__73_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__73_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__74_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__21_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__73_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__74_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__74_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__75_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__18_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__74_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__75_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__75_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__76_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__15_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__75_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__76_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__76_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__77_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__12_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__76_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__77_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__77_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__78_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__77_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__78_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__78_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__79_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__78_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__79_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__79_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__80_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__79_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__80_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__80_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__81_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__81_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__82_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__82_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__83_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__83_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerDenyListExt;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1_spec__2(double, double, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1(double, double, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT double l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__2(lean_object*, size_t, size_t, double);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols(lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__0 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__0_value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__1 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__1_value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__2 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__2_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__3_value_aux_0),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__3_value_aux_1),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__3_value_aux_2),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__3 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__3_value;
static const lean_array_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__4 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__4_value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__5 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__5_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__6_value_aux_0),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__6_value_aux_1),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__6_value_aux_2),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__6 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__6_value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__7 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__7_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__8 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__8_value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__9 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__9_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__10_value_aux_0),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__10_value_aux_1),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__10_value_aux_2),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__9_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__10 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__10_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__11;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__12;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__13 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__13_value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__14 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__14_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__15_value_aux_0),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__15_value_aux_1),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__13_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__15_value_aux_2),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__14_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__15 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__15_value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__16 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__16_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__17_value_aux_0),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__17_value_aux_1),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__13_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__17_value_aux_2),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__16_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__17 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__17_value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__18 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__18_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__19;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__20;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__21 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__21_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__21_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__22 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__22_value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__23 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__23_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__24;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__25;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__26;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__27;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__28;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__29;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__30;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__31;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≤_"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__32 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__32_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__32_value),LEAN_SCALAR_PTR_LITERAL(111, 3, 61, 112, 38, 138, 106, 121)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__33 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__33_value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cdot"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__34 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__34_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__35_value_aux_0),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__35_value_aux_1),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__13_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__35_value_aux_2),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__34_value),LEAN_SCALAR_PTR_LITERAL(215, 94, 65, 66, 49, 100, 151, 85)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__35 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__35_value;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "·"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__36 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__36_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__37;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__38;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__39;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__40;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__41;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≤"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__42 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__42_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__43;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__44;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__45;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__46;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__47;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__48 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__48_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__49;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__50;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__51;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__52;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__53;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__54;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__55;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__56;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__57;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__58;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__59;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger___closed__0 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger(lean_object*, lean_object*, lean_object*, double);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__2(double, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers___closed__0 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers(lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___lam__0(lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg___closed__0_value;
static const lean_array_object l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__0;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "sine qua non premise selection extension"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object*);
static const lean_array_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "sineQueNon"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(67, 84, 59, 241, 113, 198, 42, 47)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_array_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_228879371____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_228879371____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersRef;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___closed__0 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___closed__0_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg(lean_object*, double, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore(lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg(double, double, double, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__0_value;
static const lean_ctor_object l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__0_value)}};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__1_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__2;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__3;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__7___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__4(double, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "acceptedTheorems: "};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__0 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__0_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__1;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\npastTriggers: "};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__2 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__2_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__3;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\ntriggerQueue: "};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__4 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__4_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__5;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "\nqueuedTheorems: "};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__6 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__6_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go(lean_object*, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3(double, double, double, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNon(lean_object*, lean_object*, double, double, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_sineQuaNonSelector(double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_sineQuaNonSelector___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__21_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_unsigned_to_nat(4180265299u);
v___x_50_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__20_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_));
v___x_51_ = l_Lean_Name_num___override(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__23_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__22_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_));
v___x_54_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__21_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__21_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__21_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_);
v___x_55_ = l_Lean_Name_str___override(v___x_54_, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__25_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__24_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_));
v___x_58_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__23_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__23_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__23_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_);
v___x_59_ = l_Lean_Name_str___override(v___x_58_, v___x_57_);
return v___x_59_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__26_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_unsigned_to_nat(2u);
v___x_61_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__25_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__25_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__25_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_);
v___x_62_ = l_Lean_Name_num___override(v___x_61_, v___x_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_64_; uint8_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_64_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_));
v___x_65_ = 0;
v___x_66_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__26_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__26_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2__once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__26_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_);
v___x_67_ = l_Lean_registerTraceClass(v___x_64_, v___x_65_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2____boxed(lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_();
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_(lean_object* v_es_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_array_mk(v_es_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_72_, size_t v_i_73_, size_t v_stop_74_, lean_object* v_b_75_){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = lean_usize_dec_eq(v_i_73_, v_stop_74_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; size_t v___x_79_; size_t v___x_80_; 
v___x_77_ = lean_array_uget_borrowed(v_as_72_, v_i_73_);
lean_inc(v___x_77_);
v___x_78_ = l_Lean_NameSet_insert(v_b_75_, v___x_77_);
v___x_79_ = ((size_t)1ULL);
v___x_80_ = lean_usize_add(v_i_73_, v___x_79_);
v_i_73_ = v___x_80_;
v_b_75_ = v___x_78_;
goto _start;
}
else
{
return v_b_75_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_82_, lean_object* v_i_83_, lean_object* v_stop_84_, lean_object* v_b_85_){
_start:
{
size_t v_i_boxed_86_; size_t v_stop_boxed_87_; lean_object* v_res_88_; 
v_i_boxed_86_ = lean_unbox_usize(v_i_83_);
lean_dec(v_i_83_);
v_stop_boxed_87_ = lean_unbox_usize(v_stop_84_);
lean_dec(v_stop_84_);
v_res_88_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0_spec__0(v_as_82_, v_i_boxed_86_, v_stop_boxed_87_, v_b_85_);
lean_dec_ref(v_as_82_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_89_, size_t v_i_90_, size_t v_stop_91_, lean_object* v_b_92_){
_start:
{
lean_object* v___y_94_; uint8_t v___x_98_; 
v___x_98_ = lean_usize_dec_eq(v_i_90_, v_stop_91_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_99_ = lean_array_uget_borrowed(v_as_89_, v_i_90_);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_array_get_size(v___x_99_);
v___x_102_ = lean_nat_dec_lt(v___x_100_, v___x_101_);
if (v___x_102_ == 0)
{
v___y_94_ = v_b_92_;
goto v___jp_93_;
}
else
{
uint8_t v___x_103_; 
v___x_103_ = lean_nat_dec_le(v___x_101_, v___x_101_);
if (v___x_103_ == 0)
{
if (v___x_102_ == 0)
{
v___y_94_ = v_b_92_;
goto v___jp_93_;
}
else
{
size_t v___x_104_; size_t v___x_105_; lean_object* v___x_106_; 
v___x_104_ = ((size_t)0ULL);
v___x_105_ = lean_usize_of_nat(v___x_101_);
v___x_106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0_spec__0(v___x_99_, v___x_104_, v___x_105_, v_b_92_);
v___y_94_ = v___x_106_;
goto v___jp_93_;
}
}
else
{
size_t v___x_107_; size_t v___x_108_; lean_object* v___x_109_; 
v___x_107_ = ((size_t)0ULL);
v___x_108_ = lean_usize_of_nat(v___x_101_);
v___x_109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0_spec__0(v___x_99_, v___x_107_, v___x_108_, v_b_92_);
v___y_94_ = v___x_109_;
goto v___jp_93_;
}
}
}
else
{
return v_b_92_;
}
v___jp_93_:
{
size_t v___x_95_; size_t v___x_96_; 
v___x_95_ = ((size_t)1ULL);
v___x_96_ = lean_usize_add(v_i_90_, v___x_95_);
v_i_90_ = v___x_96_;
v_b_92_ = v___y_94_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_110_, lean_object* v_i_111_, lean_object* v_stop_112_, lean_object* v_b_113_){
_start:
{
size_t v_i_boxed_114_; size_t v_stop_boxed_115_; lean_object* v_res_116_; 
v_i_boxed_114_ = lean_unbox_usize(v_i_111_);
lean_dec(v_i_111_);
v_stop_boxed_115_ = lean_unbox_usize(v_stop_112_);
lean_dec(v_stop_112_);
v_res_116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0_spec__1(v_as_110_, v_i_boxed_114_, v_stop_boxed_115_, v_b_113_);
lean_dec_ref(v_as_110_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0(lean_object* v_initState_117_, lean_object* v_as_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_array_get_size(v_as_118_);
v___x_121_ = lean_nat_dec_lt(v___x_119_, v___x_120_);
if (v___x_121_ == 0)
{
return v_initState_117_;
}
else
{
uint8_t v___x_122_; 
v___x_122_ = lean_nat_dec_le(v___x_120_, v___x_120_);
if (v___x_122_ == 0)
{
if (v___x_121_ == 0)
{
return v_initState_117_;
}
else
{
size_t v___x_123_; size_t v___x_124_; lean_object* v___x_125_; 
v___x_123_ = ((size_t)0ULL);
v___x_124_ = lean_usize_of_nat(v___x_120_);
v___x_125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0_spec__1(v_as_118_, v___x_123_, v___x_124_, v_initState_117_);
return v___x_125_;
}
}
else
{
size_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; 
v___x_126_ = ((size_t)0ULL);
v___x_127_ = lean_usize_of_nat(v___x_120_);
v___x_128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0_spec__1(v_as_118_, v___x_126_, v___x_127_, v_initState_117_);
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_129_, lean_object* v_as_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0(v_initState_129_, v_as_130_);
lean_dec_ref(v_as_130_);
return v_res_131_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__81_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = ((lean_object*)(l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__80_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_));
v___x_303_ = l_Lean_NameSet_ofList(v___x_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__82_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_obj_once(&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__81_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_, &l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__81_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__once, _init_l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__81_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_);
v___x_305_ = lean_alloc_closure((void*)(l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__spec__0___boxed), 2, 1);
lean_closure_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__83_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___f_308_; lean_object* v___x_309_; lean_object* v___f_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_306_ = lean_box(2);
v___x_307_ = lean_box(0);
v___f_308_ = ((lean_object*)(l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_));
v___x_309_ = lean_obj_once(&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__82_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_, &l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__82_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__once, _init_l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__82_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_);
v___f_310_ = ((lean_object*)(l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_));
v___x_311_ = ((lean_object*)(l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_));
v___x_312_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v___f_310_);
lean_ctor_set(v___x_312_, 2, v___x_309_);
lean_ctor_set(v___x_312_, 3, v___f_308_);
lean_ctor_set(v___x_312_, 4, v___x_307_);
lean_ctor_set(v___x_312_, 5, v___x_306_);
lean_ctor_set(v___x_312_, 6, v___x_307_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_obj_once(&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__83_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_, &l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__83_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2__once, _init_l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__83_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_);
v___x_315_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2____boxed(lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_();
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1_spec__2(double v___y_318_, double v_maxTolerance_319_, lean_object* v_as_320_, size_t v_i_321_, size_t v_stop_322_, lean_object* v_b_323_){
_start:
{
lean_object* v___y_325_; uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_eq(v_i_321_, v_stop_322_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v_fst_331_; lean_object* v_snd_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_346_; 
v___x_330_ = lean_array_uget(v_as_320_, v_i_321_);
v_fst_331_ = lean_ctor_get(v___x_330_, 0);
v_snd_332_ = lean_ctor_get(v___x_330_, 1);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_346_ == 0)
{
v___x_334_ = v___x_330_;
v_isShared_335_ = v_isSharedCheck_346_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_snd_332_);
lean_inc(v_fst_331_);
lean_dec(v___x_330_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_346_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
double v___x_336_; double v___x_337_; uint8_t v___x_338_; 
v___x_336_ = lean_float_mul(v___y_318_, v_maxTolerance_319_);
v___x_337_ = lean_unbox_float(v_snd_332_);
v___x_338_ = lean_float_decLe(v___x_337_, v___x_336_);
if (v___x_338_ == 0)
{
lean_del_object(v___x_334_);
lean_dec(v_snd_332_);
lean_dec(v_fst_331_);
v___y_325_ = v_b_323_;
goto v___jp_324_;
}
else
{
double v___x_339_; double v___x_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_339_ = lean_unbox_float(v_snd_332_);
lean_dec(v_snd_332_);
v___x_340_ = lean_float_div(v___x_339_, v___y_318_);
v___x_341_ = lean_box_float(v___x_340_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 1, v___x_341_);
v___x_343_ = v___x_334_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_fst_331_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v___x_341_);
v___x_343_ = v_reuseFailAlloc_345_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; 
v___x_344_ = lean_array_push(v_b_323_, v___x_343_);
v___y_325_ = v___x_344_;
goto v___jp_324_;
}
}
}
}
else
{
return v_b_323_;
}
v___jp_324_:
{
size_t v___x_326_; size_t v___x_327_; 
v___x_326_ = ((size_t)1ULL);
v___x_327_ = lean_usize_add(v_i_321_, v___x_326_);
v_i_321_ = v___x_327_;
v_b_323_ = v___y_325_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1_spec__2___boxed(lean_object* v___y_347_, lean_object* v_maxTolerance_348_, lean_object* v_as_349_, lean_object* v_i_350_, lean_object* v_stop_351_, lean_object* v_b_352_){
_start:
{
double v___y_3121__boxed_353_; double v_maxTolerance_boxed_354_; size_t v_i_boxed_355_; size_t v_stop_boxed_356_; lean_object* v_res_357_; 
v___y_3121__boxed_353_ = lean_unbox_float(v___y_347_);
lean_dec_ref(v___y_347_);
v_maxTolerance_boxed_354_ = lean_unbox_float(v_maxTolerance_348_);
lean_dec_ref(v_maxTolerance_348_);
v_i_boxed_355_ = lean_unbox_usize(v_i_350_);
lean_dec(v_i_350_);
v_stop_boxed_356_ = lean_unbox_usize(v_stop_351_);
lean_dec(v_stop_351_);
v_res_357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1_spec__2(v___y_3121__boxed_353_, v_maxTolerance_boxed_354_, v_as_349_, v_i_boxed_355_, v_stop_boxed_356_, v_b_352_);
lean_dec_ref(v_as_349_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1(double v___y_360_, double v_maxTolerance_361_, lean_object* v_as_362_, lean_object* v_start_363_, lean_object* v_stop_364_){
_start:
{
lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_365_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1___closed__0));
v___x_366_ = lean_nat_dec_lt(v_start_363_, v_stop_364_);
if (v___x_366_ == 0)
{
return v___x_365_;
}
else
{
lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_367_ = lean_array_get_size(v_as_362_);
v___x_368_ = lean_nat_dec_le(v_stop_364_, v___x_367_);
if (v___x_368_ == 0)
{
uint8_t v___x_369_; 
v___x_369_ = lean_nat_dec_lt(v_start_363_, v___x_367_);
if (v___x_369_ == 0)
{
return v___x_365_;
}
else
{
size_t v___x_370_; size_t v___x_371_; lean_object* v___x_372_; 
v___x_370_ = lean_usize_of_nat(v_start_363_);
v___x_371_ = lean_usize_of_nat(v___x_367_);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1_spec__2(v___y_360_, v_maxTolerance_361_, v_as_362_, v___x_370_, v___x_371_, v___x_365_);
return v___x_372_;
}
}
else
{
size_t v___x_373_; size_t v___x_374_; lean_object* v___x_375_; 
v___x_373_ = lean_usize_of_nat(v_start_363_);
v___x_374_ = lean_usize_of_nat(v_stop_364_);
v___x_375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1_spec__2(v___y_360_, v_maxTolerance_361_, v_as_362_, v___x_373_, v___x_374_, v___x_365_);
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1___boxed(lean_object* v___y_376_, lean_object* v_maxTolerance_377_, lean_object* v_as_378_, lean_object* v_start_379_, lean_object* v_stop_380_){
_start:
{
double v___y_3174__boxed_381_; double v_maxTolerance_boxed_382_; lean_object* v_res_383_; 
v___y_3174__boxed_381_ = lean_unbox_float(v___y_376_);
lean_dec_ref(v___y_376_);
v_maxTolerance_boxed_382_ = lean_unbox_float(v_maxTolerance_377_);
lean_dec_ref(v_maxTolerance_377_);
v_res_383_ = l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1(v___y_3174__boxed_381_, v_maxTolerance_boxed_382_, v_as_378_, v_start_379_, v_stop_380_);
lean_dec(v_stop_380_);
lean_dec(v_start_379_);
lean_dec_ref(v_as_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__0_spec__0(lean_object* v___x_384_, lean_object* v_as_385_, size_t v_i_386_, size_t v_stop_387_, lean_object* v_b_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_a_395_; uint8_t v___x_399_; 
v___x_399_ = lean_usize_dec_eq(v_i_386_, v_stop_387_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = lean_array_uget_borrowed(v_as_385_, v_i_386_);
v___x_401_ = l_Lean_NameSet_contains(v___x_384_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_LibrarySuggestions_symbolFrequency___redArg(v___x_400_, v___y_392_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_404_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref(v___x_402_);
lean_inc(v___y_392_);
lean_inc_ref(v___y_391_);
lean_inc(v___y_390_);
lean_inc_ref(v___y_389_);
v___x_404_ = l_Lean_LibrarySuggestions_localSymbolFrequency(v___x_400_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
lean_dec_ref(v___x_404_);
v___x_406_ = lean_nat_add(v_a_403_, v_a_405_);
lean_dec(v_a_405_);
lean_dec(v_a_403_);
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = lean_nat_dec_eq(v___x_406_, v___x_407_);
if (v___x_408_ == 0)
{
double v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_409_ = lean_float_of_nat(v___x_406_);
v___x_410_ = lean_box_float(v___x_409_);
lean_inc(v___x_400_);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_400_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = lean_array_push(v_b_388_, v___x_411_);
v_a_395_ = v___x_412_;
goto v___jp_394_;
}
else
{
lean_dec(v___x_406_);
v_a_395_ = v_b_388_;
goto v___jp_394_;
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec(v_a_403_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec_ref(v_b_388_);
v_a_413_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_404_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_404_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec_ref(v_b_388_);
v_a_421_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_402_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_402_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
else
{
v_a_395_ = v_b_388_;
goto v___jp_394_;
}
}
else
{
lean_object* v___x_429_; 
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v_b_388_);
return v___x_429_;
}
v___jp_394_:
{
size_t v___x_396_; size_t v___x_397_; 
v___x_396_ = ((size_t)1ULL);
v___x_397_ = lean_usize_add(v_i_386_, v___x_396_);
v_i_386_ = v___x_397_;
v_b_388_ = v_a_395_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__0_spec__0___boxed(lean_object* v___x_430_, lean_object* v_as_431_, lean_object* v_i_432_, lean_object* v_stop_433_, lean_object* v_b_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
size_t v_i_boxed_440_; size_t v_stop_boxed_441_; lean_object* v_res_442_; 
v_i_boxed_440_ = lean_unbox_usize(v_i_432_);
lean_dec(v_i_432_);
v_stop_boxed_441_ = lean_unbox_usize(v_stop_433_);
lean_dec(v_stop_433_);
v_res_442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__0_spec__0(v___x_430_, v_as_431_, v_i_boxed_440_, v_stop_boxed_441_, v_b_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
lean_dec_ref(v_as_431_);
lean_dec(v___x_430_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__0(lean_object* v___x_443_, lean_object* v_as_444_, lean_object* v_start_445_, lean_object* v_stop_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1___closed__0));
v___x_453_ = lean_nat_dec_lt(v_start_445_, v_stop_446_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
return v___x_454_;
}
else
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = lean_array_get_size(v_as_444_);
v___x_456_ = lean_nat_dec_le(v_stop_446_, v___x_455_);
if (v___x_456_ == 0)
{
uint8_t v___x_457_; 
v___x_457_ = lean_nat_dec_lt(v_start_445_, v___x_455_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; 
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_452_);
return v___x_458_;
}
else
{
size_t v___x_459_; size_t v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_usize_of_nat(v_start_445_);
v___x_460_ = lean_usize_of_nat(v___x_455_);
v___x_461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__0_spec__0(v___x_443_, v_as_444_, v___x_459_, v___x_460_, v___x_452_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
return v___x_461_;
}
}
else
{
size_t v___x_462_; size_t v___x_463_; lean_object* v___x_464_; 
v___x_462_ = lean_usize_of_nat(v_start_445_);
v___x_463_ = lean_usize_of_nat(v_stop_446_);
v___x_464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__0_spec__0(v___x_443_, v_as_444_, v___x_462_, v___x_463_, v___x_452_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
return v___x_464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__0___boxed(lean_object* v___x_465_, lean_object* v_as_466_, lean_object* v_start_467_, lean_object* v_stop_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__0(v___x_465_, v_as_466_, v_start_467_, v_stop_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v_stop_468_);
lean_dec(v_start_467_);
lean_dec_ref(v_as_466_);
lean_dec(v___x_465_);
return v_res_474_;
}
}
LEAN_EXPORT double l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__2(lean_object* v_as_475_, size_t v_i_476_, size_t v_stop_477_, double v_b_478_){
_start:
{
double v___y_480_; uint8_t v___x_484_; 
v___x_484_ = lean_usize_dec_eq(v_i_476_, v_stop_477_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v_snd_486_; double v___x_487_; uint8_t v___x_488_; 
v___x_485_ = lean_array_uget_borrowed(v_as_475_, v_i_476_);
v_snd_486_ = lean_ctor_get(v___x_485_, 1);
v___x_487_ = lean_unbox_float(v_snd_486_);
v___x_488_ = lean_float_decLe(v_b_478_, v___x_487_);
if (v___x_488_ == 0)
{
double v___x_489_; 
v___x_489_ = lean_unbox_float(v_snd_486_);
v___y_480_ = v___x_489_;
goto v___jp_479_;
}
else
{
v___y_480_ = v_b_478_;
goto v___jp_479_;
}
}
else
{
return v_b_478_;
}
v___jp_479_:
{
size_t v___x_481_; size_t v___x_482_; 
v___x_481_ = ((size_t)1ULL);
v___x_482_ = lean_usize_add(v_i_476_, v___x_481_);
v_i_476_ = v___x_482_;
v_b_478_ = v___y_480_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__2___boxed(lean_object* v_as_490_, lean_object* v_i_491_, lean_object* v_stop_492_, lean_object* v_b_493_){
_start:
{
size_t v_i_boxed_494_; size_t v_stop_boxed_495_; double v_b_boxed_496_; double v_res_497_; lean_object* v_r_498_; 
v_i_boxed_494_ = lean_unbox_usize(v_i_491_);
lean_dec(v_i_491_);
v_stop_boxed_495_ = lean_unbox_usize(v_stop_492_);
lean_dec(v_stop_492_);
v_b_boxed_496_ = lean_unbox_float(v_b_493_);
lean_dec_ref(v_b_493_);
v_res_497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__2(v_as_490_, v_i_boxed_494_, v_stop_boxed_495_, v_b_boxed_496_);
lean_dec_ref(v_as_490_);
v_r_498_ = lean_box_float(v_res_497_);
return v_r_498_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols___closed__0___boxed__const__1(void){
_start:
{
double v___x_499_; lean_object* v___x_500_; 
v___x_499_ = l_instInhabitedFloat;
v___x_500_ = lean_box_float(v___x_499_);
return v___x_500_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols___closed__0(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_box(0);
v___x_502_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols___closed__0___boxed__const__1;
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_501_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols(lean_object* v_ci_504_, double v_maxTolerance_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = lean_st_ref_get(v_a_509_);
v___x_512_ = l_Lean_ConstantInfo_type(v_ci_504_);
lean_inc(v_a_509_);
lean_inc_ref(v_a_508_);
lean_inc(v_a_507_);
lean_inc_ref(v_a_506_);
v___x_513_ = l_Lean_Expr_relevantConstants(v___x_512_, v_a_506_, v_a_507_, v_a_508_, v_a_509_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_560_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_560_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_560_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_560_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v_env_518_; lean_object* v___x_519_; lean_object* v_toEnvExtension_520_; lean_object* v_asyncMode_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_env_518_ = lean_ctor_get(v___x_511_, 0);
lean_inc_ref(v_env_518_);
lean_dec(v___x_511_);
v___x_519_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerDenyListExt;
v_toEnvExtension_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc_ref(v_toEnvExtension_520_);
v_asyncMode_521_ = lean_ctor_get(v_toEnvExtension_520_, 2);
lean_inc(v_asyncMode_521_);
lean_dec_ref(v_toEnvExtension_520_);
v___x_522_ = lean_box(1);
v___x_523_ = lean_box(0);
v___x_524_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_522_, v___x_519_, v_env_518_, v_asyncMode_521_, v___x_523_);
lean_dec(v_asyncMode_521_);
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = lean_array_get_size(v_a_514_);
v___x_527_ = l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__0(v___x_524_, v_a_514_, v___x_525_, v___x_526_, v_a_506_, v_a_507_, v_a_508_, v_a_509_);
lean_dec(v_a_514_);
lean_dec(v___x_524_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_559_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_559_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_559_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_559_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; double v___y_534_; uint8_t v___x_539_; 
v___x_532_ = lean_array_get_size(v_a_528_);
v___x_539_ = lean_nat_dec_eq(v___x_532_, v___x_525_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v_snd_542_; uint8_t v___x_543_; 
lean_del_object(v___x_516_);
v___x_540_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols___closed__0, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols___closed__0_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols___closed__0);
v___x_541_ = lean_array_get_borrowed(v___x_540_, v_a_528_, v___x_525_);
v_snd_542_ = lean_ctor_get(v___x_541_, 1);
v___x_543_ = lean_nat_dec_lt(v___x_525_, v___x_532_);
if (v___x_543_ == 0)
{
double v___x_544_; 
v___x_544_ = lean_unbox_float(v_snd_542_);
v___y_534_ = v___x_544_;
goto v___jp_533_;
}
else
{
uint8_t v___x_545_; 
v___x_545_ = lean_nat_dec_le(v___x_532_, v___x_532_);
if (v___x_545_ == 0)
{
if (v___x_543_ == 0)
{
double v___x_546_; 
v___x_546_ = lean_unbox_float(v_snd_542_);
v___y_534_ = v___x_546_;
goto v___jp_533_;
}
else
{
size_t v___x_547_; size_t v___x_548_; double v___x_549_; double v___x_550_; 
v___x_547_ = ((size_t)0ULL);
v___x_548_ = lean_usize_of_nat(v___x_532_);
v___x_549_ = lean_unbox_float(v_snd_542_);
v___x_550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__2(v_a_528_, v___x_547_, v___x_548_, v___x_549_);
v___y_534_ = v___x_550_;
goto v___jp_533_;
}
}
else
{
size_t v___x_551_; size_t v___x_552_; double v___x_553_; double v___x_554_; 
v___x_551_ = ((size_t)0ULL);
v___x_552_ = lean_usize_of_nat(v___x_532_);
v___x_553_ = lean_unbox_float(v_snd_542_);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__2(v_a_528_, v___x_551_, v___x_552_, v___x_553_);
v___y_534_ = v___x_554_;
goto v___jp_533_;
}
}
}
else
{
lean_object* v___x_555_; lean_object* v___x_557_; 
lean_del_object(v___x_530_);
lean_dec(v_a_528_);
v___x_555_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1___closed__0));
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_555_);
v___x_557_ = v___x_516_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
v___jp_533_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1(v___y_534_, v_maxTolerance_505_, v_a_528_, v___x_525_, v___x_532_);
lean_dec(v_a_528_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_535_);
v___x_537_ = v___x_530_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
else
{
lean_del_object(v___x_516_);
return v___x_527_;
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec(v___x_511_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
v_a_561_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_513_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_513_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols___boxed(lean_object* v_ci_569_, lean_object* v_maxTolerance_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
double v_maxTolerance_boxed_576_; lean_object* v_res_577_; 
v_maxTolerance_boxed_576_ = lean_unbox_float(v_maxTolerance_570_);
lean_dec_ref(v_maxTolerance_570_);
v_res_577_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols(v_ci_569_, v_maxTolerance_boxed_576_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
lean_dec_ref(v_ci_569_);
return v_res_577_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__11(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__9));
v___x_604_ = l_Lean_mkAtom(v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__12(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__11, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__11_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__11);
v___x_606_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__4));
v___x_607_ = lean_array_push(v___x_606_, v___x_605_);
return v___x_607_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__19(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__18));
v___x_623_ = l_Lean_mkAtom(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__20(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__19, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__19_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__19);
v___x_625_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__4));
v___x_626_ = lean_array_push(v___x_625_, v___x_624_);
return v___x_626_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__24(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__23));
v___x_632_ = lean_string_utf8_byte_size(v___x_631_);
return v___x_632_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__25(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_633_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__24, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__24_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__24);
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__23));
v___x_636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v___x_634_);
lean_ctor_set(v___x_636_, 2, v___x_633_);
return v___x_636_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__26(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_637_ = lean_box(0);
v___x_638_ = lean_box(0);
v___x_639_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__25, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__25_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__25);
v___x_640_ = lean_box(2);
v___x_641_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v___x_639_);
lean_ctor_set(v___x_641_, 2, v___x_638_);
lean_ctor_set(v___x_641_, 3, v___x_637_);
return v___x_641_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__27(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__26, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__26_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__26);
v___x_643_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__4));
v___x_644_ = lean_array_push(v___x_643_, v___x_642_);
return v___x_644_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__28(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_645_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__27, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__27_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__27);
v___x_646_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__22));
v___x_647_ = lean_box(2);
v___x_648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v___x_646_);
lean_ctor_set(v___x_648_, 2, v___x_645_);
return v___x_648_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__29(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_649_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__28, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__28_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__28);
v___x_650_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__20, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__20_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__20);
v___x_651_ = lean_array_push(v___x_650_, v___x_649_);
return v___x_651_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__30(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_652_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__29, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__29_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__29);
v___x_653_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__17));
v___x_654_ = lean_box(2);
v___x_655_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v___x_653_);
lean_ctor_set(v___x_655_, 2, v___x_652_);
return v___x_655_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__31(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__30, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__30_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__30);
v___x_657_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__4));
v___x_658_ = lean_array_push(v___x_657_, v___x_656_);
return v___x_658_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__37(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__36));
v___x_670_ = l_Lean_mkAtom(v___x_669_);
return v___x_670_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__38(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__37, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__37_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__37);
v___x_672_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__4));
v___x_673_ = lean_array_push(v___x_672_, v___x_671_);
return v___x_673_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__39(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__28, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__28_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__28);
v___x_675_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__38, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__38_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__38);
v___x_676_ = lean_array_push(v___x_675_, v___x_674_);
return v___x_676_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__40(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_677_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__39, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__39_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__39);
v___x_678_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__35));
v___x_679_ = lean_box(2);
v___x_680_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v___x_678_);
lean_ctor_set(v___x_680_, 2, v___x_677_);
return v___x_680_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__41(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__40, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__40_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__40);
v___x_682_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__4));
v___x_683_ = lean_array_push(v___x_682_, v___x_681_);
return v___x_683_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__43(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__42));
v___x_686_ = l_Lean_mkAtom(v___x_685_);
return v___x_686_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__44(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__43, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__43_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__43);
v___x_688_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__41, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__41_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__41);
v___x_689_ = lean_array_push(v___x_688_, v___x_687_);
return v___x_689_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__45(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__40, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__40_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__40);
v___x_691_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__44, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__44_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__44);
v___x_692_ = lean_array_push(v___x_691_, v___x_690_);
return v___x_692_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__46(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_693_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__45, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__45_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__45);
v___x_694_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__33));
v___x_695_ = lean_box(2);
v___x_696_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___x_694_);
lean_ctor_set(v___x_696_, 2, v___x_693_);
return v___x_696_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__47(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__46, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__46_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__46);
v___x_698_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__31, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__31_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__31);
v___x_699_ = lean_array_push(v___x_698_, v___x_697_);
return v___x_699_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__49(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__48));
v___x_702_ = l_Lean_mkAtom(v___x_701_);
return v___x_702_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__50(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__49, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__49_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__49);
v___x_704_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__47, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__47_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__47);
v___x_705_ = lean_array_push(v___x_704_, v___x_703_);
return v___x_705_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__51(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_706_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__50, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__50_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__50);
v___x_707_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__15));
v___x_708_ = lean_box(2);
v___x_709_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___x_707_);
lean_ctor_set(v___x_709_, 2, v___x_706_);
return v___x_709_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__52(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_710_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__51, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__51_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__51);
v___x_711_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__12, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__12_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__12);
v___x_712_ = lean_array_push(v___x_711_, v___x_710_);
return v___x_712_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__53(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_713_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__52, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__52_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__52);
v___x_714_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__10));
v___x_715_ = lean_box(2);
v___x_716_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set(v___x_716_, 1, v___x_714_);
lean_ctor_set(v___x_716_, 2, v___x_713_);
return v___x_716_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__54(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__53, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__53_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__53);
v___x_718_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__4));
v___x_719_ = lean_array_push(v___x_718_, v___x_717_);
return v___x_719_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__55(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_720_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__54, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__54_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__54);
v___x_721_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__8));
v___x_722_ = lean_box(2);
v___x_723_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v___x_721_);
lean_ctor_set(v___x_723_, 2, v___x_720_);
return v___x_723_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__56(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_724_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__55, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__55_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__55);
v___x_725_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__4));
v___x_726_ = lean_array_push(v___x_725_, v___x_724_);
return v___x_726_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__57(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_727_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__56, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__56_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__56);
v___x_728_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__6));
v___x_729_ = lean_box(2);
v___x_730_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v___x_728_);
lean_ctor_set(v___x_730_, 2, v___x_727_);
return v___x_730_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__58(void){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__57, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__57_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__57);
v___x_732_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__4));
v___x_733_ = lean_array_push(v___x_732_, v___x_731_);
return v___x_733_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__59(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_734_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__58, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__58_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__58);
v___x_735_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__3));
v___x_736_ = lean_box(2);
v___x_737_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v___x_735_);
lean_ctor_set(v___x_737_, 2, v___x_734_);
return v___x_737_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3(void){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__59, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__59_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3___closed__59);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___redArg(lean_object* v_r_739_, lean_object* v_a_740_, lean_object* v_x_741_){
_start:
{
if (lean_obj_tag(v_x_741_) == 0)
{
lean_object* v___x_742_; 
lean_dec_ref(v_r_739_);
v___x_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_742_, 0, v_a_740_);
lean_ctor_set(v___x_742_, 1, v_x_741_);
return v___x_742_;
}
else
{
lean_object* v_head_743_; lean_object* v_tail_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v_head_743_ = lean_ctor_get(v_x_741_, 0);
v_tail_744_ = lean_ctor_get(v_x_741_, 1);
lean_inc_ref(v_r_739_);
lean_inc(v_head_743_);
lean_inc(v_a_740_);
v___x_745_ = lean_apply_2(v_r_739_, v_a_740_, v_head_743_);
v___x_746_ = lean_unbox(v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_754_; 
lean_inc(v_tail_744_);
lean_inc(v_head_743_);
v_isSharedCheck_754_ = !lean_is_exclusive(v_x_741_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; lean_object* v_unused_756_; 
v_unused_755_ = lean_ctor_get(v_x_741_, 1);
lean_dec(v_unused_755_);
v_unused_756_ = lean_ctor_get(v_x_741_, 0);
lean_dec(v_unused_756_);
v___x_748_ = v_x_741_;
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
else
{
lean_dec(v_x_741_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___redArg(v_r_739_, v_a_740_, v_tail_744_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_head_743_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v___x_750_);
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
lean_object* v___x_757_; 
lean_dec_ref(v_r_739_);
v___x_757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_757_, 0, v_a_740_);
lean_ctor_set(v___x_757_, 1, v_x_741_);
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert(lean_object* v_00_u03b1_758_, lean_object* v_r_759_, lean_object* v_a_760_, lean_object* v_x_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___redArg(v_r_759_, v_a_760_, v_x_761_);
return v___x_762_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger___lam__0(lean_object* v_x_763_, lean_object* v_y_764_){
_start:
{
lean_object* v_snd_765_; lean_object* v_snd_766_; double v___x_767_; double v___x_768_; uint8_t v___x_769_; 
v_snd_765_ = lean_ctor_get(v_x_763_, 1);
v_snd_766_ = lean_ctor_get(v_y_764_, 1);
v___x_767_ = lean_unbox_float(v_snd_765_);
v___x_768_ = lean_unbox_float(v_snd_766_);
v___x_769_ = lean_float_decLe(v___x_767_, v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger___lam__0___boxed(lean_object* v_x_770_, lean_object* v_y_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger___lam__0(v_x_770_, v_y_771_);
lean_dec_ref(v_y_771_);
lean_dec_ref(v_x_770_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger(lean_object* v_map_775_, lean_object* v_trigger_776_, lean_object* v_decl_777_, double v_tolerance_778_){
_start:
{
lean_object* v___f_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___f_779_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger___closed__0));
v___x_780_ = lean_box_float(v_tolerance_778_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v_decl_777_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = lean_box(0);
v___x_783_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_map_775_, v_trigger_776_, v___x_782_);
v___x_784_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___redArg(v___f_779_, v___x_781_, v___x_783_);
v___x_785_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_trigger_776_, v___x_784_, v_map_775_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger___boxed(lean_object* v_map_786_, lean_object* v_trigger_787_, lean_object* v_decl_788_, lean_object* v_tolerance_789_){
_start:
{
double v_tolerance_boxed_790_; lean_object* v_res_791_; 
v_tolerance_boxed_790_ = lean_unbox_float(v_tolerance_789_);
lean_dec_ref(v_tolerance_789_);
v_res_791_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger(v_map_786_, v_trigger_787_, v_decl_788_, v_tolerance_boxed_790_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__3(lean_object* v___x_792_, lean_object* v_as_793_, size_t v_i_794_, size_t v_stop_795_, lean_object* v_b_796_){
_start:
{
lean_object* v___y_798_; uint8_t v___x_802_; 
v___x_802_ = lean_usize_dec_eq(v_i_794_, v_stop_795_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = lean_array_uget_borrowed(v_as_793_, v_i_794_);
lean_inc(v___x_803_);
lean_inc_ref(v___x_792_);
v___x_804_ = l_Lean_LibrarySuggestions_isDeniedPremise(v___x_792_, v___x_803_, v___x_802_);
if (v___x_804_ == 0)
{
uint8_t v___x_805_; 
lean_inc(v___x_803_);
lean_inc_ref(v___x_792_);
v___x_805_ = l_Lean_wasOriginallyTheorem(v___x_792_, v___x_803_);
if (v___x_805_ == 0)
{
v___y_798_ = v_b_796_;
goto v___jp_797_;
}
else
{
lean_object* v___x_806_; 
lean_inc(v___x_803_);
v___x_806_ = lean_array_push(v_b_796_, v___x_803_);
v___y_798_ = v___x_806_;
goto v___jp_797_;
}
}
else
{
v___y_798_ = v_b_796_;
goto v___jp_797_;
}
}
else
{
lean_dec_ref(v___x_792_);
return v_b_796_;
}
v___jp_797_:
{
size_t v___x_799_; size_t v___x_800_; 
v___x_799_ = ((size_t)1ULL);
v___x_800_ = lean_usize_add(v_i_794_, v___x_799_);
v_i_794_ = v___x_800_;
v_b_796_ = v___y_798_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__3___boxed(lean_object* v___x_807_, lean_object* v_as_808_, lean_object* v_i_809_, lean_object* v_stop_810_, lean_object* v_b_811_){
_start:
{
size_t v_i_boxed_812_; size_t v_stop_boxed_813_; lean_object* v_res_814_; 
v_i_boxed_812_ = lean_unbox_usize(v_i_809_);
lean_dec(v_i_809_);
v_stop_boxed_813_ = lean_unbox_usize(v_stop_810_);
lean_dec(v_stop_810_);
v_res_814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__3(v___x_807_, v_as_808_, v_i_boxed_812_, v_stop_boxed_813_, v_b_811_);
lean_dec_ref(v_as_808_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__1___redArg(lean_object* v_a_815_, lean_object* v_as_816_, size_t v_sz_817_, size_t v_i_818_, lean_object* v_b_819_){
_start:
{
uint8_t v___x_821_; 
v___x_821_ = lean_usize_dec_lt(v_i_818_, v_sz_817_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; 
lean_dec(v_a_815_);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v_b_819_);
return v___x_822_;
}
else
{
lean_object* v_a_823_; lean_object* v_fst_824_; lean_object* v_snd_825_; double v___x_826_; lean_object* v___x_827_; size_t v___x_828_; size_t v___x_829_; 
v_a_823_ = lean_array_uget_borrowed(v_as_816_, v_i_818_);
v_fst_824_ = lean_ctor_get(v_a_823_, 0);
v_snd_825_ = lean_ctor_get(v_a_823_, 1);
v___x_826_ = lean_unbox_float(v_snd_825_);
lean_inc(v_a_815_);
lean_inc(v_fst_824_);
v___x_827_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger(v_b_819_, v_fst_824_, v_a_815_, v___x_826_);
v___x_828_ = ((size_t)1ULL);
v___x_829_ = lean_usize_add(v_i_818_, v___x_828_);
v_i_818_ = v___x_829_;
v_b_819_ = v___x_827_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__1___redArg___boxed(lean_object* v_a_831_, lean_object* v_as_832_, lean_object* v_sz_833_, lean_object* v_i_834_, lean_object* v_b_835_, lean_object* v___y_836_){
_start:
{
size_t v_sz_boxed_837_; size_t v_i_boxed_838_; lean_object* v_res_839_; 
v_sz_boxed_837_ = lean_unbox_usize(v_sz_833_);
lean_dec(v_sz_833_);
v_i_boxed_838_ = lean_unbox_usize(v_i_834_);
lean_dec(v_i_834_);
v_res_839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__1___redArg(v_a_831_, v_as_832_, v_sz_boxed_837_, v_i_boxed_838_, v_b_835_);
lean_dec_ref(v_as_832_);
return v_res_839_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_840_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__0);
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_844_ = lean_unsigned_to_nat(0u);
v___x_845_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
lean_ctor_set(v___x_845_, 2, v___x_844_);
lean_ctor_set(v___x_845_, 3, v___x_843_);
lean_ctor_set(v___x_845_, 4, v___x_843_);
lean_ctor_set(v___x_845_, 5, v___x_843_);
lean_ctor_set(v___x_845_, 6, v___x_843_);
lean_ctor_set(v___x_845_, 7, v___x_843_);
lean_ctor_set(v___x_845_, 8, v___x_843_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = lean_unsigned_to_nat(32u);
v___x_847_ = lean_mk_empty_array_with_capacity(v___x_846_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__4(void){
_start:
{
size_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_849_ = ((size_t)5ULL);
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = lean_unsigned_to_nat(32u);
v___x_852_ = lean_mk_empty_array_with_capacity(v___x_851_);
v___x_853_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_854_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v___x_852_);
lean_ctor_set(v___x_854_, 2, v___x_850_);
lean_ctor_set(v___x_854_, 3, v___x_850_);
lean_ctor_set_usize(v___x_854_, 4, v___x_849_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_855_ = lean_box(1);
v___x_856_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__4);
v___x_857_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___x_856_);
lean_ctor_set(v___x_858_, 2, v___x_855_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_861_ = l_Lean_stringToMessageData(v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_864_ = l_Lean_stringToMessageData(v___x_863_);
return v___x_864_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_867_ = l_Lean_stringToMessageData(v___x_866_);
return v___x_867_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_870_ = l_Lean_stringToMessageData(v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__15(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__14));
v___x_873_ = l_Lean_stringToMessageData(v___x_872_);
return v___x_873_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__17(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__16));
v___x_876_ = l_Lean_stringToMessageData(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__19(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__18));
v___x_879_ = l_Lean_stringToMessageData(v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_880_, lean_object* v_declHint_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; lean_object* v_env_885_; uint8_t v___x_886_; 
v___x_884_ = lean_st_ref_get(v___y_882_);
v_env_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc_ref(v_env_885_);
lean_dec(v___x_884_);
v___x_886_ = l_Lean_Name_isAnonymous(v_declHint_881_);
if (v___x_886_ == 0)
{
uint8_t v_isExporting_887_; 
v_isExporting_887_ = lean_ctor_get_uint8(v_env_885_, sizeof(void*)*8);
if (v_isExporting_887_ == 0)
{
lean_object* v___x_888_; 
lean_dec_ref(v_env_885_);
lean_dec(v_declHint_881_);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v_msg_880_);
return v___x_888_;
}
else
{
lean_object* v___x_889_; uint8_t v___x_890_; 
lean_inc_ref(v_env_885_);
v___x_889_ = l_Lean_Environment_setExporting(v_env_885_, v___x_886_);
lean_inc(v_declHint_881_);
lean_inc_ref(v___x_889_);
v___x_890_ = l_Lean_Environment_contains(v___x_889_, v_declHint_881_, v_isExporting_887_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
lean_dec_ref(v___x_889_);
lean_dec_ref(v_env_885_);
lean_dec(v_declHint_881_);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v_msg_880_);
return v___x_891_;
}
else
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v_c_897_; lean_object* v___x_898_; 
v___x_892_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__2);
v___x_893_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_894_ = l_Lean_Options_empty;
v___x_895_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_895_, 0, v___x_889_);
lean_ctor_set(v___x_895_, 1, v___x_892_);
lean_ctor_set(v___x_895_, 2, v___x_893_);
lean_ctor_set(v___x_895_, 3, v___x_894_);
lean_inc(v_declHint_881_);
v___x_896_ = l_Lean_MessageData_ofConstName(v_declHint_881_, v___x_886_);
v_c_897_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_897_, 0, v___x_895_);
lean_ctor_set(v_c_897_, 1, v___x_896_);
v___x_898_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_885_, v_declHint_881_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
lean_dec_ref(v_env_885_);
lean_dec(v_declHint_881_);
v___x_899_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v_c_897_);
v___x_901_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = l_Lean_MessageData_note(v___x_902_);
v___x_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_904_, 0, v_msg_880_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
else
{
lean_object* v_val_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_941_; 
v_val_906_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_941_ == 0)
{
v___x_908_ = v___x_898_;
v_isShared_909_ = v_isSharedCheck_941_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_val_906_);
lean_dec(v___x_898_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_941_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v_mod_913_; uint8_t v___x_914_; 
v___x_910_ = lean_box(0);
v___x_911_ = l_Lean_Environment_header(v_env_885_);
lean_dec_ref(v_env_885_);
v___x_912_ = l_Lean_EnvironmentHeader_moduleNames(v___x_911_);
v_mod_913_ = lean_array_get(v___x_910_, v___x_912_, v_val_906_);
lean_dec(v_val_906_);
lean_dec_ref(v___x_912_);
v___x_914_ = l_Lean_isPrivateName(v_declHint_881_);
lean_dec(v_declHint_881_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_915_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v_c_897_);
v___x_917_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_Lean_MessageData_ofName(v_mod_913_);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__15);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_920_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = l_Lean_MessageData_note(v___x_922_);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v_msg_880_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
if (v_isShared_909_ == 0)
{
lean_ctor_set_tag(v___x_908_, 0);
lean_ctor_set(v___x_908_, 0, v___x_924_);
v___x_926_ = v___x_908_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_928_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v_c_897_);
v___x_930_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__17);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = l_Lean_MessageData_ofName(v_mod_913_);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___closed__19);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = l_Lean_MessageData_note(v___x_935_);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v_msg_880_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
if (v_isShared_909_ == 0)
{
lean_ctor_set_tag(v___x_908_, 0);
lean_ctor_set(v___x_908_, 0, v___x_937_);
v___x_939_ = v___x_908_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_942_; 
lean_dec_ref(v_env_885_);
lean_dec(v_declHint_881_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v_msg_880_);
return v___x_942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_943_, lean_object* v_declHint_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg(v_msg_943_, v_declHint_944_, v___y_945_);
lean_dec(v___y_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6(lean_object* v_msg_948_, lean_object* v_declHint_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_965_; 
v___x_955_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg(v_msg_948_, v_declHint_949_, v___y_953_);
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_965_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_960_ = l_Lean_unknownIdentifierMessageTag;
v___x_961_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v_a_956_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_961_);
v___x_963_ = v___x_958_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_msg_966_, lean_object* v_declHint_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6(v_msg_966_, v_declHint_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9_spec__10(lean_object* v_msgData_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; lean_object* v_env_981_; lean_object* v___x_982_; lean_object* v_mctx_983_; lean_object* v_lctx_984_; lean_object* v_options_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_980_ = lean_st_ref_get(v___y_978_);
v_env_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc_ref(v_env_981_);
lean_dec(v___x_980_);
v___x_982_ = lean_st_ref_get(v___y_976_);
v_mctx_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc_ref(v_mctx_983_);
lean_dec(v___x_982_);
v_lctx_984_ = lean_ctor_get(v___y_975_, 2);
v_options_985_ = lean_ctor_get(v___y_977_, 2);
lean_inc_ref(v_options_985_);
lean_inc_ref(v_lctx_984_);
v___x_986_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_986_, 0, v_env_981_);
lean_ctor_set(v___x_986_, 1, v_mctx_983_);
lean_ctor_set(v___x_986_, 2, v_lctx_984_);
lean_ctor_set(v___x_986_, 3, v_options_985_);
v___x_987_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v_msgData_974_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9_spec__10___boxed(lean_object* v_msgData_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9_spec__10(v_msgData_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(lean_object* v_msg_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_ref_1002_; lean_object* v___x_1003_; lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1012_; 
v_ref_1002_ = lean_ctor_get(v___y_999_, 5);
v___x_1003_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9_spec__10(v_msg_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1012_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1012_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
lean_inc(v_ref_1002_);
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v_ref_1002_);
lean_ctor_set(v___x_1008_, 1, v_a_1004_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set_tag(v___x_1006_, 1);
lean_ctor_set(v___x_1006_, 0, v___x_1008_);
v___x_1010_ = v___x_1006_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_msg_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(v_msg_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(lean_object* v_ref_1020_, lean_object* v_msg_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_fileName_1027_; lean_object* v_fileMap_1028_; lean_object* v_options_1029_; lean_object* v_currRecDepth_1030_; lean_object* v_maxRecDepth_1031_; lean_object* v_ref_1032_; lean_object* v_currNamespace_1033_; lean_object* v_openDecls_1034_; lean_object* v_initHeartbeats_1035_; lean_object* v_maxHeartbeats_1036_; lean_object* v_quotContext_1037_; lean_object* v_currMacroScope_1038_; uint8_t v_diag_1039_; lean_object* v_cancelTk_x3f_1040_; uint8_t v_suppressElabErrors_1041_; lean_object* v_inheritedTraceOptions_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1051_; 
v_fileName_1027_ = lean_ctor_get(v___y_1024_, 0);
v_fileMap_1028_ = lean_ctor_get(v___y_1024_, 1);
v_options_1029_ = lean_ctor_get(v___y_1024_, 2);
v_currRecDepth_1030_ = lean_ctor_get(v___y_1024_, 3);
v_maxRecDepth_1031_ = lean_ctor_get(v___y_1024_, 4);
v_ref_1032_ = lean_ctor_get(v___y_1024_, 5);
v_currNamespace_1033_ = lean_ctor_get(v___y_1024_, 6);
v_openDecls_1034_ = lean_ctor_get(v___y_1024_, 7);
v_initHeartbeats_1035_ = lean_ctor_get(v___y_1024_, 8);
v_maxHeartbeats_1036_ = lean_ctor_get(v___y_1024_, 9);
v_quotContext_1037_ = lean_ctor_get(v___y_1024_, 10);
v_currMacroScope_1038_ = lean_ctor_get(v___y_1024_, 11);
v_diag_1039_ = lean_ctor_get_uint8(v___y_1024_, sizeof(void*)*14);
v_cancelTk_x3f_1040_ = lean_ctor_get(v___y_1024_, 12);
v_suppressElabErrors_1041_ = lean_ctor_get_uint8(v___y_1024_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1042_ = lean_ctor_get(v___y_1024_, 13);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___y_1024_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1044_ = v___y_1024_;
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_inheritedTraceOptions_1042_);
lean_inc(v_cancelTk_x3f_1040_);
lean_inc(v_currMacroScope_1038_);
lean_inc(v_quotContext_1037_);
lean_inc(v_maxHeartbeats_1036_);
lean_inc(v_initHeartbeats_1035_);
lean_inc(v_openDecls_1034_);
lean_inc(v_currNamespace_1033_);
lean_inc(v_ref_1032_);
lean_inc(v_maxRecDepth_1031_);
lean_inc(v_currRecDepth_1030_);
lean_inc(v_options_1029_);
lean_inc(v_fileMap_1028_);
lean_inc(v_fileName_1027_);
lean_dec(v___y_1024_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v_ref_1046_; lean_object* v___x_1048_; 
v_ref_1046_ = l_Lean_replaceRef(v_ref_1020_, v_ref_1032_);
lean_dec(v_ref_1032_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 5, v_ref_1046_);
v___x_1048_ = v___x_1044_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_fileName_1027_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_fileMap_1028_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_options_1029_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v_currRecDepth_1030_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v_maxRecDepth_1031_);
lean_ctor_set(v_reuseFailAlloc_1050_, 5, v_ref_1046_);
lean_ctor_set(v_reuseFailAlloc_1050_, 6, v_currNamespace_1033_);
lean_ctor_set(v_reuseFailAlloc_1050_, 7, v_openDecls_1034_);
lean_ctor_set(v_reuseFailAlloc_1050_, 8, v_initHeartbeats_1035_);
lean_ctor_set(v_reuseFailAlloc_1050_, 9, v_maxHeartbeats_1036_);
lean_ctor_set(v_reuseFailAlloc_1050_, 10, v_quotContext_1037_);
lean_ctor_set(v_reuseFailAlloc_1050_, 11, v_currMacroScope_1038_);
lean_ctor_set(v_reuseFailAlloc_1050_, 12, v_cancelTk_x3f_1040_);
lean_ctor_set(v_reuseFailAlloc_1050_, 13, v_inheritedTraceOptions_1042_);
lean_ctor_set_uint8(v_reuseFailAlloc_1050_, sizeof(void*)*14, v_diag_1039_);
lean_ctor_set_uint8(v_reuseFailAlloc_1050_, sizeof(void*)*14 + 1, v_suppressElabErrors_1041_);
v___x_1048_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(v_msg_1021_, v___y_1022_, v___y_1023_, v___x_1048_, v___y_1025_);
lean_dec_ref(v___x_1048_);
return v___x_1049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1052_, lean_object* v_msg_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_1052_, v_msg_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v_ref_1052_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_ref_1060_, lean_object* v_msg_1061_, lean_object* v_declHint_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___x_1068_; lean_object* v_a_1069_; lean_object* v___x_1070_; 
v___x_1068_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6(v_msg_1061_, v_declHint_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref(v___x_1068_);
v___x_1070_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_1060_, v_a_1069_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_ref_1071_, lean_object* v_msg_1072_, lean_object* v_declHint_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_1071_, v_msg_1072_, v_declHint_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v_ref_1071_);
return v_res_1079_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1082_ = l_Lean_stringToMessageData(v___x_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1085_ = l_Lean_stringToMessageData(v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1086_, lean_object* v_constName_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1093_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1094_ = 0;
lean_inc(v_constName_1087_);
v___x_1095_ = l_Lean_MessageData_ofConstName(v_constName_1087_, v___x_1094_);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1093_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_1086_, v___x_1098_, v_constName_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1100_, lean_object* v_constName_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg(v_ref_1100_, v_constName_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v_ref_1100_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0___redArg(lean_object* v_constName_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_ref_1114_; lean_object* v___x_1115_; 
v_ref_1114_ = lean_ctor_get(v___y_1111_, 5);
lean_inc(v_ref_1114_);
v___x_1115_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg(v_ref_1114_, v_constName_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v_ref_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0___redArg(v_constName_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0(lean_object* v_constName_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1129_; lean_object* v_env_1130_; uint8_t v___x_1131_; lean_object* v___x_1132_; 
v___x_1129_ = lean_st_ref_get(v___y_1127_);
v_env_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc_ref(v_env_1130_);
lean_dec(v___x_1129_);
v___x_1131_ = 0;
lean_inc(v_constName_1123_);
v___x_1132_ = l_Lean_Environment_find_x3f(v_env_1130_, v_constName_1123_, v___x_1131_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0___redArg(v_constName_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
return v___x_1133_;
}
else
{
lean_object* v_val_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec_ref(v___y_1126_);
lean_dec(v_constName_1123_);
v_val_1134_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1132_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_val_1134_);
lean_dec(v___x_1132_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set_tag(v___x_1136_, 0);
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_val_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0___boxed(lean_object* v_constName_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0(v_constName_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__2(double v_maxTolerance_1149_, lean_object* v_as_1150_, size_t v_sz_1151_, size_t v_i_1152_, lean_object* v_b_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
uint8_t v___x_1159_; 
v___x_1159_ = lean_usize_dec_lt(v_i_1152_, v_sz_1151_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_b_1153_);
return v___x_1160_;
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1162_; 
v_a_1161_ = lean_array_uget_borrowed(v_as_1150_, v_i_1152_);
lean_inc_ref(v___y_1156_);
lean_inc(v_a_1161_);
v___x_1162_ = l_Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0(v_a_1161_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1164_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref(v___x_1162_);
lean_inc(v___y_1157_);
lean_inc_ref(v___y_1156_);
lean_inc(v___y_1155_);
lean_inc_ref(v___y_1154_);
v___x_1164_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols(v_a_1163_, v_maxTolerance_1149_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v_a_1163_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; size_t v_sz_1166_; size_t v___x_1167_; lean_object* v___x_1168_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref(v___x_1164_);
v_sz_1166_ = lean_array_size(v_a_1165_);
v___x_1167_ = ((size_t)0ULL);
lean_inc(v_a_1161_);
v___x_1168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__1___redArg(v_a_1161_, v_a_1165_, v_sz_1166_, v___x_1167_, v_b_1153_);
lean_dec(v_a_1165_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; size_t v___x_1170_; size_t v___x_1171_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref(v___x_1168_);
v___x_1170_ = ((size_t)1ULL);
v___x_1171_ = lean_usize_add(v_i_1152_, v___x_1170_);
v_i_1152_ = v___x_1171_;
v_b_1153_ = v_a_1169_;
goto _start;
}
else
{
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
return v___x_1168_;
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v_b_1153_);
v_a_1173_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1164_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1164_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v_b_1153_);
v_a_1181_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1162_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1162_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__2___boxed(lean_object* v_maxTolerance_1189_, lean_object* v_as_1190_, lean_object* v_sz_1191_, lean_object* v_i_1192_, lean_object* v_b_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
double v_maxTolerance_boxed_1199_; size_t v_sz_boxed_1200_; size_t v_i_boxed_1201_; lean_object* v_res_1202_; 
v_maxTolerance_boxed_1199_ = lean_unbox_float(v_maxTolerance_1189_);
lean_dec_ref(v_maxTolerance_1189_);
v_sz_boxed_1200_ = lean_unbox_usize(v_sz_1191_);
lean_dec(v_sz_1191_);
v_i_boxed_1201_ = lean_unbox_usize(v_i_1192_);
lean_dec(v_i_1192_);
v_res_1202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__2(v_maxTolerance_boxed_1199_, v_as_1190_, v_sz_boxed_1200_, v_i_boxed_1201_, v_b_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec_ref(v_as_1190_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers(lean_object* v_names_1205_, double v_maxTolerance_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v___x_1212_; lean_object* v_map_1213_; lean_object* v___y_1215_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1212_ = lean_st_ref_get(v_a_1210_);
v_map_1213_ = lean_box(1);
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = lean_array_get_size(v_names_1205_);
v___x_1221_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers___closed__0));
v___x_1222_ = lean_nat_dec_lt(v___x_1219_, v___x_1220_);
if (v___x_1222_ == 0)
{
lean_dec(v___x_1212_);
v___y_1215_ = v___x_1221_;
goto v___jp_1214_;
}
else
{
lean_object* v_env_1223_; uint8_t v___x_1224_; 
v_env_1223_ = lean_ctor_get(v___x_1212_, 0);
lean_inc_ref(v_env_1223_);
lean_dec(v___x_1212_);
v___x_1224_ = lean_nat_dec_le(v___x_1220_, v___x_1220_);
if (v___x_1224_ == 0)
{
if (v___x_1222_ == 0)
{
lean_dec_ref(v_env_1223_);
v___y_1215_ = v___x_1221_;
goto v___jp_1214_;
}
else
{
size_t v___x_1225_; size_t v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = ((size_t)0ULL);
v___x_1226_ = lean_usize_of_nat(v___x_1220_);
v___x_1227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__3(v_env_1223_, v_names_1205_, v___x_1225_, v___x_1226_, v___x_1221_);
v___y_1215_ = v___x_1227_;
goto v___jp_1214_;
}
}
else
{
size_t v___x_1228_; size_t v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = ((size_t)0ULL);
v___x_1229_ = lean_usize_of_nat(v___x_1220_);
v___x_1230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__3(v_env_1223_, v_names_1205_, v___x_1228_, v___x_1229_, v___x_1221_);
v___y_1215_ = v___x_1230_;
goto v___jp_1214_;
}
}
v___jp_1214_:
{
size_t v_sz_1216_; size_t v___x_1217_; lean_object* v___x_1218_; 
v_sz_1216_ = lean_array_size(v___y_1215_);
v___x_1217_ = ((size_t)0ULL);
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__2(v_maxTolerance_1206_, v___y_1215_, v_sz_1216_, v___x_1217_, v_map_1213_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
lean_dec_ref(v___y_1215_);
return v___x_1218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers___boxed(lean_object* v_names_1231_, lean_object* v_maxTolerance_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
double v_maxTolerance_boxed_1238_; lean_object* v_res_1239_; 
v_maxTolerance_boxed_1238_ = lean_unbox_float(v_maxTolerance_1232_);
lean_dec_ref(v_maxTolerance_1232_);
v_res_1239_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers(v_names_1231_, v_maxTolerance_boxed_1238_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
lean_dec_ref(v_names_1231_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__1(lean_object* v_a_1240_, lean_object* v_as_1241_, size_t v_sz_1242_, size_t v_i_1243_, lean_object* v_b_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__1___redArg(v_a_1240_, v_as_1241_, v_sz_1242_, v_i_1243_, v_b_1244_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__1___boxed(lean_object* v_a_1251_, lean_object* v_as_1252_, lean_object* v_sz_1253_, lean_object* v_i_1254_, lean_object* v_b_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
size_t v_sz_boxed_1261_; size_t v_i_boxed_1262_; lean_object* v_res_1263_; 
v_sz_boxed_1261_ = lean_unbox_usize(v_sz_1253_);
lean_dec(v_sz_1253_);
v_i_boxed_1262_ = lean_unbox_usize(v_i_1254_);
lean_dec(v_i_1254_);
v_res_1263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__1(v_a_1251_, v_as_1252_, v_sz_boxed_1261_, v_i_boxed_1262_, v_b_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec_ref(v_as_1252_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0(lean_object* v_00_u03b1_1264_, lean_object* v_constName_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0___redArg(v_constName_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1272_, lean_object* v_constName_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0(v_00_u03b1_1272_, v_constName_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1280_, lean_object* v_ref_1281_, lean_object* v_constName_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg(v_ref_1281_, v_constName_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1289_, lean_object* v_ref_1290_, lean_object* v_constName_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1(v_00_u03b1_1289_, v_ref_1290_, v_constName_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v_ref_1290_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b1_1298_, lean_object* v_ref_1299_, lean_object* v_msg_1300_, lean_object* v_declHint_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_1299_, v_msg_1300_, v_declHint_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b1_1308_, lean_object* v_ref_1309_, lean_object* v_msg_1310_, lean_object* v_declHint_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5(v_00_u03b1_1308_, v_ref_1309_, v_msg_1310_, v_declHint_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v_ref_1309_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7(lean_object* v_msg_1318_, lean_object* v_declHint_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg(v_msg_1318_, v_declHint_1319_, v___y_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_1326_, lean_object* v_declHint_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7(v_msg_1326_, v_declHint_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_1334_, lean_object* v_ref_1335_, lean_object* v_msg_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_1335_, v_msg_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1343_, lean_object* v_ref_1344_, lean_object* v_msg_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7(v_00_u03b1_1343_, v_ref_1344_, v_msg_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v_ref_1344_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_1352_, lean_object* v_msg_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(v_msg_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1360_, lean_object* v_msg_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9(v_00_u03b1_1360_, v_msg_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers_spec__0(lean_object* v_x_1368_, lean_object* v_x_1369_){
_start:
{
if (lean_obj_tag(v_x_1369_) == 0)
{
return v_x_1368_;
}
else
{
lean_object* v_head_1370_; lean_object* v_tail_1371_; lean_object* v___f_1372_; lean_object* v___x_1373_; 
v_head_1370_ = lean_ctor_get(v_x_1369_, 0);
lean_inc(v_head_1370_);
v_tail_1371_ = lean_ctor_get(v_x_1369_, 1);
lean_inc(v_tail_1371_);
lean_dec_ref(v_x_1369_);
v___f_1372_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger___closed__0));
v___x_1373_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___redArg(v___f_1372_, v_head_1370_, v_x_1368_);
v_x_1368_ = v___x_1373_;
v_x_1369_ = v_tail_1371_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers_spec__1(lean_object* v_map_u2081_1375_, lean_object* v_init_1376_, lean_object* v_x_1377_){
_start:
{
if (lean_obj_tag(v_x_1377_) == 0)
{
lean_object* v_k_1378_; lean_object* v_v_1379_; lean_object* v_l_1380_; lean_object* v_r_1381_; lean_object* v___x_1382_; lean_object* v_a_1383_; lean_object* v___x_1384_; 
v_k_1378_ = lean_ctor_get(v_x_1377_, 1);
lean_inc(v_k_1378_);
v_v_1379_ = lean_ctor_get(v_x_1377_, 2);
lean_inc(v_v_1379_);
v_l_1380_ = lean_ctor_get(v_x_1377_, 3);
lean_inc(v_l_1380_);
v_r_1381_ = lean_ctor_get(v_x_1377_, 4);
lean_inc(v_r_1381_);
lean_dec_ref(v_x_1377_);
v___x_1382_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers_spec__1(v_map_u2081_1375_, v_init_1376_, v_l_1380_);
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref(v___x_1382_);
v___x_1384_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_u2081_1375_, v_k_1378_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1378_, v_v_1379_, v_a_1383_);
v_init_1376_ = v___x_1385_;
v_x_1377_ = v_r_1381_;
goto _start;
}
else
{
lean_object* v_val_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v_val_1387_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_val_1387_);
lean_dec_ref(v___x_1384_);
v___x_1388_ = l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers_spec__0(v_val_1387_, v_v_1379_);
v___x_1389_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1378_, v___x_1388_, v_a_1383_);
v_init_1376_ = v___x_1389_;
v_x_1377_ = v_r_1381_;
goto _start;
}
}
else
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1391_, 0, v_init_1376_);
return v___x_1391_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers_spec__1___boxed(lean_object* v_map_u2081_1392_, lean_object* v_init_1393_, lean_object* v_x_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers_spec__1(v_map_u2081_1392_, v_init_1393_, v_x_1394_);
lean_dec(v_map_u2081_1392_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers(lean_object* v_map_u2081_1396_, lean_object* v_map_u2082_1397_){
_start:
{
lean_object* v___x_1398_; lean_object* v_a_1399_; 
lean_inc(v_map_u2081_1396_);
v___x_1398_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers_spec__1(v_map_u2081_1396_, v_map_u2081_1396_, v_map_u2082_1397_);
lean_dec(v_map_u2081_1396_);
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref(v___x_1398_);
return v_a_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___lam__0(lean_object* v___x_1400_, double v___x_1401_, lean_object* v___x_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers(v___x_1400_, v___x_1401_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1418_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1418_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1418_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1413_ = lean_mk_empty_array_with_capacity(v___x_1402_);
v___x_1414_ = lean_array_push(v___x_1413_, v_a_1409_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1414_);
v___x_1416_ = v___x_1411_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
v_a_1419_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1408_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1408_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___lam__0___boxed(lean_object* v___x_1427_, lean_object* v___x_1428_, lean_object* v___x_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
double v___x_883__boxed_1435_; lean_object* v_res_1436_; 
v___x_883__boxed_1435_ = lean_unbox_float(v___x_1428_);
lean_dec_ref(v___x_1428_);
v_res_1436_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___lam__0(v___x_1427_, v___x_883__boxed_1435_, v___x_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___x_1429_);
lean_dec_ref(v___x_1427_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__1(size_t v_sz_1437_, size_t v_i_1438_, lean_object* v_bs_1439_){
_start:
{
uint8_t v___x_1440_; 
v___x_1440_ = lean_usize_dec_lt(v_i_1438_, v_sz_1437_);
if (v___x_1440_ == 0)
{
return v_bs_1439_;
}
else
{
lean_object* v_v_1441_; lean_object* v_fst_1442_; lean_object* v___x_1443_; lean_object* v_bs_x27_1444_; size_t v___x_1445_; size_t v___x_1446_; lean_object* v___x_1447_; 
v_v_1441_ = lean_array_uget_borrowed(v_bs_1439_, v_i_1438_);
v_fst_1442_ = lean_ctor_get(v_v_1441_, 0);
lean_inc(v_fst_1442_);
v___x_1443_ = lean_unsigned_to_nat(0u);
v_bs_x27_1444_ = lean_array_uset(v_bs_1439_, v_i_1438_, v___x_1443_);
v___x_1445_ = ((size_t)1ULL);
v___x_1446_ = lean_usize_add(v_i_1438_, v___x_1445_);
v___x_1447_ = lean_array_uset(v_bs_x27_1444_, v_i_1438_, v_fst_1442_);
v_i_1438_ = v___x_1446_;
v_bs_1439_ = v___x_1447_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__1___boxed(lean_object* v_sz_1449_, lean_object* v_i_1450_, lean_object* v_bs_1451_){
_start:
{
size_t v_sz_boxed_1452_; size_t v_i_boxed_1453_; lean_object* v_res_1454_; 
v_sz_boxed_1452_ = lean_unbox_usize(v_sz_1449_);
lean_dec(v_sz_1449_);
v_i_boxed_1453_ = lean_unbox_usize(v_i_1450_);
lean_dec(v_i_1450_);
v_res_1454_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__1(v_sz_boxed_1452_, v_i_boxed_1453_, v_bs_1451_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg___lam__0(lean_object* v_f_1455_, lean_object* v_x1_1456_, lean_object* v_x2_1457_, lean_object* v_x3_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_apply_3(v_f_1455_, v_x1_1456_, v_x2_1457_, v_x3_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_f_1460_, lean_object* v_keys_1461_, lean_object* v_vals_1462_, lean_object* v_i_1463_, lean_object* v_acc_1464_){
_start:
{
lean_object* v___x_1465_; uint8_t v___x_1466_; 
v___x_1465_ = lean_array_get_size(v_keys_1461_);
v___x_1466_ = lean_nat_dec_lt(v_i_1463_, v___x_1465_);
if (v___x_1466_ == 0)
{
lean_dec(v_i_1463_);
lean_dec(v_f_1460_);
return v_acc_1464_;
}
else
{
lean_object* v_k_1467_; lean_object* v_v_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v_k_1467_ = lean_array_fget_borrowed(v_keys_1461_, v_i_1463_);
v_v_1468_ = lean_array_fget_borrowed(v_vals_1462_, v_i_1463_);
lean_inc(v_f_1460_);
lean_inc(v_v_1468_);
lean_inc(v_k_1467_);
v___x_1469_ = lean_apply_3(v_f_1460_, v_acc_1464_, v_k_1467_, v_v_1468_);
v___x_1470_ = lean_unsigned_to_nat(1u);
v___x_1471_ = lean_nat_add(v_i_1463_, v___x_1470_);
lean_dec(v_i_1463_);
v_i_1463_ = v___x_1471_;
v_acc_1464_ = v___x_1469_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_1473_, lean_object* v_keys_1474_, lean_object* v_vals_1475_, lean_object* v_i_1476_, lean_object* v_acc_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_1473_, v_keys_1474_, v_vals_1475_, v_i_1476_, v_acc_1477_);
lean_dec_ref(v_vals_1475_);
lean_dec_ref(v_keys_1474_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_1479_, lean_object* v_x_1480_, lean_object* v_x_1481_){
_start:
{
if (lean_obj_tag(v_x_1480_) == 0)
{
lean_object* v_es_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v_es_1482_ = lean_ctor_get(v_x_1480_, 0);
v___x_1483_ = lean_unsigned_to_nat(0u);
v___x_1484_ = lean_array_get_size(v_es_1482_);
v___x_1485_ = lean_nat_dec_lt(v___x_1483_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_dec(v_f_1479_);
return v_x_1481_;
}
else
{
uint8_t v___x_1486_; 
v___x_1486_ = lean_nat_dec_le(v___x_1484_, v___x_1484_);
if (v___x_1486_ == 0)
{
if (v___x_1485_ == 0)
{
lean_dec(v_f_1479_);
return v_x_1481_;
}
else
{
size_t v___x_1487_; size_t v___x_1488_; lean_object* v___x_1489_; 
v___x_1487_ = ((size_t)0ULL);
v___x_1488_ = lean_usize_of_nat(v___x_1484_);
v___x_1489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_f_1479_, v_es_1482_, v___x_1487_, v___x_1488_, v_x_1481_);
return v___x_1489_;
}
}
else
{
size_t v___x_1490_; size_t v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = ((size_t)0ULL);
v___x_1491_ = lean_usize_of_nat(v___x_1484_);
v___x_1492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_f_1479_, v_es_1482_, v___x_1490_, v___x_1491_, v_x_1481_);
return v___x_1492_;
}
}
}
else
{
lean_object* v_ks_1493_; lean_object* v_vs_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_ks_1493_ = lean_ctor_get(v_x_1480_, 0);
v_vs_1494_ = lean_ctor_get(v_x_1480_, 1);
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_1479_, v_ks_1493_, v_vs_1494_, v___x_1495_, v_x_1481_);
return v___x_1496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_f_1497_, lean_object* v_as_1498_, size_t v_i_1499_, size_t v_stop_1500_, lean_object* v_b_1501_){
_start:
{
lean_object* v___y_1503_; uint8_t v___x_1507_; 
v___x_1507_ = lean_usize_dec_eq(v_i_1499_, v_stop_1500_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_array_uget_borrowed(v_as_1498_, v_i_1499_);
switch(lean_obj_tag(v___x_1508_))
{
case 0:
{
lean_object* v_key_1509_; lean_object* v_val_1510_; lean_object* v___x_1511_; 
v_key_1509_ = lean_ctor_get(v___x_1508_, 0);
v_val_1510_ = lean_ctor_get(v___x_1508_, 1);
lean_inc(v_f_1497_);
lean_inc(v_val_1510_);
lean_inc(v_key_1509_);
v___x_1511_ = lean_apply_3(v_f_1497_, v_b_1501_, v_key_1509_, v_val_1510_);
v___y_1503_ = v___x_1511_;
goto v___jp_1502_;
}
case 1:
{
lean_object* v_node_1512_; lean_object* v___x_1513_; 
v_node_1512_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_f_1497_);
v___x_1513_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1497_, v_node_1512_, v_b_1501_);
v___y_1503_ = v___x_1513_;
goto v___jp_1502_;
}
default: 
{
v___y_1503_ = v_b_1501_;
goto v___jp_1502_;
}
}
}
else
{
lean_dec(v_f_1497_);
return v_b_1501_;
}
v___jp_1502_:
{
size_t v___x_1504_; size_t v___x_1505_; 
v___x_1504_ = ((size_t)1ULL);
v___x_1505_ = lean_usize_add(v_i_1499_, v___x_1504_);
v_i_1499_ = v___x_1505_;
v_b_1501_ = v___y_1503_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_f_1514_, lean_object* v_as_1515_, lean_object* v_i_1516_, lean_object* v_stop_1517_, lean_object* v_b_1518_){
_start:
{
size_t v_i_boxed_1519_; size_t v_stop_boxed_1520_; lean_object* v_res_1521_; 
v_i_boxed_1519_ = lean_unbox_usize(v_i_1516_);
lean_dec(v_i_1516_);
v_stop_boxed_1520_ = lean_unbox_usize(v_stop_1517_);
lean_dec(v_stop_1517_);
v_res_1521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_f_1514_, v_as_1515_, v_i_boxed_1519_, v_stop_boxed_1520_, v_b_1518_);
lean_dec_ref(v_as_1515_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_1522_, lean_object* v_x_1523_, lean_object* v_x_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1522_, v_x_1523_, v_x_1524_);
lean_dec_ref(v_x_1523_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg(lean_object* v_map_1526_, lean_object* v_f_1527_, lean_object* v_init_1528_){
_start:
{
lean_object* v___f_1529_; lean_object* v___x_1530_; 
v___f_1529_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1529_, 0, v_f_1527_);
v___x_1530_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(v___f_1529_, v_map_1526_, v_init_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg___boxed(lean_object* v_map_1531_, lean_object* v_f_1532_, lean_object* v_init_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg(v_map_1531_, v_f_1532_, v_init_1533_);
lean_dec_ref(v_map_1531_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg___lam__0(lean_object* v_ps_1535_, lean_object* v_k_1536_, lean_object* v_v_1537_){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v_k_1536_);
lean_ctor_set(v___x_1538_, 1, v_v_1537_);
v___x_1539_ = lean_array_push(v_ps_1535_, v___x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg(lean_object* v_m_1543_){
_start:
{
lean_object* v___f_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___f_1544_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg___closed__0));
v___x_1545_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg___closed__1));
v___x_1546_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg(v_m_1543_, v___f_1544_, v___x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg___boxed(lean_object* v_m_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg(v_m_1547_);
lean_dec_ref(v_m_1547_);
return v_res_1548_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__0(void){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Array_instInhabited(lean_box(0));
return v___x_1549_;
}
}
static double _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__1(void){
_start:
{
lean_object* v___x_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; double v___x_1553_; 
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = 1;
v___x_1552_ = lean_unsigned_to_nat(30u);
v___x_1553_ = l_Float_ofScientific(v___x_1552_, v___x_1551_, v___x_1550_);
return v___x_1553_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___boxed__const__1(void){
_start:
{
double v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = lean_float_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__1, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__1_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__1);
v___x_1555_ = lean_box_float(v___x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3(lean_object* v_env_1556_){
_start:
{
lean_object* v___x_1557_; lean_object* v_map_u2082_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; size_t v_sz_1561_; size_t v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___f_1566_; lean_object* v___x_1567_; 
lean_inc_ref(v_env_1556_);
v___x_1557_ = l_Lean_Environment_constants(v_env_1556_);
v_map_u2082_1558_ = lean_ctor_get(v___x_1557_, 1);
lean_inc_ref(v_map_u2082_1558_);
lean_dec_ref(v___x_1557_);
v___x_1559_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__0, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__0_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__0);
v___x_1560_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg(v_map_u2082_1558_);
lean_dec_ref(v_map_u2082_1558_);
v_sz_1561_ = lean_array_size(v___x_1560_);
v___x_1562_ = ((size_t)0ULL);
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__1(v_sz_1561_, v___x_1562_, v___x_1560_);
v___x_1564_ = lean_unsigned_to_nat(1u);
v___x_1565_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___boxed__const__1;
v___f_1566_ = lean_alloc_closure((void*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1566_, 0, v___x_1563_);
lean_closure_set(v___f_1566_, 1, v___x_1565_);
lean_closure_set(v___f_1566_, 2, v___x_1564_);
v___x_1567_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v___x_1559_, v_env_1556_, v___f_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0(lean_object* v_00_u03b2_1568_, lean_object* v_m_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg(v_m_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___boxed(lean_object* v_00_u03b2_1571_, lean_object* v_m_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0(v_00_u03b2_1571_, v_m_1572_);
lean_dec_ref(v_m_1572_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0(lean_object* v_00_u03c3_1574_, lean_object* v_00_u03b2_1575_, lean_object* v_map_1576_, lean_object* v_f_1577_, lean_object* v_init_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg(v_map_1576_, v_f_1577_, v_init_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___boxed(lean_object* v_00_u03c3_1580_, lean_object* v_00_u03b2_1581_, lean_object* v_map_1582_, lean_object* v_f_1583_, lean_object* v_init_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0(v_00_u03c3_1580_, v_00_u03b2_1581_, v_map_1582_, v_f_1583_, v_init_1584_);
lean_dec_ref(v_map_1582_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1___redArg(lean_object* v_map_1586_, lean_object* v_f_1587_, lean_object* v_init_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1587_, v_map_1586_, v_init_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_1590_, lean_object* v_f_1591_, lean_object* v_init_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1___redArg(v_map_1590_, v_f_1591_, v_init_1592_);
lean_dec_ref(v_map_1590_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_1594_, lean_object* v_00_u03b2_1595_, lean_object* v_map_1596_, lean_object* v_f_1597_, lean_object* v_init_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1597_, v_map_1596_, v_init_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1600_, lean_object* v_00_u03b2_1601_, lean_object* v_map_1602_, lean_object* v_f_1603_, lean_object* v_init_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1(v_00_u03c3_1600_, v_00_u03b2_1601_, v_map_1602_, v_f_1603_, v_init_1604_);
lean_dec_ref(v_map_1602_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_1606_, lean_object* v_00_u03b1_1607_, lean_object* v_00_u03b2_1608_, lean_object* v_f_1609_, lean_object* v_x_1610_, lean_object* v_x_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1609_, v_x_1610_, v_x_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_1613_, lean_object* v_00_u03b1_1614_, lean_object* v_00_u03b2_1615_, lean_object* v_f_1616_, lean_object* v_x_1617_, lean_object* v_x_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_1613_, v_00_u03b1_1614_, v_00_u03b2_1615_, v_f_1616_, v_x_1617_, v_x_1618_);
lean_dec_ref(v_x_1617_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b1_1620_, lean_object* v_00_u03b2_1621_, lean_object* v_00_u03c3_1622_, lean_object* v_f_1623_, lean_object* v_as_1624_, size_t v_i_1625_, size_t v_stop_1626_, lean_object* v_b_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_f_1623_, v_as_1624_, v_i_1625_, v_stop_1626_, v_b_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1629_, lean_object* v_00_u03b2_1630_, lean_object* v_00_u03c3_1631_, lean_object* v_f_1632_, lean_object* v_as_1633_, lean_object* v_i_1634_, lean_object* v_stop_1635_, lean_object* v_b_1636_){
_start:
{
size_t v_i_boxed_1637_; size_t v_stop_boxed_1638_; lean_object* v_res_1639_; 
v_i_boxed_1637_ = lean_unbox_usize(v_i_1634_);
lean_dec(v_i_1634_);
v_stop_boxed_1638_ = lean_unbox_usize(v_stop_1635_);
lean_dec(v_stop_1635_);
v_res_1639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4(v_00_u03b1_1629_, v_00_u03b2_1630_, v_00_u03c3_1631_, v_f_1632_, v_as_1633_, v_i_boxed_1637_, v_stop_boxed_1638_, v_b_1636_);
lean_dec_ref(v_as_1633_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03c3_1640_, lean_object* v_00_u03b1_1641_, lean_object* v_00_u03b2_1642_, lean_object* v_f_1643_, lean_object* v_keys_1644_, lean_object* v_vals_1645_, lean_object* v_heq_1646_, lean_object* v_i_1647_, lean_object* v_acc_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_1643_, v_keys_1644_, v_vals_1645_, v_i_1647_, v_acc_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03c3_1650_, lean_object* v_00_u03b1_1651_, lean_object* v_00_u03b2_1652_, lean_object* v_f_1653_, lean_object* v_keys_1654_, lean_object* v_vals_1655_, lean_object* v_heq_1656_, lean_object* v_i_1657_, lean_object* v_acc_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03c3_1650_, v_00_u03b1_1651_, v_00_u03b2_1652_, v_f_1653_, v_keys_1654_, v_vals_1655_, v_heq_1656_, v_i_1657_, v_acc_1658_);
lean_dec_ref(v_vals_1655_);
lean_dec_ref(v_keys_1654_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object* v_mapss_1660_, lean_object* v_x_1661_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v_mapss_1660_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object* v_mapss_1664_, lean_object* v_x_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(v_mapss_1664_, v_x_1665_);
lean_dec_ref(v_x_1665_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object* v_a_1668_, uint8_t v_a_1669_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
uint8_t v_a_166__boxed_1672_; lean_object* v_res_1673_; 
v_a_166__boxed_1672_ = lean_unbox(v_a_1671_);
v_res_1673_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(v_a_1670_, v_a_166__boxed_1672_);
lean_dec_ref(v_a_1670_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object* v_env_1674_, lean_object* v_x_1675_, uint8_t v_x_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3(v_env_1674_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object* v_env_1678_, lean_object* v_x_1679_, lean_object* v_x_1680_){
_start:
{
uint8_t v_x_172__boxed_1681_; lean_object* v_res_1682_; 
v_x_172__boxed_1681_ = lean_unbox(v_x_1680_);
v_res_1682_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(v_env_1678_, v_x_1679_, v_x_172__boxed_1681_);
lean_dec_ref(v_x_1679_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object* v_x_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = ((lean_object*)(l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_));
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object* v_x_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(v_x_1688_);
lean_dec_ref(v_x_1688_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object* v_x_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = ((lean_object*)(l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_));
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object* v_x_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(v_x_1694_);
lean_dec_ref(v_x_1694_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object* v___x_1696_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object* v___x_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(v___x_1699_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = ((lean_object*)(l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_));
v___x_1728_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_();
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_228879371____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = lean_box(0);
v___x_1733_ = lean_st_mk_ref(v___x_1732_);
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_228879371____hygCtx___hyg_2____boxed(lean_object* v_a_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_228879371____hygCtx___hyg_2_();
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__0(lean_object* v_as_1737_, size_t v_i_1738_, size_t v_stop_1739_, lean_object* v_b_1740_){
_start:
{
uint8_t v___x_1741_; 
v___x_1741_ = lean_usize_dec_eq(v_i_1738_, v_stop_1739_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1743_; size_t v___x_1744_; size_t v___x_1745_; 
v___x_1742_ = lean_array_uget_borrowed(v_as_1737_, v_i_1738_);
lean_inc(v___x_1742_);
v___x_1743_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers(v_b_1740_, v___x_1742_);
v___x_1744_ = ((size_t)1ULL);
v___x_1745_ = lean_usize_add(v_i_1738_, v___x_1744_);
v_i_1738_ = v___x_1745_;
v_b_1740_ = v___x_1743_;
goto _start;
}
else
{
return v_b_1740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__0___boxed(lean_object* v_as_1747_, lean_object* v_i_1748_, lean_object* v_stop_1749_, lean_object* v_b_1750_){
_start:
{
size_t v_i_boxed_1751_; size_t v_stop_boxed_1752_; lean_object* v_res_1753_; 
v_i_boxed_1751_ = lean_unbox_usize(v_i_1748_);
lean_dec(v_i_1748_);
v_stop_boxed_1752_ = lean_unbox_usize(v_stop_1749_);
lean_dec(v_stop_1749_);
v_res_1753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__0(v_as_1747_, v_i_boxed_1751_, v_stop_boxed_1752_, v_b_1750_);
lean_dec_ref(v_as_1747_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__1(lean_object* v_as_1754_, size_t v_i_1755_, size_t v_stop_1756_, lean_object* v_b_1757_){
_start:
{
lean_object* v___y_1759_; uint8_t v___x_1763_; 
v___x_1763_ = lean_usize_dec_eq(v_i_1755_, v_stop_1756_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1764_ = lean_array_uget_borrowed(v_as_1754_, v_i_1755_);
v___x_1765_ = lean_unsigned_to_nat(0u);
v___x_1766_ = lean_array_get_size(v___x_1764_);
v___x_1767_ = lean_nat_dec_lt(v___x_1765_, v___x_1766_);
if (v___x_1767_ == 0)
{
v___y_1759_ = v_b_1757_;
goto v___jp_1758_;
}
else
{
uint8_t v___x_1768_; 
v___x_1768_ = lean_nat_dec_le(v___x_1766_, v___x_1766_);
if (v___x_1768_ == 0)
{
if (v___x_1767_ == 0)
{
v___y_1759_ = v_b_1757_;
goto v___jp_1758_;
}
else
{
size_t v___x_1769_; size_t v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = ((size_t)0ULL);
v___x_1770_ = lean_usize_of_nat(v___x_1766_);
v___x_1771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__0(v___x_1764_, v___x_1769_, v___x_1770_, v_b_1757_);
v___y_1759_ = v___x_1771_;
goto v___jp_1758_;
}
}
else
{
size_t v___x_1772_; size_t v___x_1773_; lean_object* v___x_1774_; 
v___x_1772_ = ((size_t)0ULL);
v___x_1773_ = lean_usize_of_nat(v___x_1766_);
v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__0(v___x_1764_, v___x_1772_, v___x_1773_, v_b_1757_);
v___y_1759_ = v___x_1774_;
goto v___jp_1758_;
}
}
}
else
{
return v_b_1757_;
}
v___jp_1758_:
{
size_t v___x_1760_; size_t v___x_1761_; 
v___x_1760_ = ((size_t)1ULL);
v___x_1761_ = lean_usize_add(v_i_1755_, v___x_1760_);
v_i_1755_ = v___x_1761_;
v_b_1757_ = v___y_1759_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__1___boxed(lean_object* v_as_1775_, lean_object* v_i_1776_, lean_object* v_stop_1777_, lean_object* v_b_1778_){
_start:
{
size_t v_i_boxed_1779_; size_t v_stop_boxed_1780_; lean_object* v_res_1781_; 
v_i_boxed_1779_ = lean_unbox_usize(v_i_1776_);
lean_dec(v_i_1776_);
v_stop_boxed_1780_ = lean_unbox_usize(v_stop_1777_);
lean_dec(v_stop_1777_);
v_res_1781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__1(v_as_1775_, v_i_boxed_1779_, v_stop_boxed_1780_, v_b_1778_);
lean_dec_ref(v_as_1775_);
return v_res_1781_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___closed__0(void){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Array_instInhabited(lean_box(0));
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg(lean_object* v_a_1783_){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersRef;
v___x_1786_ = lean_st_ref_get(v___x_1785_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v___x_1787_; lean_object* v___y_1789_; lean_object* v_env_1793_; lean_object* v___x_1794_; lean_object* v_toEnvExtension_1795_; lean_object* v_asyncMode_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1787_ = lean_st_ref_get(v_a_1783_);
v_env_1793_ = lean_ctor_get(v___x_1787_, 0);
lean_inc_ref(v_env_1793_);
lean_dec(v___x_1787_);
v___x_1794_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt;
v_toEnvExtension_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc_ref(v_toEnvExtension_1795_);
v_asyncMode_1796_ = lean_ctor_get(v_toEnvExtension_1795_, 2);
lean_inc(v_asyncMode_1796_);
lean_dec_ref(v_toEnvExtension_1795_);
v___x_1797_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___closed__0, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___closed__0_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___closed__0);
v___x_1798_ = lean_box(0);
v___x_1799_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1797_, v___x_1794_, v_env_1793_, v_asyncMode_1796_, v___x_1798_);
lean_dec(v_asyncMode_1796_);
v___x_1800_ = lean_box(1);
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = lean_array_get_size(v___x_1799_);
v___x_1803_ = lean_nat_dec_lt(v___x_1801_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_dec(v___x_1799_);
v___y_1789_ = v___x_1800_;
goto v___jp_1788_;
}
else
{
uint8_t v___x_1804_; 
v___x_1804_ = lean_nat_dec_le(v___x_1802_, v___x_1802_);
if (v___x_1804_ == 0)
{
if (v___x_1803_ == 0)
{
lean_dec(v___x_1799_);
v___y_1789_ = v___x_1800_;
goto v___jp_1788_;
}
else
{
size_t v___x_1805_; size_t v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = ((size_t)0ULL);
v___x_1806_ = lean_usize_of_nat(v___x_1802_);
v___x_1807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__1(v___x_1799_, v___x_1805_, v___x_1806_, v___x_1800_);
lean_dec(v___x_1799_);
v___y_1789_ = v___x_1807_;
goto v___jp_1788_;
}
}
else
{
size_t v___x_1808_; size_t v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = ((size_t)0ULL);
v___x_1809_ = lean_usize_of_nat(v___x_1802_);
v___x_1810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__1(v___x_1799_, v___x_1808_, v___x_1809_, v___x_1800_);
lean_dec(v___x_1799_);
v___y_1789_ = v___x_1810_;
goto v___jp_1788_;
}
}
v___jp_1788_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_inc(v___y_1789_);
v___x_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___y_1789_);
v___x_1791_ = lean_st_ref_set(v___x_1785_, v___x_1790_);
v___x_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1792_, 0, v___y_1789_);
return v___x_1792_;
}
}
else
{
lean_object* v_val_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
v_val_1811_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1786_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_val_1811_);
lean_dec(v___x_1786_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
lean_ctor_set_tag(v___x_1813_, 0);
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_val_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___boxed(lean_object* v_a_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg(v_a_1819_);
lean_dec(v_a_1819_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap(lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg(v_a_1823_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___boxed(lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap(v_a_1826_, v_a_1827_);
lean_dec(v_a_1827_);
lean_dec_ref(v_a_1826_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___redArg(lean_object* v_trigger_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v___x_1833_; lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1843_; 
v___x_1833_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg(v_a_1831_);
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1843_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1843_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1838_ = lean_box(0);
v___x_1839_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_a_1834_, v_trigger_1830_, v___x_1838_);
lean_dec(v_a_1834_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1839_);
v___x_1841_ = v___x_1836_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___redArg___boxed(lean_object* v_trigger_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___redArg(v_trigger_1844_, v_a_1845_);
lean_dec(v_a_1845_);
lean_dec(v_trigger_1844_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems(lean_object* v_trigger_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___redArg(v_trigger_1848_, v_a_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___boxed(lean_object* v_trigger_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems(v_trigger_1853_, v_a_1854_, v_a_1855_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec(v_trigger_1853_);
return v_res_1857_;
}
}
LEAN_EXPORT uint8_t l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1___lam__0(lean_object* v_decl_1858_, lean_object* v_x_1859_){
_start:
{
lean_object* v_fst_1860_; uint8_t v___x_1861_; 
v_fst_1860_ = lean_ctor_get(v_x_1859_, 0);
v___x_1861_ = lean_name_eq(v_fst_1860_, v_decl_1858_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1___lam__0___boxed(lean_object* v_decl_1862_, lean_object* v_x_1863_){
_start:
{
uint8_t v_res_1864_; lean_object* v_r_1865_; 
v_res_1864_ = l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1___lam__0(v_decl_1862_, v_x_1863_);
lean_dec_ref(v_x_1863_);
lean_dec(v_decl_1862_);
v_r_1865_ = lean_box(v_res_1864_);
return v_r_1865_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1(lean_object* v_decl_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
if (lean_obj_tag(v_a_1867_) == 0)
{
lean_object* v___x_1869_; 
lean_dec(v_decl_1866_);
v___x_1869_ = lean_array_to_list(v_a_1868_);
return v___x_1869_;
}
else
{
lean_object* v_head_1870_; lean_object* v_tail_1871_; lean_object* v_val_1873_; lean_object* v_fst_1876_; lean_object* v_snd_1877_; lean_object* v___f_1878_; lean_object* v___x_1879_; 
v_head_1870_ = lean_ctor_get(v_a_1867_, 0);
lean_inc(v_head_1870_);
v_tail_1871_ = lean_ctor_get(v_a_1867_, 1);
lean_inc(v_tail_1871_);
lean_dec_ref(v_a_1867_);
v_fst_1876_ = lean_ctor_get(v_head_1870_, 0);
lean_inc(v_fst_1876_);
v_snd_1877_ = lean_ctor_get(v_head_1870_, 1);
lean_inc(v_snd_1877_);
lean_dec(v_head_1870_);
lean_inc(v_decl_1866_);
v___f_1878_ = lean_alloc_closure((void*)(l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1878_, 0, v_decl_1866_);
v___x_1879_ = l_List_find_x3f___redArg(v___f_1878_, v_snd_1877_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_dec(v_fst_1876_);
if (lean_obj_tag(v___x_1879_) == 0)
{
v_a_1867_ = v_tail_1871_;
goto _start;
}
else
{
lean_object* v_val_1881_; 
v_val_1881_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_val_1881_);
lean_dec_ref(v___x_1879_);
v_val_1873_ = v_val_1881_;
goto v___jp_1872_;
}
}
else
{
lean_object* v_val_1882_; lean_object* v_snd_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
v_val_1882_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_val_1882_);
lean_dec_ref(v___x_1879_);
v_snd_1883_ = lean_ctor_get(v_val_1882_, 1);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_val_1882_);
if (v_isSharedCheck_1890_ == 0)
{
lean_object* v_unused_1891_; 
v_unused_1891_ = lean_ctor_get(v_val_1882_, 0);
lean_dec(v_unused_1891_);
v___x_1885_ = v_val_1882_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_snd_1883_);
lean_dec(v_val_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v_fst_1876_);
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_fst_1876_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_snd_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
v_val_1873_ = v___x_1888_;
goto v___jp_1872_;
}
}
}
v___jp_1872_:
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_array_push(v_a_1868_, v_val_1873_);
v_a_1867_ = v_tail_1871_;
v_a_1868_ = v___x_1874_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__0(lean_object* v_init_1892_, lean_object* v_x_1893_){
_start:
{
if (lean_obj_tag(v_x_1893_) == 0)
{
lean_object* v_k_1894_; lean_object* v_v_1895_; lean_object* v_l_1896_; lean_object* v_r_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v_k_1894_ = lean_ctor_get(v_x_1893_, 1);
v_v_1895_ = lean_ctor_get(v_x_1893_, 2);
v_l_1896_ = lean_ctor_get(v_x_1893_, 3);
v_r_1897_ = lean_ctor_get(v_x_1893_, 4);
v___x_1898_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__0(v_init_1892_, v_r_1897_);
lean_inc(v_v_1895_);
lean_inc(v_k_1894_);
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v_k_1894_);
lean_ctor_set(v___x_1899_, 1, v_v_1895_);
v___x_1900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
lean_ctor_set(v___x_1900_, 1, v___x_1898_);
v_init_1892_ = v___x_1900_;
v_x_1893_ = v_l_1896_;
goto _start;
}
else
{
return v_init_1892_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__0___boxed(lean_object* v_init_1902_, lean_object* v_x_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__0(v_init_1902_, v_x_1903_);
lean_dec(v_x_1903_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___redArg(lean_object* v_decl_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v___x_1908_; lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1920_; 
v___x_1908_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg(v_a_1906_);
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1920_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1920_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1918_; 
v___x_1913_ = lean_box(0);
v___x_1914_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__0(v___x_1913_, v_a_1909_);
lean_dec(v_a_1909_);
v___x_1915_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1___closed__0));
v___x_1916_ = l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1(v_decl_1905_, v___x_1914_, v___x_1915_);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1916_);
v___x_1918_ = v___x_1911_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___redArg___boxed(lean_object* v_decl_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___redArg(v_decl_1921_, v_a_1922_);
lean_dec(v_a_1922_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor(lean_object* v_decl_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___redArg(v_decl_1925_, v_a_1927_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___boxed(lean_object* v_decl_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor(v_decl_1930_, v_a_1931_, v_a_1932_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
return v_res_1934_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___lam__0(lean_object* v_x_1935_, lean_object* v_y_1936_){
_start:
{
lean_object* v_fst_1937_; lean_object* v_snd_1938_; lean_object* v_fst_1939_; lean_object* v_snd_1940_; double v___x_1941_; double v___x_1942_; uint8_t v___x_1943_; 
v_fst_1937_ = lean_ctor_get(v_x_1935_, 0);
v_snd_1938_ = lean_ctor_get(v_x_1935_, 1);
v_fst_1939_ = lean_ctor_get(v_y_1936_, 0);
v_snd_1940_ = lean_ctor_get(v_y_1936_, 1);
v___x_1941_ = lean_unbox_float(v_fst_1937_);
v___x_1942_ = lean_unbox_float(v_fst_1939_);
v___x_1943_ = lean_float_decLt(v___x_1941_, v___x_1942_);
if (v___x_1943_ == 0)
{
double v___x_1944_; double v___x_1945_; uint8_t v___x_1946_; 
v___x_1944_ = lean_unbox_float(v_fst_1939_);
v___x_1945_ = lean_unbox_float(v_fst_1937_);
v___x_1946_ = lean_float_decLt(v___x_1944_, v___x_1945_);
if (v___x_1946_ == 0)
{
uint8_t v___x_1947_; 
v___x_1947_ = l_Lean_Name_cmp(v_snd_1938_, v_snd_1940_);
return v___x_1947_;
}
else
{
uint8_t v___x_1948_; 
v___x_1948_ = 2;
return v___x_1948_;
}
}
else
{
uint8_t v___x_1949_; 
v___x_1949_ = 0;
return v___x_1949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___lam__0___boxed(lean_object* v_x_1950_, lean_object* v_y_1951_){
_start:
{
uint8_t v_res_1952_; lean_object* v_r_1953_; 
v_res_1952_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___lam__0(v_x_1950_, v_y_1951_);
lean_dec_ref(v_y_1951_);
lean_dec_ref(v_x_1950_);
v_r_1953_ = lean_box(v_res_1952_);
return v_r_1953_;
}
}
static double _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___closed__0(void){
_start:
{
lean_object* v___x_1956_; uint8_t v___x_1957_; lean_object* v___x_1958_; double v___x_1959_; 
v___x_1956_ = lean_unsigned_to_nat(1u);
v___x_1957_ = 1;
v___x_1958_ = lean_unsigned_to_nat(10u);
v___x_1959_ = l_Float_ofScientific(v___x_1958_, v___x_1957_, v___x_1956_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg(lean_object* v_n_1960_, double v_frequencyWeight_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_LibrarySuggestions_symbolFrequency___redArg(v_n_1960_, v_a_1962_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1980_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_1980_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1980_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; double v___x_1970_; lean_object* v___x_1971_; double v___x_1972_; double v___x_1973_; double v___x_1974_; double v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1969_ = lean_unsigned_to_nat(1u);
v___x_1970_ = lean_float_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___closed__0, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___closed__0_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___closed__0);
v___x_1971_ = lean_nat_add(v_a_1965_, v___x_1969_);
lean_dec(v_a_1965_);
v___x_1972_ = lean_float_of_nat(v___x_1971_);
v___x_1973_ = log2(v___x_1972_);
v___x_1974_ = lean_float_mul(v_frequencyWeight_1961_, v___x_1973_);
v___x_1975_ = lean_float_add(v___x_1970_, v___x_1974_);
v___x_1976_ = lean_box_float(v___x_1975_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v___x_1976_);
v___x_1978_ = v___x_1967_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
v_a_1981_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1964_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1964_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___boxed(lean_object* v_n_1989_, lean_object* v_frequencyWeight_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
double v_frequencyWeight_boxed_1993_; lean_object* v_res_1994_; 
v_frequencyWeight_boxed_1993_ = lean_unbox_float(v_frequencyWeight_1990_);
lean_dec_ref(v_frequencyWeight_1990_);
v_res_1994_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg(v_n_1989_, v_frequencyWeight_boxed_1993_, v_a_1991_);
lean_dec(v_a_1991_);
lean_dec(v_n_1989_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore(lean_object* v_n_1995_, double v_frequencyWeight_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg(v_n_1995_, v_frequencyWeight_1996_, v_a_2000_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___boxed(lean_object* v_n_2003_, lean_object* v_frequencyWeight_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
double v_frequencyWeight_boxed_2010_; lean_object* v_res_2011_; 
v_frequencyWeight_boxed_2010_ = lean_unbox_float(v_frequencyWeight_2004_);
lean_dec_ref(v_frequencyWeight_2004_);
v_res_2011_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore(v_n_2003_, v_frequencyWeight_boxed_2010_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
lean_dec(v_n_2003_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg(lean_object* v_cls_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_options_2018_; uint8_t v_hasTrace_2019_; 
v_options_2018_ = lean_ctor_get(v___y_2016_, 2);
v_hasTrace_2019_ = lean_ctor_get_uint8(v_options_2018_, sizeof(void*)*1);
if (v_hasTrace_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
lean_dec(v_cls_2015_);
v___x_2020_ = lean_box(v_hasTrace_2019_);
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
return v___x_2021_;
}
else
{
lean_object* v_inheritedTraceOptions_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_inheritedTraceOptions_2022_ = lean_ctor_get(v___y_2016_, 13);
v___x_2023_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg___closed__1));
v___x_2024_ = l_Lean_Name_append(v___x_2023_, v_cls_2015_);
v___x_2025_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2022_, v_options_2018_, v___x_2024_);
lean_dec(v___x_2024_);
v___x_2026_ = lean_box(v___x_2025_);
v___x_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
return v___x_2027_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg___boxed(lean_object* v_cls_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg(v_cls_2028_, v___y_2029_);
lean_dec_ref(v___y_2029_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5(lean_object* v_cls_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg(v_cls_2032_, v___y_2035_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___boxed(lean_object* v_cls_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5(v_cls_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(lean_object* v_k_2046_, lean_object* v_t_2047_){
_start:
{
lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; 
if (lean_obj_tag(v_t_2047_) == 0)
{
lean_object* v_k_2062_; lean_object* v_v_2063_; lean_object* v_l_2064_; lean_object* v_r_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2708_; 
v_k_2062_ = lean_ctor_get(v_t_2047_, 1);
v_v_2063_ = lean_ctor_get(v_t_2047_, 2);
v_l_2064_ = lean_ctor_get(v_t_2047_, 3);
v_r_2065_ = lean_ctor_get(v_t_2047_, 4);
v_isSharedCheck_2708_ = !lean_is_exclusive(v_t_2047_);
if (v_isSharedCheck_2708_ == 0)
{
lean_object* v_unused_2709_; 
v_unused_2709_ = lean_ctor_get(v_t_2047_, 0);
lean_dec(v_unused_2709_);
v___x_2067_ = v_t_2047_;
v_isShared_2068_ = v_isSharedCheck_2708_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_r_2065_);
lean_inc(v_l_2064_);
lean_inc(v_v_2063_);
lean_inc(v_k_2062_);
lean_dec(v_t_2047_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2708_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v_fst_2386_; lean_object* v_snd_2387_; lean_object* v_fst_2388_; lean_object* v_snd_2389_; double v___x_2390_; double v___x_2391_; uint8_t v___x_2392_; 
v_fst_2386_ = lean_ctor_get(v_k_2046_, 0);
v_snd_2387_ = lean_ctor_get(v_k_2046_, 1);
v_fst_2388_ = lean_ctor_get(v_k_2062_, 0);
v_snd_2389_ = lean_ctor_get(v_k_2062_, 1);
v___x_2390_ = lean_unbox_float(v_fst_2386_);
v___x_2391_ = lean_unbox_float(v_fst_2388_);
v___x_2392_ = lean_float_decLt(v___x_2390_, v___x_2391_);
if (v___x_2392_ == 0)
{
double v___x_2393_; double v___x_2394_; uint8_t v___x_2395_; 
v___x_2393_ = lean_unbox_float(v_fst_2388_);
v___x_2394_ = lean_unbox_float(v_fst_2386_);
v___x_2395_ = lean_float_decLt(v___x_2393_, v___x_2394_);
if (v___x_2395_ == 0)
{
uint8_t v___x_2396_; 
v___x_2396_ = l_Lean_Name_cmp(v_snd_2387_, v_snd_2389_);
switch(v___x_2396_)
{
case 0:
{
lean_del_object(v___x_2067_);
goto v___jp_2254_;
}
case 1:
{
lean_del_object(v___x_2067_);
lean_dec(v_v_2063_);
lean_dec(v_k_2062_);
if (lean_obj_tag(v_l_2064_) == 0)
{
if (lean_obj_tag(v_r_2065_) == 0)
{
lean_object* v_size_2397_; lean_object* v_k_2398_; lean_object* v_v_2399_; lean_object* v_l_2400_; lean_object* v_r_2401_; lean_object* v_size_2402_; lean_object* v_k_2403_; lean_object* v_v_2404_; lean_object* v_l_2405_; lean_object* v_r_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; 
v_size_2397_ = lean_ctor_get(v_l_2064_, 0);
v_k_2398_ = lean_ctor_get(v_l_2064_, 1);
v_v_2399_ = lean_ctor_get(v_l_2064_, 2);
v_l_2400_ = lean_ctor_get(v_l_2064_, 3);
v_r_2401_ = lean_ctor_get(v_l_2064_, 4);
lean_inc(v_r_2401_);
v_size_2402_ = lean_ctor_get(v_r_2065_, 0);
v_k_2403_ = lean_ctor_get(v_r_2065_, 1);
v_v_2404_ = lean_ctor_get(v_r_2065_, 2);
v_l_2405_ = lean_ctor_get(v_r_2065_, 3);
lean_inc(v_l_2405_);
v_r_2406_ = lean_ctor_get(v_r_2065_, 4);
v___x_2407_ = lean_unsigned_to_nat(1u);
v___x_2408_ = lean_nat_dec_lt(v_size_2397_, v_size_2402_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2544_; 
lean_inc(v_l_2400_);
lean_inc(v_v_2399_);
lean_inc(v_k_2398_);
v_isSharedCheck_2544_ = !lean_is_exclusive(v_l_2064_);
if (v_isSharedCheck_2544_ == 0)
{
lean_object* v_unused_2545_; lean_object* v_unused_2546_; lean_object* v_unused_2547_; lean_object* v_unused_2548_; lean_object* v_unused_2549_; 
v_unused_2545_ = lean_ctor_get(v_l_2064_, 4);
lean_dec(v_unused_2545_);
v_unused_2546_ = lean_ctor_get(v_l_2064_, 3);
lean_dec(v_unused_2546_);
v_unused_2547_ = lean_ctor_get(v_l_2064_, 2);
lean_dec(v_unused_2547_);
v_unused_2548_ = lean_ctor_get(v_l_2064_, 1);
lean_dec(v_unused_2548_);
v_unused_2549_ = lean_ctor_get(v_l_2064_, 0);
lean_dec(v_unused_2549_);
v___x_2410_ = v_l_2064_;
v_isShared_2411_ = v_isSharedCheck_2544_;
goto v_resetjp_2409_;
}
else
{
lean_dec(v_l_2064_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2544_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v_tree_2413_; 
v___x_2412_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2398_, v_v_2399_, v_l_2400_, v_r_2401_);
v_tree_2413_ = lean_ctor_get(v___x_2412_, 2);
lean_inc(v_tree_2413_);
if (lean_obj_tag(v_tree_2413_) == 0)
{
lean_object* v_k_2414_; lean_object* v_v_2415_; lean_object* v_size_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; 
v_k_2414_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_k_2414_);
v_v_2415_ = lean_ctor_get(v___x_2412_, 1);
lean_inc(v_v_2415_);
lean_dec_ref(v___x_2412_);
v_size_2416_ = lean_ctor_get(v_tree_2413_, 0);
v___x_2417_ = lean_unsigned_to_nat(3u);
v___x_2418_ = lean_nat_mul(v___x_2417_, v_size_2416_);
v___x_2419_ = lean_nat_dec_lt(v___x_2418_, v_size_2402_);
lean_dec(v___x_2418_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
lean_dec(v_l_2405_);
v___x_2420_ = lean_nat_add(v___x_2407_, v_size_2416_);
v___x_2421_ = lean_nat_add(v___x_2420_, v_size_2402_);
lean_dec(v___x_2420_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 4, v_r_2065_);
lean_ctor_set(v___x_2410_, 3, v_tree_2413_);
lean_ctor_set(v___x_2410_, 2, v_v_2415_);
lean_ctor_set(v___x_2410_, 1, v_k_2414_);
lean_ctor_set(v___x_2410_, 0, v___x_2421_);
v___x_2423_ = v___x_2410_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_k_2414_);
lean_ctor_set(v_reuseFailAlloc_2424_, 2, v_v_2415_);
lean_ctor_set(v_reuseFailAlloc_2424_, 3, v_tree_2413_);
lean_ctor_set(v_reuseFailAlloc_2424_, 4, v_r_2065_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
else
{
lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2479_; 
lean_inc(v_r_2406_);
lean_inc(v_v_2404_);
lean_inc(v_k_2403_);
lean_inc(v_size_2402_);
v_isSharedCheck_2479_ = !lean_is_exclusive(v_r_2065_);
if (v_isSharedCheck_2479_ == 0)
{
lean_object* v_unused_2480_; lean_object* v_unused_2481_; lean_object* v_unused_2482_; lean_object* v_unused_2483_; lean_object* v_unused_2484_; 
v_unused_2480_ = lean_ctor_get(v_r_2065_, 4);
lean_dec(v_unused_2480_);
v_unused_2481_ = lean_ctor_get(v_r_2065_, 3);
lean_dec(v_unused_2481_);
v_unused_2482_ = lean_ctor_get(v_r_2065_, 2);
lean_dec(v_unused_2482_);
v_unused_2483_ = lean_ctor_get(v_r_2065_, 1);
lean_dec(v_unused_2483_);
v_unused_2484_ = lean_ctor_get(v_r_2065_, 0);
lean_dec(v_unused_2484_);
v___x_2426_ = v_r_2065_;
v_isShared_2427_ = v_isSharedCheck_2479_;
goto v_resetjp_2425_;
}
else
{
lean_dec(v_r_2065_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2479_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_size_2428_; lean_object* v_k_2429_; lean_object* v_v_2430_; lean_object* v_l_2431_; lean_object* v_r_2432_; lean_object* v_size_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; uint8_t v___x_2436_; 
v_size_2428_ = lean_ctor_get(v_l_2405_, 0);
v_k_2429_ = lean_ctor_get(v_l_2405_, 1);
v_v_2430_ = lean_ctor_get(v_l_2405_, 2);
v_l_2431_ = lean_ctor_get(v_l_2405_, 3);
v_r_2432_ = lean_ctor_get(v_l_2405_, 4);
v_size_2433_ = lean_ctor_get(v_r_2406_, 0);
v___x_2434_ = lean_unsigned_to_nat(2u);
v___x_2435_ = lean_nat_mul(v___x_2434_, v_size_2433_);
v___x_2436_ = lean_nat_dec_lt(v_size_2428_, v___x_2435_);
lean_dec(v___x_2435_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2464_; 
lean_inc(v_r_2432_);
lean_inc(v_l_2431_);
lean_inc(v_v_2430_);
lean_inc(v_k_2429_);
v_isSharedCheck_2464_ = !lean_is_exclusive(v_l_2405_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; lean_object* v_unused_2466_; lean_object* v_unused_2467_; lean_object* v_unused_2468_; lean_object* v_unused_2469_; 
v_unused_2465_ = lean_ctor_get(v_l_2405_, 4);
lean_dec(v_unused_2465_);
v_unused_2466_ = lean_ctor_get(v_l_2405_, 3);
lean_dec(v_unused_2466_);
v_unused_2467_ = lean_ctor_get(v_l_2405_, 2);
lean_dec(v_unused_2467_);
v_unused_2468_ = lean_ctor_get(v_l_2405_, 1);
lean_dec(v_unused_2468_);
v_unused_2469_ = lean_ctor_get(v_l_2405_, 0);
lean_dec(v_unused_2469_);
v___x_2438_ = v_l_2405_;
v_isShared_2439_ = v_isSharedCheck_2464_;
goto v_resetjp_2437_;
}
else
{
lean_dec(v_l_2405_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2464_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2454_; 
v___x_2440_ = lean_nat_add(v___x_2407_, v_size_2416_);
v___x_2441_ = lean_nat_add(v___x_2440_, v_size_2402_);
lean_dec(v_size_2402_);
if (lean_obj_tag(v_l_2431_) == 0)
{
lean_object* v_size_2462_; 
v_size_2462_ = lean_ctor_get(v_l_2431_, 0);
lean_inc(v_size_2462_);
v___y_2454_ = v_size_2462_;
goto v___jp_2453_;
}
else
{
lean_object* v___x_2463_; 
v___x_2463_ = lean_unsigned_to_nat(0u);
v___y_2454_ = v___x_2463_;
goto v___jp_2453_;
}
v___jp_2442_:
{
lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2446_ = lean_nat_add(v___y_2443_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec(v___y_2443_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 4, v_r_2406_);
lean_ctor_set(v___x_2438_, 3, v_r_2432_);
lean_ctor_set(v___x_2438_, 2, v_v_2404_);
lean_ctor_set(v___x_2438_, 1, v_k_2403_);
lean_ctor_set(v___x_2438_, 0, v___x_2446_);
v___x_2448_ = v___x_2438_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_k_2403_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v_v_2404_);
lean_ctor_set(v_reuseFailAlloc_2452_, 3, v_r_2432_);
lean_ctor_set(v_reuseFailAlloc_2452_, 4, v_r_2406_);
v___x_2448_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2450_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 4, v___x_2448_);
lean_ctor_set(v___x_2426_, 3, v___y_2444_);
lean_ctor_set(v___x_2426_, 2, v_v_2430_);
lean_ctor_set(v___x_2426_, 1, v_k_2429_);
lean_ctor_set(v___x_2426_, 0, v___x_2441_);
v___x_2450_ = v___x_2426_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2441_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_k_2429_);
lean_ctor_set(v_reuseFailAlloc_2451_, 2, v_v_2430_);
lean_ctor_set(v_reuseFailAlloc_2451_, 3, v___y_2444_);
lean_ctor_set(v_reuseFailAlloc_2451_, 4, v___x_2448_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
v___jp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2455_ = lean_nat_add(v___x_2440_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec(v___x_2440_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 4, v_l_2431_);
lean_ctor_set(v___x_2410_, 3, v_tree_2413_);
lean_ctor_set(v___x_2410_, 2, v_v_2415_);
lean_ctor_set(v___x_2410_, 1, v_k_2414_);
lean_ctor_set(v___x_2410_, 0, v___x_2455_);
v___x_2457_ = v___x_2410_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2455_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v_k_2414_);
lean_ctor_set(v_reuseFailAlloc_2461_, 2, v_v_2415_);
lean_ctor_set(v_reuseFailAlloc_2461_, 3, v_tree_2413_);
lean_ctor_set(v_reuseFailAlloc_2461_, 4, v_l_2431_);
v___x_2457_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; 
v___x_2458_ = lean_nat_add(v___x_2407_, v_size_2433_);
if (lean_obj_tag(v_r_2432_) == 0)
{
lean_object* v_size_2459_; 
v_size_2459_ = lean_ctor_get(v_r_2432_, 0);
lean_inc(v_size_2459_);
v___y_2443_ = v___x_2458_;
v___y_2444_ = v___x_2457_;
v___y_2445_ = v_size_2459_;
goto v___jp_2442_;
}
else
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_unsigned_to_nat(0u);
v___y_2443_ = v___x_2458_;
v___y_2444_ = v___x_2457_;
v___y_2445_ = v___x_2460_;
goto v___jp_2442_;
}
}
}
}
}
else
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
v___x_2470_ = lean_nat_add(v___x_2407_, v_size_2416_);
v___x_2471_ = lean_nat_add(v___x_2470_, v_size_2402_);
lean_dec(v_size_2402_);
v___x_2472_ = lean_nat_add(v___x_2470_, v_size_2428_);
lean_dec(v___x_2470_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 4, v_l_2405_);
lean_ctor_set(v___x_2426_, 3, v_tree_2413_);
lean_ctor_set(v___x_2426_, 2, v_v_2415_);
lean_ctor_set(v___x_2426_, 1, v_k_2414_);
lean_ctor_set(v___x_2426_, 0, v___x_2472_);
v___x_2474_ = v___x_2426_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_k_2414_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v_v_2415_);
lean_ctor_set(v_reuseFailAlloc_2478_, 3, v_tree_2413_);
lean_ctor_set(v_reuseFailAlloc_2478_, 4, v_l_2405_);
v___x_2474_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2476_; 
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 4, v_r_2406_);
lean_ctor_set(v___x_2410_, 3, v___x_2474_);
lean_ctor_set(v___x_2410_, 2, v_v_2404_);
lean_ctor_set(v___x_2410_, 1, v_k_2403_);
lean_ctor_set(v___x_2410_, 0, v___x_2471_);
v___x_2476_ = v___x_2410_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_k_2403_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_v_2404_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v___x_2474_);
lean_ctor_set(v_reuseFailAlloc_2477_, 4, v_r_2406_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
}
else
{
lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2538_; 
lean_inc(v_r_2406_);
lean_inc(v_v_2404_);
lean_inc(v_k_2403_);
lean_inc(v_size_2402_);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_r_2065_);
if (v_isSharedCheck_2538_ == 0)
{
lean_object* v_unused_2539_; lean_object* v_unused_2540_; lean_object* v_unused_2541_; lean_object* v_unused_2542_; lean_object* v_unused_2543_; 
v_unused_2539_ = lean_ctor_get(v_r_2065_, 4);
lean_dec(v_unused_2539_);
v_unused_2540_ = lean_ctor_get(v_r_2065_, 3);
lean_dec(v_unused_2540_);
v_unused_2541_ = lean_ctor_get(v_r_2065_, 2);
lean_dec(v_unused_2541_);
v_unused_2542_ = lean_ctor_get(v_r_2065_, 1);
lean_dec(v_unused_2542_);
v_unused_2543_ = lean_ctor_get(v_r_2065_, 0);
lean_dec(v_unused_2543_);
v___x_2486_ = v_r_2065_;
v_isShared_2487_ = v_isSharedCheck_2538_;
goto v_resetjp_2485_;
}
else
{
lean_dec(v_r_2065_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2538_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
if (lean_obj_tag(v_l_2405_) == 0)
{
if (lean_obj_tag(v_r_2406_) == 0)
{
lean_object* v_k_2488_; lean_object* v_v_2489_; lean_object* v_size_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2494_; 
v_k_2488_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_k_2488_);
v_v_2489_ = lean_ctor_get(v___x_2412_, 1);
lean_inc(v_v_2489_);
lean_dec_ref(v___x_2412_);
v_size_2490_ = lean_ctor_get(v_l_2405_, 0);
v___x_2491_ = lean_nat_add(v___x_2407_, v_size_2402_);
lean_dec(v_size_2402_);
v___x_2492_ = lean_nat_add(v___x_2407_, v_size_2490_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 4, v_l_2405_);
lean_ctor_set(v___x_2486_, 3, v_tree_2413_);
lean_ctor_set(v___x_2486_, 2, v_v_2489_);
lean_ctor_set(v___x_2486_, 1, v_k_2488_);
lean_ctor_set(v___x_2486_, 0, v___x_2492_);
v___x_2494_ = v___x_2486_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2492_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_k_2488_);
lean_ctor_set(v_reuseFailAlloc_2498_, 2, v_v_2489_);
lean_ctor_set(v_reuseFailAlloc_2498_, 3, v_tree_2413_);
lean_ctor_set(v_reuseFailAlloc_2498_, 4, v_l_2405_);
v___x_2494_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
lean_object* v___x_2496_; 
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 4, v_r_2406_);
lean_ctor_set(v___x_2410_, 3, v___x_2494_);
lean_ctor_set(v___x_2410_, 2, v_v_2404_);
lean_ctor_set(v___x_2410_, 1, v_k_2403_);
lean_ctor_set(v___x_2410_, 0, v___x_2491_);
v___x_2496_ = v___x_2410_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v_k_2403_);
lean_ctor_set(v_reuseFailAlloc_2497_, 2, v_v_2404_);
lean_ctor_set(v_reuseFailAlloc_2497_, 3, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2497_, 4, v_r_2406_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
else
{
lean_object* v_k_2499_; lean_object* v_v_2500_; lean_object* v_k_2501_; lean_object* v_v_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2516_; 
lean_dec(v_size_2402_);
v_k_2499_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_k_2499_);
v_v_2500_ = lean_ctor_get(v___x_2412_, 1);
lean_inc(v_v_2500_);
lean_dec_ref(v___x_2412_);
v_k_2501_ = lean_ctor_get(v_l_2405_, 1);
v_v_2502_ = lean_ctor_get(v_l_2405_, 2);
v_isSharedCheck_2516_ = !lean_is_exclusive(v_l_2405_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; lean_object* v_unused_2518_; lean_object* v_unused_2519_; 
v_unused_2517_ = lean_ctor_get(v_l_2405_, 4);
lean_dec(v_unused_2517_);
v_unused_2518_ = lean_ctor_get(v_l_2405_, 3);
lean_dec(v_unused_2518_);
v_unused_2519_ = lean_ctor_get(v_l_2405_, 0);
lean_dec(v_unused_2519_);
v___x_2504_ = v_l_2405_;
v_isShared_2505_ = v_isSharedCheck_2516_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_v_2502_);
lean_inc(v_k_2501_);
lean_dec(v_l_2405_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2516_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2506_ = lean_unsigned_to_nat(3u);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 4, v_r_2406_);
lean_ctor_set(v___x_2504_, 3, v_r_2406_);
lean_ctor_set(v___x_2504_, 2, v_v_2500_);
lean_ctor_set(v___x_2504_, 1, v_k_2499_);
lean_ctor_set(v___x_2504_, 0, v___x_2407_);
v___x_2508_ = v___x_2504_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_k_2499_);
lean_ctor_set(v_reuseFailAlloc_2515_, 2, v_v_2500_);
lean_ctor_set(v_reuseFailAlloc_2515_, 3, v_r_2406_);
lean_ctor_set(v_reuseFailAlloc_2515_, 4, v_r_2406_);
v___x_2508_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2510_; 
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 3, v_r_2406_);
lean_ctor_set(v___x_2486_, 0, v___x_2407_);
v___x_2510_ = v___x_2486_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_k_2403_);
lean_ctor_set(v_reuseFailAlloc_2514_, 2, v_v_2404_);
lean_ctor_set(v_reuseFailAlloc_2514_, 3, v_r_2406_);
lean_ctor_set(v_reuseFailAlloc_2514_, 4, v_r_2406_);
v___x_2510_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_object* v___x_2512_; 
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 4, v___x_2510_);
lean_ctor_set(v___x_2410_, 3, v___x_2508_);
lean_ctor_set(v___x_2410_, 2, v_v_2502_);
lean_ctor_set(v___x_2410_, 1, v_k_2501_);
lean_ctor_set(v___x_2410_, 0, v___x_2506_);
v___x_2512_ = v___x_2410_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_k_2501_);
lean_ctor_set(v_reuseFailAlloc_2513_, 2, v_v_2502_);
lean_ctor_set(v_reuseFailAlloc_2513_, 3, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2513_, 4, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2406_) == 0)
{
lean_object* v_k_2520_; lean_object* v_v_2521_; lean_object* v___x_2522_; lean_object* v___x_2524_; 
lean_dec(v_size_2402_);
v_k_2520_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_k_2520_);
v_v_2521_ = lean_ctor_get(v___x_2412_, 1);
lean_inc(v_v_2521_);
lean_dec_ref(v___x_2412_);
v___x_2522_ = lean_unsigned_to_nat(3u);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 4, v_l_2405_);
lean_ctor_set(v___x_2486_, 2, v_v_2521_);
lean_ctor_set(v___x_2486_, 1, v_k_2520_);
lean_ctor_set(v___x_2486_, 0, v___x_2407_);
v___x_2524_ = v___x_2486_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_k_2520_);
lean_ctor_set(v_reuseFailAlloc_2528_, 2, v_v_2521_);
lean_ctor_set(v_reuseFailAlloc_2528_, 3, v_l_2405_);
lean_ctor_set(v_reuseFailAlloc_2528_, 4, v_l_2405_);
v___x_2524_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2526_; 
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 4, v_r_2406_);
lean_ctor_set(v___x_2410_, 3, v___x_2524_);
lean_ctor_set(v___x_2410_, 2, v_v_2404_);
lean_ctor_set(v___x_2410_, 1, v_k_2403_);
lean_ctor_set(v___x_2410_, 0, v___x_2522_);
v___x_2526_ = v___x_2410_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v_k_2403_);
lean_ctor_set(v_reuseFailAlloc_2527_, 2, v_v_2404_);
lean_ctor_set(v_reuseFailAlloc_2527_, 3, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2527_, 4, v_r_2406_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
else
{
lean_object* v_k_2529_; lean_object* v_v_2530_; lean_object* v___x_2532_; 
v_k_2529_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_k_2529_);
v_v_2530_ = lean_ctor_get(v___x_2412_, 1);
lean_inc(v_v_2530_);
lean_dec_ref(v___x_2412_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 3, v_r_2406_);
v___x_2532_ = v___x_2486_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_size_2402_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_k_2403_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_v_2404_);
lean_ctor_set(v_reuseFailAlloc_2537_, 3, v_r_2406_);
lean_ctor_set(v_reuseFailAlloc_2537_, 4, v_r_2406_);
v___x_2532_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2533_ = lean_unsigned_to_nat(2u);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 4, v___x_2532_);
lean_ctor_set(v___x_2410_, 3, v_r_2406_);
lean_ctor_set(v___x_2410_, 2, v_v_2530_);
lean_ctor_set(v___x_2410_, 1, v_k_2529_);
lean_ctor_set(v___x_2410_, 0, v___x_2533_);
v___x_2535_ = v___x_2410_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_k_2529_);
lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_v_2530_);
lean_ctor_set(v_reuseFailAlloc_2536_, 3, v_r_2406_);
lean_ctor_set(v_reuseFailAlloc_2536_, 4, v___x_2532_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
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
lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2702_; 
lean_inc(v_r_2406_);
lean_inc(v_v_2404_);
lean_inc(v_k_2403_);
v_isSharedCheck_2702_ = !lean_is_exclusive(v_r_2065_);
if (v_isSharedCheck_2702_ == 0)
{
lean_object* v_unused_2703_; lean_object* v_unused_2704_; lean_object* v_unused_2705_; lean_object* v_unused_2706_; lean_object* v_unused_2707_; 
v_unused_2703_ = lean_ctor_get(v_r_2065_, 4);
lean_dec(v_unused_2703_);
v_unused_2704_ = lean_ctor_get(v_r_2065_, 3);
lean_dec(v_unused_2704_);
v_unused_2705_ = lean_ctor_get(v_r_2065_, 2);
lean_dec(v_unused_2705_);
v_unused_2706_ = lean_ctor_get(v_r_2065_, 1);
lean_dec(v_unused_2706_);
v_unused_2707_ = lean_ctor_get(v_r_2065_, 0);
lean_dec(v_unused_2707_);
v___x_2551_ = v_r_2065_;
v_isShared_2552_ = v_isSharedCheck_2702_;
goto v_resetjp_2550_;
}
else
{
lean_dec(v_r_2065_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2702_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2553_; lean_object* v_tree_2554_; 
v___x_2553_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2403_, v_v_2404_, v_l_2405_, v_r_2406_);
v_tree_2554_ = lean_ctor_get(v___x_2553_, 2);
lean_inc(v_tree_2554_);
if (lean_obj_tag(v_tree_2554_) == 0)
{
lean_object* v_k_2555_; lean_object* v_v_2556_; lean_object* v_size_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
v_k_2555_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_k_2555_);
v_v_2556_ = lean_ctor_get(v___x_2553_, 1);
lean_inc(v_v_2556_);
lean_dec_ref(v___x_2553_);
v_size_2557_ = lean_ctor_get(v_tree_2554_, 0);
v___x_2558_ = lean_unsigned_to_nat(3u);
v___x_2559_ = lean_nat_mul(v___x_2558_, v_size_2557_);
v___x_2560_ = lean_nat_dec_lt(v___x_2559_, v_size_2397_);
lean_dec(v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2564_; 
lean_dec(v_r_2401_);
v___x_2561_ = lean_nat_add(v___x_2407_, v_size_2397_);
v___x_2562_ = lean_nat_add(v___x_2561_, v_size_2557_);
lean_dec(v___x_2561_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 4, v_tree_2554_);
lean_ctor_set(v___x_2551_, 3, v_l_2064_);
lean_ctor_set(v___x_2551_, 2, v_v_2556_);
lean_ctor_set(v___x_2551_, 1, v_k_2555_);
lean_ctor_set(v___x_2551_, 0, v___x_2562_);
v___x_2564_ = v___x_2551_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_k_2555_);
lean_ctor_set(v_reuseFailAlloc_2565_, 2, v_v_2556_);
lean_ctor_set(v_reuseFailAlloc_2565_, 3, v_l_2064_);
lean_ctor_set(v_reuseFailAlloc_2565_, 4, v_tree_2554_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
else
{
lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2631_; 
lean_inc(v_l_2400_);
lean_inc(v_v_2399_);
lean_inc(v_k_2398_);
lean_inc(v_size_2397_);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_l_2064_);
if (v_isSharedCheck_2631_ == 0)
{
lean_object* v_unused_2632_; lean_object* v_unused_2633_; lean_object* v_unused_2634_; lean_object* v_unused_2635_; lean_object* v_unused_2636_; 
v_unused_2632_ = lean_ctor_get(v_l_2064_, 4);
lean_dec(v_unused_2632_);
v_unused_2633_ = lean_ctor_get(v_l_2064_, 3);
lean_dec(v_unused_2633_);
v_unused_2634_ = lean_ctor_get(v_l_2064_, 2);
lean_dec(v_unused_2634_);
v_unused_2635_ = lean_ctor_get(v_l_2064_, 1);
lean_dec(v_unused_2635_);
v_unused_2636_ = lean_ctor_get(v_l_2064_, 0);
lean_dec(v_unused_2636_);
v___x_2567_ = v_l_2064_;
v_isShared_2568_ = v_isSharedCheck_2631_;
goto v_resetjp_2566_;
}
else
{
lean_dec(v_l_2064_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2631_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v_size_2569_; lean_object* v_size_2570_; lean_object* v_k_2571_; lean_object* v_v_2572_; lean_object* v_l_2573_; lean_object* v_r_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; 
v_size_2569_ = lean_ctor_get(v_l_2400_, 0);
v_size_2570_ = lean_ctor_get(v_r_2401_, 0);
v_k_2571_ = lean_ctor_get(v_r_2401_, 1);
v_v_2572_ = lean_ctor_get(v_r_2401_, 2);
v_l_2573_ = lean_ctor_get(v_r_2401_, 3);
v_r_2574_ = lean_ctor_get(v_r_2401_, 4);
v___x_2575_ = lean_unsigned_to_nat(2u);
v___x_2576_ = lean_nat_mul(v___x_2575_, v_size_2569_);
v___x_2577_ = lean_nat_dec_lt(v_size_2570_, v___x_2576_);
lean_dec(v___x_2576_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2615_; 
lean_inc(v_r_2574_);
lean_inc(v_l_2573_);
lean_inc(v_v_2572_);
lean_inc(v_k_2571_);
lean_del_object(v___x_2567_);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_r_2401_);
if (v_isSharedCheck_2615_ == 0)
{
lean_object* v_unused_2616_; lean_object* v_unused_2617_; lean_object* v_unused_2618_; lean_object* v_unused_2619_; lean_object* v_unused_2620_; 
v_unused_2616_ = lean_ctor_get(v_r_2401_, 4);
lean_dec(v_unused_2616_);
v_unused_2617_ = lean_ctor_get(v_r_2401_, 3);
lean_dec(v_unused_2617_);
v_unused_2618_ = lean_ctor_get(v_r_2401_, 2);
lean_dec(v_unused_2618_);
v_unused_2619_ = lean_ctor_get(v_r_2401_, 1);
lean_dec(v_unused_2619_);
v_unused_2620_ = lean_ctor_get(v_r_2401_, 0);
lean_dec(v_unused_2620_);
v___x_2579_ = v_r_2401_;
v_isShared_2580_ = v_isSharedCheck_2615_;
goto v_resetjp_2578_;
}
else
{
lean_dec(v_r_2401_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2615_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___x_2603_; lean_object* v___y_2605_; 
v___x_2581_ = lean_nat_add(v___x_2407_, v_size_2397_);
lean_dec(v_size_2397_);
v___x_2582_ = lean_nat_add(v___x_2581_, v_size_2557_);
lean_dec(v___x_2581_);
v___x_2603_ = lean_nat_add(v___x_2407_, v_size_2569_);
if (lean_obj_tag(v_l_2573_) == 0)
{
lean_object* v_size_2613_; 
v_size_2613_ = lean_ctor_get(v_l_2573_, 0);
lean_inc(v_size_2613_);
v___y_2605_ = v_size_2613_;
goto v___jp_2604_;
}
else
{
lean_object* v___x_2614_; 
v___x_2614_ = lean_unsigned_to_nat(0u);
v___y_2605_ = v___x_2614_;
goto v___jp_2604_;
}
v___jp_2583_:
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
v___x_2587_ = lean_nat_add(v___y_2585_, v___y_2586_);
lean_dec(v___y_2586_);
lean_dec(v___y_2585_);
lean_inc_ref(v_tree_2554_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 4, v_tree_2554_);
lean_ctor_set(v___x_2579_, 3, v_r_2574_);
lean_ctor_set(v___x_2579_, 2, v_v_2556_);
lean_ctor_set(v___x_2579_, 1, v_k_2555_);
lean_ctor_set(v___x_2579_, 0, v___x_2587_);
v___x_2589_ = v___x_2579_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v_k_2555_);
lean_ctor_set(v_reuseFailAlloc_2602_, 2, v_v_2556_);
lean_ctor_set(v_reuseFailAlloc_2602_, 3, v_r_2574_);
lean_ctor_set(v_reuseFailAlloc_2602_, 4, v_tree_2554_);
v___x_2589_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
v_isSharedCheck_2596_ = !lean_is_exclusive(v_tree_2554_);
if (v_isSharedCheck_2596_ == 0)
{
lean_object* v_unused_2597_; lean_object* v_unused_2598_; lean_object* v_unused_2599_; lean_object* v_unused_2600_; lean_object* v_unused_2601_; 
v_unused_2597_ = lean_ctor_get(v_tree_2554_, 4);
lean_dec(v_unused_2597_);
v_unused_2598_ = lean_ctor_get(v_tree_2554_, 3);
lean_dec(v_unused_2598_);
v_unused_2599_ = lean_ctor_get(v_tree_2554_, 2);
lean_dec(v_unused_2599_);
v_unused_2600_ = lean_ctor_get(v_tree_2554_, 1);
lean_dec(v_unused_2600_);
v_unused_2601_ = lean_ctor_get(v_tree_2554_, 0);
lean_dec(v_unused_2601_);
v___x_2591_ = v_tree_2554_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_dec(v_tree_2554_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 4, v___x_2589_);
lean_ctor_set(v___x_2591_, 3, v___y_2584_);
lean_ctor_set(v___x_2591_, 2, v_v_2572_);
lean_ctor_set(v___x_2591_, 1, v_k_2571_);
lean_ctor_set(v___x_2591_, 0, v___x_2582_);
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2582_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v_k_2571_);
lean_ctor_set(v_reuseFailAlloc_2595_, 2, v_v_2572_);
lean_ctor_set(v_reuseFailAlloc_2595_, 3, v___y_2584_);
lean_ctor_set(v_reuseFailAlloc_2595_, 4, v___x_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
v___jp_2604_:
{
lean_object* v___x_2606_; lean_object* v___x_2608_; 
v___x_2606_ = lean_nat_add(v___x_2603_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec(v___x_2603_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 4, v_l_2573_);
lean_ctor_set(v___x_2551_, 3, v_l_2400_);
lean_ctor_set(v___x_2551_, 2, v_v_2399_);
lean_ctor_set(v___x_2551_, 1, v_k_2398_);
lean_ctor_set(v___x_2551_, 0, v___x_2606_);
v___x_2608_ = v___x_2551_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2606_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_k_2398_);
lean_ctor_set(v_reuseFailAlloc_2612_, 2, v_v_2399_);
lean_ctor_set(v_reuseFailAlloc_2612_, 3, v_l_2400_);
lean_ctor_set(v_reuseFailAlloc_2612_, 4, v_l_2573_);
v___x_2608_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
lean_object* v___x_2609_; 
v___x_2609_ = lean_nat_add(v___x_2407_, v_size_2557_);
if (lean_obj_tag(v_r_2574_) == 0)
{
lean_object* v_size_2610_; 
v_size_2610_ = lean_ctor_get(v_r_2574_, 0);
lean_inc(v_size_2610_);
v___y_2584_ = v___x_2608_;
v___y_2585_ = v___x_2609_;
v___y_2586_ = v_size_2610_;
goto v___jp_2583_;
}
else
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_unsigned_to_nat(0u);
v___y_2584_ = v___x_2608_;
v___y_2585_ = v___x_2609_;
v___y_2586_ = v___x_2611_;
goto v___jp_2583_;
}
}
}
}
}
else
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2621_ = lean_nat_add(v___x_2407_, v_size_2397_);
lean_dec(v_size_2397_);
v___x_2622_ = lean_nat_add(v___x_2621_, v_size_2557_);
lean_dec(v___x_2621_);
v___x_2623_ = lean_nat_add(v___x_2407_, v_size_2557_);
v___x_2624_ = lean_nat_add(v___x_2623_, v_size_2570_);
lean_dec(v___x_2623_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 4, v_tree_2554_);
lean_ctor_set(v___x_2551_, 3, v_r_2401_);
lean_ctor_set(v___x_2551_, 2, v_v_2556_);
lean_ctor_set(v___x_2551_, 1, v_k_2555_);
lean_ctor_set(v___x_2551_, 0, v___x_2624_);
v___x_2626_ = v___x_2551_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_k_2555_);
lean_ctor_set(v_reuseFailAlloc_2630_, 2, v_v_2556_);
lean_ctor_set(v_reuseFailAlloc_2630_, 3, v_r_2401_);
lean_ctor_set(v_reuseFailAlloc_2630_, 4, v_tree_2554_);
v___x_2626_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
lean_object* v___x_2628_; 
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 4, v___x_2626_);
lean_ctor_set(v___x_2567_, 0, v___x_2622_);
v___x_2628_ = v___x_2567_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_k_2398_);
lean_ctor_set(v_reuseFailAlloc_2629_, 2, v_v_2399_);
lean_ctor_set(v_reuseFailAlloc_2629_, 3, v_l_2400_);
lean_ctor_set(v_reuseFailAlloc_2629_, 4, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2400_) == 0)
{
lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2660_; 
lean_inc_ref(v_l_2400_);
lean_inc(v_v_2399_);
lean_inc(v_k_2398_);
lean_inc(v_size_2397_);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_l_2064_);
if (v_isSharedCheck_2660_ == 0)
{
lean_object* v_unused_2661_; lean_object* v_unused_2662_; lean_object* v_unused_2663_; lean_object* v_unused_2664_; lean_object* v_unused_2665_; 
v_unused_2661_ = lean_ctor_get(v_l_2064_, 4);
lean_dec(v_unused_2661_);
v_unused_2662_ = lean_ctor_get(v_l_2064_, 3);
lean_dec(v_unused_2662_);
v_unused_2663_ = lean_ctor_get(v_l_2064_, 2);
lean_dec(v_unused_2663_);
v_unused_2664_ = lean_ctor_get(v_l_2064_, 1);
lean_dec(v_unused_2664_);
v_unused_2665_ = lean_ctor_get(v_l_2064_, 0);
lean_dec(v_unused_2665_);
v___x_2638_ = v_l_2064_;
v_isShared_2639_ = v_isSharedCheck_2660_;
goto v_resetjp_2637_;
}
else
{
lean_dec(v_l_2064_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2660_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
if (lean_obj_tag(v_r_2401_) == 0)
{
lean_object* v_k_2640_; lean_object* v_v_2641_; lean_object* v_size_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2646_; 
v_k_2640_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_k_2640_);
v_v_2641_ = lean_ctor_get(v___x_2553_, 1);
lean_inc(v_v_2641_);
lean_dec_ref(v___x_2553_);
v_size_2642_ = lean_ctor_get(v_r_2401_, 0);
v___x_2643_ = lean_nat_add(v___x_2407_, v_size_2397_);
lean_dec(v_size_2397_);
v___x_2644_ = lean_nat_add(v___x_2407_, v_size_2642_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 4, v_tree_2554_);
lean_ctor_set(v___x_2551_, 3, v_r_2401_);
lean_ctor_set(v___x_2551_, 2, v_v_2641_);
lean_ctor_set(v___x_2551_, 1, v_k_2640_);
lean_ctor_set(v___x_2551_, 0, v___x_2644_);
v___x_2646_ = v___x_2551_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v_k_2640_);
lean_ctor_set(v_reuseFailAlloc_2650_, 2, v_v_2641_);
lean_ctor_set(v_reuseFailAlloc_2650_, 3, v_r_2401_);
lean_ctor_set(v_reuseFailAlloc_2650_, 4, v_tree_2554_);
v___x_2646_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
lean_object* v___x_2648_; 
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 4, v___x_2646_);
lean_ctor_set(v___x_2638_, 0, v___x_2643_);
v___x_2648_ = v___x_2638_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_k_2398_);
lean_ctor_set(v_reuseFailAlloc_2649_, 2, v_v_2399_);
lean_ctor_set(v_reuseFailAlloc_2649_, 3, v_l_2400_);
lean_ctor_set(v_reuseFailAlloc_2649_, 4, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
else
{
lean_object* v_k_2651_; lean_object* v_v_2652_; lean_object* v___x_2653_; lean_object* v___x_2655_; 
lean_dec(v_size_2397_);
v_k_2651_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_k_2651_);
v_v_2652_ = lean_ctor_get(v___x_2553_, 1);
lean_inc(v_v_2652_);
lean_dec_ref(v___x_2553_);
v___x_2653_ = lean_unsigned_to_nat(3u);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 4, v_r_2401_);
lean_ctor_set(v___x_2551_, 3, v_r_2401_);
lean_ctor_set(v___x_2551_, 2, v_v_2652_);
lean_ctor_set(v___x_2551_, 1, v_k_2651_);
lean_ctor_set(v___x_2551_, 0, v___x_2407_);
v___x_2655_ = v___x_2551_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v_k_2651_);
lean_ctor_set(v_reuseFailAlloc_2659_, 2, v_v_2652_);
lean_ctor_set(v_reuseFailAlloc_2659_, 3, v_r_2401_);
lean_ctor_set(v_reuseFailAlloc_2659_, 4, v_r_2401_);
v___x_2655_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
lean_object* v___x_2657_; 
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 4, v___x_2655_);
lean_ctor_set(v___x_2638_, 0, v___x_2653_);
v___x_2657_ = v___x_2638_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2653_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_k_2398_);
lean_ctor_set(v_reuseFailAlloc_2658_, 2, v_v_2399_);
lean_ctor_set(v_reuseFailAlloc_2658_, 3, v_l_2400_);
lean_ctor_set(v_reuseFailAlloc_2658_, 4, v___x_2655_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2401_) == 0)
{
lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2690_; 
lean_inc(v_l_2400_);
lean_inc(v_v_2399_);
lean_inc(v_k_2398_);
v_isSharedCheck_2690_ = !lean_is_exclusive(v_l_2064_);
if (v_isSharedCheck_2690_ == 0)
{
lean_object* v_unused_2691_; lean_object* v_unused_2692_; lean_object* v_unused_2693_; lean_object* v_unused_2694_; lean_object* v_unused_2695_; 
v_unused_2691_ = lean_ctor_get(v_l_2064_, 4);
lean_dec(v_unused_2691_);
v_unused_2692_ = lean_ctor_get(v_l_2064_, 3);
lean_dec(v_unused_2692_);
v_unused_2693_ = lean_ctor_get(v_l_2064_, 2);
lean_dec(v_unused_2693_);
v_unused_2694_ = lean_ctor_get(v_l_2064_, 1);
lean_dec(v_unused_2694_);
v_unused_2695_ = lean_ctor_get(v_l_2064_, 0);
lean_dec(v_unused_2695_);
v___x_2667_ = v_l_2064_;
v_isShared_2668_ = v_isSharedCheck_2690_;
goto v_resetjp_2666_;
}
else
{
lean_dec(v_l_2064_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2690_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v_k_2669_; lean_object* v_v_2670_; lean_object* v_k_2671_; lean_object* v_v_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2686_; 
v_k_2669_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_k_2669_);
v_v_2670_ = lean_ctor_get(v___x_2553_, 1);
lean_inc(v_v_2670_);
lean_dec_ref(v___x_2553_);
v_k_2671_ = lean_ctor_get(v_r_2401_, 1);
v_v_2672_ = lean_ctor_get(v_r_2401_, 2);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_r_2401_);
if (v_isSharedCheck_2686_ == 0)
{
lean_object* v_unused_2687_; lean_object* v_unused_2688_; lean_object* v_unused_2689_; 
v_unused_2687_ = lean_ctor_get(v_r_2401_, 4);
lean_dec(v_unused_2687_);
v_unused_2688_ = lean_ctor_get(v_r_2401_, 3);
lean_dec(v_unused_2688_);
v_unused_2689_ = lean_ctor_get(v_r_2401_, 0);
lean_dec(v_unused_2689_);
v___x_2674_ = v_r_2401_;
v_isShared_2675_ = v_isSharedCheck_2686_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_v_2672_);
lean_inc(v_k_2671_);
lean_dec(v_r_2401_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2686_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2676_; lean_object* v___x_2678_; 
v___x_2676_ = lean_unsigned_to_nat(3u);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 4, v_l_2400_);
lean_ctor_set(v___x_2674_, 3, v_l_2400_);
lean_ctor_set(v___x_2674_, 2, v_v_2399_);
lean_ctor_set(v___x_2674_, 1, v_k_2398_);
lean_ctor_set(v___x_2674_, 0, v___x_2407_);
v___x_2678_ = v___x_2674_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_k_2398_);
lean_ctor_set(v_reuseFailAlloc_2685_, 2, v_v_2399_);
lean_ctor_set(v_reuseFailAlloc_2685_, 3, v_l_2400_);
lean_ctor_set(v_reuseFailAlloc_2685_, 4, v_l_2400_);
v___x_2678_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
lean_object* v___x_2680_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 4, v_l_2400_);
lean_ctor_set(v___x_2551_, 3, v_l_2400_);
lean_ctor_set(v___x_2551_, 2, v_v_2670_);
lean_ctor_set(v___x_2551_, 1, v_k_2669_);
lean_ctor_set(v___x_2551_, 0, v___x_2407_);
v___x_2680_ = v___x_2551_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_k_2669_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v_v_2670_);
lean_ctor_set(v_reuseFailAlloc_2684_, 3, v_l_2400_);
lean_ctor_set(v_reuseFailAlloc_2684_, 4, v_l_2400_);
v___x_2680_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2682_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 4, v___x_2680_);
lean_ctor_set(v___x_2667_, 3, v___x_2678_);
lean_ctor_set(v___x_2667_, 2, v_v_2672_);
lean_ctor_set(v___x_2667_, 1, v_k_2671_);
lean_ctor_set(v___x_2667_, 0, v___x_2676_);
v___x_2682_ = v___x_2667_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2676_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_k_2671_);
lean_ctor_set(v_reuseFailAlloc_2683_, 2, v_v_2672_);
lean_ctor_set(v_reuseFailAlloc_2683_, 3, v___x_2678_);
lean_ctor_set(v_reuseFailAlloc_2683_, 4, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
}
else
{
lean_object* v_k_2696_; lean_object* v_v_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
v_k_2696_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_k_2696_);
v_v_2697_ = lean_ctor_get(v___x_2553_, 1);
lean_inc(v_v_2697_);
lean_dec_ref(v___x_2553_);
v___x_2698_ = lean_unsigned_to_nat(2u);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 4, v_r_2401_);
lean_ctor_set(v___x_2551_, 3, v_l_2064_);
lean_ctor_set(v___x_2551_, 2, v_v_2697_);
lean_ctor_set(v___x_2551_, 1, v_k_2696_);
lean_ctor_set(v___x_2551_, 0, v___x_2698_);
v___x_2700_ = v___x_2551_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2698_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_k_2696_);
lean_ctor_set(v_reuseFailAlloc_2701_, 2, v_v_2697_);
lean_ctor_set(v_reuseFailAlloc_2701_, 3, v_l_2064_);
lean_ctor_set(v_reuseFailAlloc_2701_, 4, v_r_2401_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
}
}
}
else
{
return v_l_2064_;
}
}
else
{
return v_r_2065_;
}
}
default: 
{
goto v___jp_2102_;
}
}
}
else
{
goto v___jp_2102_;
}
}
else
{
lean_del_object(v___x_2067_);
goto v___jp_2254_;
}
v___jp_2069_:
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2078_ = lean_nat_add(v___y_2073_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec(v___y_2073_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 4, v___y_2072_);
lean_ctor_set(v___x_2067_, 3, v___y_2074_);
lean_ctor_set(v___x_2067_, 0, v___x_2078_);
v___x_2080_ = v___x_2067_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_k_2062_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v_v_2063_);
lean_ctor_set(v_reuseFailAlloc_2082_, 3, v___y_2074_);
lean_ctor_set(v_reuseFailAlloc_2082_, 4, v___y_2072_);
v___x_2080_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2081_, 0, v___y_2076_);
lean_ctor_set(v___x_2081_, 1, v___y_2075_);
lean_ctor_set(v___x_2081_, 2, v___y_2071_);
lean_ctor_set(v___x_2081_, 3, v___y_2070_);
lean_ctor_set(v___x_2081_, 4, v___x_2080_);
return v___x_2081_;
}
}
v___jp_2083_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2097_ = lean_nat_add(v___y_2086_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec(v___y_2086_);
v___x_2098_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v___y_2093_);
lean_ctor_set(v___x_2098_, 2, v___y_2095_);
lean_ctor_set(v___x_2098_, 3, v___y_2085_);
lean_ctor_set(v___x_2098_, 4, v___y_2090_);
v___x_2099_ = lean_nat_add(v___y_2084_, v___y_2088_);
lean_dec(v___y_2088_);
if (lean_obj_tag(v___y_2091_) == 0)
{
lean_object* v_size_2100_; 
v_size_2100_ = lean_ctor_get(v___y_2091_, 0);
lean_inc(v_size_2100_);
v___y_2070_ = v___x_2098_;
v___y_2071_ = v___y_2087_;
v___y_2072_ = v___y_2089_;
v___y_2073_ = v___x_2099_;
v___y_2074_ = v___y_2091_;
v___y_2075_ = v___y_2092_;
v___y_2076_ = v___y_2094_;
v___y_2077_ = v_size_2100_;
goto v___jp_2069_;
}
else
{
lean_object* v___x_2101_; 
v___x_2101_ = lean_unsigned_to_nat(0u);
v___y_2070_ = v___x_2098_;
v___y_2071_ = v___y_2087_;
v___y_2072_ = v___y_2089_;
v___y_2073_ = v___x_2099_;
v___y_2074_ = v___y_2091_;
v___y_2075_ = v___y_2092_;
v___y_2076_ = v___y_2094_;
v___y_2077_ = v___x_2101_;
goto v___jp_2069_;
}
}
v___jp_2102_:
{
lean_object* v_impl_2103_; lean_object* v___x_2104_; 
v_impl_2103_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v_k_2046_, v_r_2065_);
v___x_2104_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2103_) == 0)
{
if (lean_obj_tag(v_l_2064_) == 0)
{
lean_object* v_size_2105_; lean_object* v_size_2106_; lean_object* v_k_2107_; lean_object* v_v_2108_; lean_object* v_l_2109_; lean_object* v_r_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v_size_2105_ = lean_ctor_get(v_impl_2103_, 0);
lean_inc(v_size_2105_);
v_size_2106_ = lean_ctor_get(v_l_2064_, 0);
v_k_2107_ = lean_ctor_get(v_l_2064_, 1);
v_v_2108_ = lean_ctor_get(v_l_2064_, 2);
v_l_2109_ = lean_ctor_get(v_l_2064_, 3);
v_r_2110_ = lean_ctor_get(v_l_2064_, 4);
v___x_2111_ = lean_unsigned_to_nat(3u);
v___x_2112_ = lean_nat_mul(v___x_2111_, v_size_2105_);
v___x_2113_ = lean_nat_dec_lt(v___x_2112_, v_size_2106_);
lean_dec(v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_del_object(v___x_2067_);
v___x_2114_ = lean_nat_add(v___x_2104_, v_size_2106_);
v___x_2115_ = lean_nat_add(v___x_2114_, v_size_2105_);
lean_dec(v_size_2105_);
lean_dec(v___x_2114_);
v___x_2116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set(v___x_2116_, 1, v_k_2062_);
lean_ctor_set(v___x_2116_, 2, v_v_2063_);
lean_ctor_set(v___x_2116_, 3, v_l_2064_);
lean_ctor_set(v___x_2116_, 4, v_impl_2103_);
return v___x_2116_;
}
else
{
lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2153_; 
lean_inc(v_r_2110_);
lean_inc(v_l_2109_);
lean_inc(v_v_2108_);
lean_inc(v_k_2107_);
lean_inc(v_size_2106_);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_l_2064_);
if (v_isSharedCheck_2153_ == 0)
{
lean_object* v_unused_2154_; lean_object* v_unused_2155_; lean_object* v_unused_2156_; lean_object* v_unused_2157_; lean_object* v_unused_2158_; 
v_unused_2154_ = lean_ctor_get(v_l_2064_, 4);
lean_dec(v_unused_2154_);
v_unused_2155_ = lean_ctor_get(v_l_2064_, 3);
lean_dec(v_unused_2155_);
v_unused_2156_ = lean_ctor_get(v_l_2064_, 2);
lean_dec(v_unused_2156_);
v_unused_2157_ = lean_ctor_get(v_l_2064_, 1);
lean_dec(v_unused_2157_);
v_unused_2158_ = lean_ctor_get(v_l_2064_, 0);
lean_dec(v_unused_2158_);
v___x_2118_ = v_l_2064_;
v_isShared_2119_ = v_isSharedCheck_2153_;
goto v_resetjp_2117_;
}
else
{
lean_dec(v_l_2064_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2153_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v_size_2120_; lean_object* v_size_2121_; lean_object* v_k_2122_; lean_object* v_v_2123_; lean_object* v_l_2124_; lean_object* v_r_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; 
v_size_2120_ = lean_ctor_get(v_l_2109_, 0);
v_size_2121_ = lean_ctor_get(v_r_2110_, 0);
v_k_2122_ = lean_ctor_get(v_r_2110_, 1);
v_v_2123_ = lean_ctor_get(v_r_2110_, 2);
v_l_2124_ = lean_ctor_get(v_r_2110_, 3);
v_r_2125_ = lean_ctor_get(v_r_2110_, 4);
v___x_2126_ = lean_unsigned_to_nat(2u);
v___x_2127_ = lean_nat_mul(v___x_2126_, v_size_2120_);
v___x_2128_ = lean_nat_dec_lt(v_size_2121_, v___x_2127_);
lean_dec(v___x_2127_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_inc(v_r_2125_);
lean_inc(v_l_2124_);
lean_inc(v_v_2123_);
lean_inc(v_k_2122_);
lean_del_object(v___x_2118_);
lean_dec(v_r_2110_);
v___x_2129_ = lean_nat_add(v___x_2104_, v_size_2106_);
lean_dec(v_size_2106_);
v___x_2130_ = lean_nat_add(v___x_2129_, v_size_2105_);
lean_dec(v___x_2129_);
v___x_2131_ = lean_nat_add(v___x_2104_, v_size_2120_);
if (lean_obj_tag(v_l_2124_) == 0)
{
lean_object* v_size_2132_; 
v_size_2132_ = lean_ctor_get(v_l_2124_, 0);
lean_inc(v_size_2132_);
v___y_2084_ = v___x_2104_;
v___y_2085_ = v_l_2109_;
v___y_2086_ = v___x_2131_;
v___y_2087_ = v_v_2123_;
v___y_2088_ = v_size_2105_;
v___y_2089_ = v_impl_2103_;
v___y_2090_ = v_l_2124_;
v___y_2091_ = v_r_2125_;
v___y_2092_ = v_k_2122_;
v___y_2093_ = v_k_2107_;
v___y_2094_ = v___x_2130_;
v___y_2095_ = v_v_2108_;
v___y_2096_ = v_size_2132_;
goto v___jp_2083_;
}
else
{
lean_object* v___x_2133_; 
v___x_2133_ = lean_unsigned_to_nat(0u);
v___y_2084_ = v___x_2104_;
v___y_2085_ = v_l_2109_;
v___y_2086_ = v___x_2131_;
v___y_2087_ = v_v_2123_;
v___y_2088_ = v_size_2105_;
v___y_2089_ = v_impl_2103_;
v___y_2090_ = v_l_2124_;
v___y_2091_ = v_r_2125_;
v___y_2092_ = v_k_2122_;
v___y_2093_ = v_k_2107_;
v___y_2094_ = v___x_2130_;
v___y_2095_ = v_v_2108_;
v___y_2096_ = v___x_2133_;
goto v___jp_2083_;
}
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
lean_del_object(v___x_2067_);
v___x_2134_ = lean_nat_add(v___x_2104_, v_size_2106_);
lean_dec(v_size_2106_);
v___x_2135_ = lean_nat_add(v___x_2134_, v_size_2105_);
lean_dec(v___x_2134_);
v___x_2136_ = lean_nat_add(v___x_2104_, v_size_2105_);
lean_dec(v_size_2105_);
v___x_2137_ = lean_nat_add(v___x_2136_, v_size_2121_);
lean_dec(v___x_2136_);
lean_inc_ref(v_impl_2103_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 4, v_impl_2103_);
lean_ctor_set(v___x_2118_, 3, v_r_2110_);
lean_ctor_set(v___x_2118_, 2, v_v_2063_);
lean_ctor_set(v___x_2118_, 1, v_k_2062_);
lean_ctor_set(v___x_2118_, 0, v___x_2137_);
v___x_2139_ = v___x_2118_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_k_2062_);
lean_ctor_set(v_reuseFailAlloc_2152_, 2, v_v_2063_);
lean_ctor_set(v_reuseFailAlloc_2152_, 3, v_r_2110_);
lean_ctor_set(v_reuseFailAlloc_2152_, 4, v_impl_2103_);
v___x_2139_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
v_isSharedCheck_2146_ = !lean_is_exclusive(v_impl_2103_);
if (v_isSharedCheck_2146_ == 0)
{
lean_object* v_unused_2147_; lean_object* v_unused_2148_; lean_object* v_unused_2149_; lean_object* v_unused_2150_; lean_object* v_unused_2151_; 
v_unused_2147_ = lean_ctor_get(v_impl_2103_, 4);
lean_dec(v_unused_2147_);
v_unused_2148_ = lean_ctor_get(v_impl_2103_, 3);
lean_dec(v_unused_2148_);
v_unused_2149_ = lean_ctor_get(v_impl_2103_, 2);
lean_dec(v_unused_2149_);
v_unused_2150_ = lean_ctor_get(v_impl_2103_, 1);
lean_dec(v_unused_2150_);
v_unused_2151_ = lean_ctor_get(v_impl_2103_, 0);
lean_dec(v_unused_2151_);
v___x_2141_ = v_impl_2103_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_dec(v_impl_2103_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 4, v___x_2139_);
lean_ctor_set(v___x_2141_, 3, v_l_2109_);
lean_ctor_set(v___x_2141_, 2, v_v_2108_);
lean_ctor_set(v___x_2141_, 1, v_k_2107_);
lean_ctor_set(v___x_2141_, 0, v___x_2135_);
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_k_2107_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v_v_2108_);
lean_ctor_set(v_reuseFailAlloc_2145_, 3, v_l_2109_);
lean_ctor_set(v_reuseFailAlloc_2145_, 4, v___x_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
lean_del_object(v___x_2067_);
v_size_2159_ = lean_ctor_get(v_impl_2103_, 0);
lean_inc(v_size_2159_);
v___x_2160_ = lean_nat_add(v___x_2104_, v_size_2159_);
lean_dec(v_size_2159_);
v___x_2161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
lean_ctor_set(v___x_2161_, 1, v_k_2062_);
lean_ctor_set(v___x_2161_, 2, v_v_2063_);
lean_ctor_set(v___x_2161_, 3, v_l_2064_);
lean_ctor_set(v___x_2161_, 4, v_impl_2103_);
return v___x_2161_;
}
}
else
{
lean_del_object(v___x_2067_);
if (lean_obj_tag(v_l_2064_) == 0)
{
lean_object* v_l_2162_; 
v_l_2162_ = lean_ctor_get(v_l_2064_, 3);
if (lean_obj_tag(v_l_2162_) == 0)
{
lean_object* v_r_2163_; 
lean_inc_ref(v_l_2162_);
v_r_2163_ = lean_ctor_get(v_l_2064_, 4);
lean_inc(v_r_2163_);
if (lean_obj_tag(v_r_2163_) == 0)
{
lean_object* v_size_2164_; lean_object* v_k_2165_; lean_object* v_v_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2188_; 
v_size_2164_ = lean_ctor_get(v_l_2064_, 0);
v_k_2165_ = lean_ctor_get(v_l_2064_, 1);
v_v_2166_ = lean_ctor_get(v_l_2064_, 2);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_l_2064_);
if (v_isSharedCheck_2188_ == 0)
{
lean_object* v_unused_2189_; lean_object* v_unused_2190_; 
v_unused_2189_ = lean_ctor_get(v_l_2064_, 4);
lean_dec(v_unused_2189_);
v_unused_2190_ = lean_ctor_get(v_l_2064_, 3);
lean_dec(v_unused_2190_);
v___x_2168_ = v_l_2064_;
v_isShared_2169_ = v_isSharedCheck_2188_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_v_2166_);
lean_inc(v_k_2165_);
lean_inc(v_size_2164_);
lean_dec(v_l_2064_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2188_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v_size_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2174_; 
v_size_2170_ = lean_ctor_get(v_r_2163_, 0);
v___x_2171_ = lean_nat_add(v___x_2104_, v_size_2164_);
lean_dec(v_size_2164_);
v___x_2172_ = lean_nat_add(v___x_2104_, v_size_2170_);
lean_inc_ref(v_r_2163_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 4, v_impl_2103_);
lean_ctor_set(v___x_2168_, 3, v_r_2163_);
lean_ctor_set(v___x_2168_, 2, v_v_2063_);
lean_ctor_set(v___x_2168_, 1, v_k_2062_);
lean_ctor_set(v___x_2168_, 0, v___x_2172_);
v___x_2174_ = v___x_2168_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_k_2062_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_v_2063_);
lean_ctor_set(v_reuseFailAlloc_2187_, 3, v_r_2163_);
lean_ctor_set(v_reuseFailAlloc_2187_, 4, v_impl_2103_);
v___x_2174_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
v_isSharedCheck_2181_ = !lean_is_exclusive(v_r_2163_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; lean_object* v_unused_2183_; lean_object* v_unused_2184_; lean_object* v_unused_2185_; lean_object* v_unused_2186_; 
v_unused_2182_ = lean_ctor_get(v_r_2163_, 4);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_r_2163_, 3);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_r_2163_, 2);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_r_2163_, 1);
lean_dec(v_unused_2185_);
v_unused_2186_ = lean_ctor_get(v_r_2163_, 0);
lean_dec(v_unused_2186_);
v___x_2176_ = v_r_2163_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_dec(v_r_2163_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 4, v___x_2174_);
lean_ctor_set(v___x_2176_, 3, v_l_2162_);
lean_ctor_set(v___x_2176_, 2, v_v_2166_);
lean_ctor_set(v___x_2176_, 1, v_k_2165_);
lean_ctor_set(v___x_2176_, 0, v___x_2171_);
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_k_2165_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_v_2166_);
lean_ctor_set(v_reuseFailAlloc_2180_, 3, v_l_2162_);
lean_ctor_set(v_reuseFailAlloc_2180_, 4, v___x_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
else
{
lean_object* v_k_2191_; lean_object* v_v_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2201_; 
v_k_2191_ = lean_ctor_get(v_l_2064_, 1);
v_v_2192_ = lean_ctor_get(v_l_2064_, 2);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_l_2064_);
if (v_isSharedCheck_2201_ == 0)
{
lean_object* v_unused_2202_; lean_object* v_unused_2203_; lean_object* v_unused_2204_; 
v_unused_2202_ = lean_ctor_get(v_l_2064_, 4);
lean_dec(v_unused_2202_);
v_unused_2203_ = lean_ctor_get(v_l_2064_, 3);
lean_dec(v_unused_2203_);
v_unused_2204_ = lean_ctor_get(v_l_2064_, 0);
lean_dec(v_unused_2204_);
v___x_2194_ = v_l_2064_;
v_isShared_2195_ = v_isSharedCheck_2201_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_v_2192_);
lean_inc(v_k_2191_);
lean_dec(v_l_2064_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2201_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2196_ = lean_unsigned_to_nat(3u);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 3, v_r_2163_);
lean_ctor_set(v___x_2194_, 2, v_v_2063_);
lean_ctor_set(v___x_2194_, 1, v_k_2062_);
lean_ctor_set(v___x_2194_, 0, v___x_2104_);
v___x_2198_ = v___x_2194_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_k_2062_);
lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_v_2063_);
lean_ctor_set(v_reuseFailAlloc_2200_, 3, v_r_2163_);
lean_ctor_set(v_reuseFailAlloc_2200_, 4, v_r_2163_);
v___x_2198_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; 
v___x_2199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2196_);
lean_ctor_set(v___x_2199_, 1, v_k_2191_);
lean_ctor_set(v___x_2199_, 2, v_v_2192_);
lean_ctor_set(v___x_2199_, 3, v_l_2162_);
lean_ctor_set(v___x_2199_, 4, v___x_2198_);
return v___x_2199_;
}
}
}
}
else
{
lean_object* v_r_2205_; 
v_r_2205_ = lean_ctor_get(v_l_2064_, 4);
lean_inc(v_r_2205_);
if (lean_obj_tag(v_r_2205_) == 0)
{
lean_object* v_k_2206_; lean_object* v_v_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2228_; 
lean_inc(v_l_2162_);
v_k_2206_ = lean_ctor_get(v_l_2064_, 1);
v_v_2207_ = lean_ctor_get(v_l_2064_, 2);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_l_2064_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; lean_object* v_unused_2230_; lean_object* v_unused_2231_; 
v_unused_2229_ = lean_ctor_get(v_l_2064_, 4);
lean_dec(v_unused_2229_);
v_unused_2230_ = lean_ctor_get(v_l_2064_, 3);
lean_dec(v_unused_2230_);
v_unused_2231_ = lean_ctor_get(v_l_2064_, 0);
lean_dec(v_unused_2231_);
v___x_2209_ = v_l_2064_;
v_isShared_2210_ = v_isSharedCheck_2228_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_v_2207_);
lean_inc(v_k_2206_);
lean_dec(v_l_2064_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2228_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v_k_2211_; lean_object* v_v_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2224_; 
v_k_2211_ = lean_ctor_get(v_r_2205_, 1);
v_v_2212_ = lean_ctor_get(v_r_2205_, 2);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_r_2205_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; lean_object* v_unused_2226_; lean_object* v_unused_2227_; 
v_unused_2225_ = lean_ctor_get(v_r_2205_, 4);
lean_dec(v_unused_2225_);
v_unused_2226_ = lean_ctor_get(v_r_2205_, 3);
lean_dec(v_unused_2226_);
v_unused_2227_ = lean_ctor_get(v_r_2205_, 0);
lean_dec(v_unused_2227_);
v___x_2214_ = v_r_2205_;
v_isShared_2215_ = v_isSharedCheck_2224_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_v_2212_);
lean_inc(v_k_2211_);
lean_dec(v_r_2205_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2224_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2216_ = lean_unsigned_to_nat(3u);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 4, v_l_2162_);
lean_ctor_set(v___x_2214_, 3, v_l_2162_);
lean_ctor_set(v___x_2214_, 2, v_v_2207_);
lean_ctor_set(v___x_2214_, 1, v_k_2206_);
lean_ctor_set(v___x_2214_, 0, v___x_2104_);
v___x_2218_ = v___x_2214_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_k_2206_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_v_2207_);
lean_ctor_set(v_reuseFailAlloc_2223_, 3, v_l_2162_);
lean_ctor_set(v_reuseFailAlloc_2223_, 4, v_l_2162_);
v___x_2218_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2220_; 
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 4, v_l_2162_);
lean_ctor_set(v___x_2209_, 2, v_v_2063_);
lean_ctor_set(v___x_2209_, 1, v_k_2062_);
lean_ctor_set(v___x_2209_, 0, v___x_2104_);
v___x_2220_ = v___x_2209_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_k_2062_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_v_2063_);
lean_ctor_set(v_reuseFailAlloc_2222_, 3, v_l_2162_);
lean_ctor_set(v_reuseFailAlloc_2222_, 4, v_l_2162_);
v___x_2220_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; 
v___x_2221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2216_);
lean_ctor_set(v___x_2221_, 1, v_k_2211_);
lean_ctor_set(v___x_2221_, 2, v_v_2212_);
lean_ctor_set(v___x_2221_, 3, v___x_2218_);
lean_ctor_set(v___x_2221_, 4, v___x_2220_);
return v___x_2221_;
}
}
}
}
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = lean_unsigned_to_nat(2u);
v___x_2233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
lean_ctor_set(v___x_2233_, 1, v_k_2062_);
lean_ctor_set(v___x_2233_, 2, v_v_2063_);
lean_ctor_set(v___x_2233_, 3, v_l_2064_);
lean_ctor_set(v___x_2233_, 4, v_r_2205_);
return v___x_2233_;
}
}
}
else
{
lean_object* v___x_2234_; 
v___x_2234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2104_);
lean_ctor_set(v___x_2234_, 1, v_k_2062_);
lean_ctor_set(v___x_2234_, 2, v_v_2063_);
lean_ctor_set(v___x_2234_, 3, v_l_2064_);
lean_ctor_set(v___x_2234_, 4, v_l_2064_);
return v___x_2234_;
}
}
}
v___jp_2235_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = lean_nat_add(v___y_2242_, v___y_2248_);
lean_dec(v___y_2248_);
lean_dec(v___y_2242_);
v___x_2250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
lean_ctor_set(v___x_2250_, 1, v_k_2062_);
lean_ctor_set(v___x_2250_, 2, v_v_2063_);
lean_ctor_set(v___x_2250_, 3, v___y_2245_);
lean_ctor_set(v___x_2250_, 4, v___y_2246_);
v___x_2251_ = lean_nat_add(v___y_2239_, v___y_2237_);
lean_dec(v___y_2237_);
if (lean_obj_tag(v___y_2241_) == 0)
{
lean_object* v_size_2252_; 
v_size_2252_ = lean_ctor_get(v___y_2241_, 0);
lean_inc(v_size_2252_);
v___y_2049_ = v___y_2236_;
v___y_2050_ = v___y_2238_;
v___y_2051_ = v___y_2240_;
v___y_2052_ = v___y_2241_;
v___y_2053_ = v___y_2243_;
v___y_2054_ = v___y_2244_;
v___y_2055_ = v___x_2250_;
v___y_2056_ = v___x_2251_;
v___y_2057_ = v___y_2247_;
v___y_2058_ = v_size_2252_;
goto v___jp_2048_;
}
else
{
lean_object* v___x_2253_; 
v___x_2253_ = lean_unsigned_to_nat(0u);
v___y_2049_ = v___y_2236_;
v___y_2050_ = v___y_2238_;
v___y_2051_ = v___y_2240_;
v___y_2052_ = v___y_2241_;
v___y_2053_ = v___y_2243_;
v___y_2054_ = v___y_2244_;
v___y_2055_ = v___x_2250_;
v___y_2056_ = v___x_2251_;
v___y_2057_ = v___y_2247_;
v___y_2058_ = v___x_2253_;
goto v___jp_2048_;
}
}
v___jp_2254_:
{
lean_object* v_impl_2255_; lean_object* v___x_2256_; 
v_impl_2255_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v_k_2046_, v_l_2064_);
v___x_2256_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2255_) == 0)
{
if (lean_obj_tag(v_r_2065_) == 0)
{
lean_object* v_size_2257_; lean_object* v_size_2258_; lean_object* v_k_2259_; lean_object* v_v_2260_; lean_object* v_l_2261_; lean_object* v_r_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; 
v_size_2257_ = lean_ctor_get(v_impl_2255_, 0);
lean_inc(v_size_2257_);
v_size_2258_ = lean_ctor_get(v_r_2065_, 0);
v_k_2259_ = lean_ctor_get(v_r_2065_, 1);
v_v_2260_ = lean_ctor_get(v_r_2065_, 2);
v_l_2261_ = lean_ctor_get(v_r_2065_, 3);
v_r_2262_ = lean_ctor_get(v_r_2065_, 4);
v___x_2263_ = lean_unsigned_to_nat(3u);
v___x_2264_ = lean_nat_mul(v___x_2263_, v_size_2257_);
v___x_2265_ = lean_nat_dec_lt(v___x_2264_, v_size_2258_);
lean_dec(v___x_2264_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2266_ = lean_nat_add(v___x_2256_, v_size_2257_);
lean_dec(v_size_2257_);
v___x_2267_ = lean_nat_add(v___x_2266_, v_size_2258_);
lean_dec(v___x_2266_);
v___x_2268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
lean_ctor_set(v___x_2268_, 1, v_k_2062_);
lean_ctor_set(v___x_2268_, 2, v_v_2063_);
lean_ctor_set(v___x_2268_, 3, v_impl_2255_);
lean_ctor_set(v___x_2268_, 4, v_r_2065_);
return v___x_2268_;
}
else
{
lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2303_; 
lean_inc(v_r_2262_);
lean_inc(v_l_2261_);
lean_inc(v_v_2260_);
lean_inc(v_k_2259_);
lean_inc(v_size_2258_);
v_isSharedCheck_2303_ = !lean_is_exclusive(v_r_2065_);
if (v_isSharedCheck_2303_ == 0)
{
lean_object* v_unused_2304_; lean_object* v_unused_2305_; lean_object* v_unused_2306_; lean_object* v_unused_2307_; lean_object* v_unused_2308_; 
v_unused_2304_ = lean_ctor_get(v_r_2065_, 4);
lean_dec(v_unused_2304_);
v_unused_2305_ = lean_ctor_get(v_r_2065_, 3);
lean_dec(v_unused_2305_);
v_unused_2306_ = lean_ctor_get(v_r_2065_, 2);
lean_dec(v_unused_2306_);
v_unused_2307_ = lean_ctor_get(v_r_2065_, 1);
lean_dec(v_unused_2307_);
v_unused_2308_ = lean_ctor_get(v_r_2065_, 0);
lean_dec(v_unused_2308_);
v___x_2270_ = v_r_2065_;
v_isShared_2271_ = v_isSharedCheck_2303_;
goto v_resetjp_2269_;
}
else
{
lean_dec(v_r_2065_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2303_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v_size_2272_; lean_object* v_k_2273_; lean_object* v_v_2274_; lean_object* v_l_2275_; lean_object* v_r_2276_; lean_object* v_size_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
v_size_2272_ = lean_ctor_get(v_l_2261_, 0);
v_k_2273_ = lean_ctor_get(v_l_2261_, 1);
v_v_2274_ = lean_ctor_get(v_l_2261_, 2);
v_l_2275_ = lean_ctor_get(v_l_2261_, 3);
v_r_2276_ = lean_ctor_get(v_l_2261_, 4);
v_size_2277_ = lean_ctor_get(v_r_2262_, 0);
v___x_2278_ = lean_unsigned_to_nat(2u);
v___x_2279_ = lean_nat_mul(v___x_2278_, v_size_2277_);
v___x_2280_ = lean_nat_dec_lt(v_size_2272_, v___x_2279_);
lean_dec(v___x_2279_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
lean_inc(v_size_2277_);
lean_inc(v_r_2276_);
lean_inc(v_l_2275_);
lean_inc(v_v_2274_);
lean_inc(v_k_2273_);
lean_del_object(v___x_2270_);
lean_dec(v_l_2261_);
v___x_2281_ = lean_nat_add(v___x_2256_, v_size_2257_);
lean_dec(v_size_2257_);
v___x_2282_ = lean_nat_add(v___x_2281_, v_size_2258_);
lean_dec(v_size_2258_);
if (lean_obj_tag(v_l_2275_) == 0)
{
lean_object* v_size_2283_; 
v_size_2283_ = lean_ctor_get(v_l_2275_, 0);
lean_inc(v_size_2283_);
v___y_2236_ = v_k_2273_;
v___y_2237_ = v_size_2277_;
v___y_2238_ = v___x_2282_;
v___y_2239_ = v___x_2256_;
v___y_2240_ = v_v_2260_;
v___y_2241_ = v_r_2276_;
v___y_2242_ = v___x_2281_;
v___y_2243_ = v_v_2274_;
v___y_2244_ = v_k_2259_;
v___y_2245_ = v_impl_2255_;
v___y_2246_ = v_l_2275_;
v___y_2247_ = v_r_2262_;
v___y_2248_ = v_size_2283_;
goto v___jp_2235_;
}
else
{
lean_object* v___x_2284_; 
v___x_2284_ = lean_unsigned_to_nat(0u);
v___y_2236_ = v_k_2273_;
v___y_2237_ = v_size_2277_;
v___y_2238_ = v___x_2282_;
v___y_2239_ = v___x_2256_;
v___y_2240_ = v_v_2260_;
v___y_2241_ = v_r_2276_;
v___y_2242_ = v___x_2281_;
v___y_2243_ = v_v_2274_;
v___y_2244_ = v_k_2259_;
v___y_2245_ = v_impl_2255_;
v___y_2246_ = v_l_2275_;
v___y_2247_ = v_r_2262_;
v___y_2248_ = v___x_2284_;
goto v___jp_2235_;
}
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2285_ = lean_nat_add(v___x_2256_, v_size_2257_);
lean_dec(v_size_2257_);
v___x_2286_ = lean_nat_add(v___x_2285_, v_size_2258_);
lean_dec(v_size_2258_);
v___x_2287_ = lean_nat_add(v___x_2285_, v_size_2272_);
lean_dec(v___x_2285_);
lean_inc_ref(v_impl_2255_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 4, v_l_2261_);
lean_ctor_set(v___x_2270_, 3, v_impl_2255_);
lean_ctor_set(v___x_2270_, 2, v_v_2063_);
lean_ctor_set(v___x_2270_, 1, v_k_2062_);
lean_ctor_set(v___x_2270_, 0, v___x_2287_);
v___x_2289_ = v___x_2270_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2302_, 1, v_k_2062_);
lean_ctor_set(v_reuseFailAlloc_2302_, 2, v_v_2063_);
lean_ctor_set(v_reuseFailAlloc_2302_, 3, v_impl_2255_);
lean_ctor_set(v_reuseFailAlloc_2302_, 4, v_l_2261_);
v___x_2289_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
v_isSharedCheck_2296_ = !lean_is_exclusive(v_impl_2255_);
if (v_isSharedCheck_2296_ == 0)
{
lean_object* v_unused_2297_; lean_object* v_unused_2298_; lean_object* v_unused_2299_; lean_object* v_unused_2300_; lean_object* v_unused_2301_; 
v_unused_2297_ = lean_ctor_get(v_impl_2255_, 4);
lean_dec(v_unused_2297_);
v_unused_2298_ = lean_ctor_get(v_impl_2255_, 3);
lean_dec(v_unused_2298_);
v_unused_2299_ = lean_ctor_get(v_impl_2255_, 2);
lean_dec(v_unused_2299_);
v_unused_2300_ = lean_ctor_get(v_impl_2255_, 1);
lean_dec(v_unused_2300_);
v_unused_2301_ = lean_ctor_get(v_impl_2255_, 0);
lean_dec(v_unused_2301_);
v___x_2291_ = v_impl_2255_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_dec(v_impl_2255_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 4, v_r_2262_);
lean_ctor_set(v___x_2291_, 3, v___x_2289_);
lean_ctor_set(v___x_2291_, 2, v_v_2260_);
lean_ctor_set(v___x_2291_, 1, v_k_2259_);
lean_ctor_set(v___x_2291_, 0, v___x_2286_);
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2295_, 1, v_k_2259_);
lean_ctor_set(v_reuseFailAlloc_2295_, 2, v_v_2260_);
lean_ctor_set(v_reuseFailAlloc_2295_, 3, v___x_2289_);
lean_ctor_set(v_reuseFailAlloc_2295_, 4, v_r_2262_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v_size_2309_ = lean_ctor_get(v_impl_2255_, 0);
lean_inc(v_size_2309_);
v___x_2310_ = lean_nat_add(v___x_2256_, v_size_2309_);
lean_dec(v_size_2309_);
v___x_2311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
lean_ctor_set(v___x_2311_, 1, v_k_2062_);
lean_ctor_set(v___x_2311_, 2, v_v_2063_);
lean_ctor_set(v___x_2311_, 3, v_impl_2255_);
lean_ctor_set(v___x_2311_, 4, v_r_2065_);
return v___x_2311_;
}
}
else
{
if (lean_obj_tag(v_r_2065_) == 0)
{
lean_object* v_l_2312_; 
v_l_2312_ = lean_ctor_get(v_r_2065_, 3);
lean_inc(v_l_2312_);
if (lean_obj_tag(v_l_2312_) == 0)
{
lean_object* v_r_2313_; 
v_r_2313_ = lean_ctor_get(v_r_2065_, 4);
lean_inc(v_r_2313_);
if (lean_obj_tag(v_r_2313_) == 0)
{
lean_object* v_size_2314_; lean_object* v_k_2315_; lean_object* v_v_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2327_; 
v_size_2314_ = lean_ctor_get(v_r_2065_, 0);
v_k_2315_ = lean_ctor_get(v_r_2065_, 1);
v_v_2316_ = lean_ctor_get(v_r_2065_, 2);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_r_2065_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; lean_object* v_unused_2329_; 
v_unused_2328_ = lean_ctor_get(v_r_2065_, 4);
lean_dec(v_unused_2328_);
v_unused_2329_ = lean_ctor_get(v_r_2065_, 3);
lean_dec(v_unused_2329_);
v___x_2318_ = v_r_2065_;
v_isShared_2319_ = v_isSharedCheck_2327_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_v_2316_);
lean_inc(v_k_2315_);
lean_inc(v_size_2314_);
lean_dec(v_r_2065_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2327_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v_size_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2324_; 
v_size_2320_ = lean_ctor_get(v_l_2312_, 0);
v___x_2321_ = lean_nat_add(v___x_2256_, v_size_2314_);
lean_dec(v_size_2314_);
v___x_2322_ = lean_nat_add(v___x_2256_, v_size_2320_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 4, v_l_2312_);
lean_ctor_set(v___x_2318_, 3, v_impl_2255_);
lean_ctor_set(v___x_2318_, 2, v_v_2063_);
lean_ctor_set(v___x_2318_, 1, v_k_2062_);
lean_ctor_set(v___x_2318_, 0, v___x_2322_);
v___x_2324_ = v___x_2318_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2322_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_k_2062_);
lean_ctor_set(v_reuseFailAlloc_2326_, 2, v_v_2063_);
lean_ctor_set(v_reuseFailAlloc_2326_, 3, v_impl_2255_);
lean_ctor_set(v_reuseFailAlloc_2326_, 4, v_l_2312_);
v___x_2324_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2325_; 
v___x_2325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2321_);
lean_ctor_set(v___x_2325_, 1, v_k_2315_);
lean_ctor_set(v___x_2325_, 2, v_v_2316_);
lean_ctor_set(v___x_2325_, 3, v___x_2324_);
lean_ctor_set(v___x_2325_, 4, v_r_2313_);
return v___x_2325_;
}
}
}
else
{
lean_object* v_k_2330_; lean_object* v_v_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2352_; 
v_k_2330_ = lean_ctor_get(v_r_2065_, 1);
v_v_2331_ = lean_ctor_get(v_r_2065_, 2);
v_isSharedCheck_2352_ = !lean_is_exclusive(v_r_2065_);
if (v_isSharedCheck_2352_ == 0)
{
lean_object* v_unused_2353_; lean_object* v_unused_2354_; lean_object* v_unused_2355_; 
v_unused_2353_ = lean_ctor_get(v_r_2065_, 4);
lean_dec(v_unused_2353_);
v_unused_2354_ = lean_ctor_get(v_r_2065_, 3);
lean_dec(v_unused_2354_);
v_unused_2355_ = lean_ctor_get(v_r_2065_, 0);
lean_dec(v_unused_2355_);
v___x_2333_ = v_r_2065_;
v_isShared_2334_ = v_isSharedCheck_2352_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_v_2331_);
lean_inc(v_k_2330_);
lean_dec(v_r_2065_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2352_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v_k_2335_; lean_object* v_v_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2348_; 
v_k_2335_ = lean_ctor_get(v_l_2312_, 1);
v_v_2336_ = lean_ctor_get(v_l_2312_, 2);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_l_2312_);
if (v_isSharedCheck_2348_ == 0)
{
lean_object* v_unused_2349_; lean_object* v_unused_2350_; lean_object* v_unused_2351_; 
v_unused_2349_ = lean_ctor_get(v_l_2312_, 4);
lean_dec(v_unused_2349_);
v_unused_2350_ = lean_ctor_get(v_l_2312_, 3);
lean_dec(v_unused_2350_);
v_unused_2351_ = lean_ctor_get(v_l_2312_, 0);
lean_dec(v_unused_2351_);
v___x_2338_ = v_l_2312_;
v_isShared_2339_ = v_isSharedCheck_2348_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_v_2336_);
lean_inc(v_k_2335_);
lean_dec(v_l_2312_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2348_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2340_ = lean_unsigned_to_nat(3u);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 4, v_r_2313_);
lean_ctor_set(v___x_2338_, 3, v_r_2313_);
lean_ctor_set(v___x_2338_, 2, v_v_2063_);
lean_ctor_set(v___x_2338_, 1, v_k_2062_);
lean_ctor_set(v___x_2338_, 0, v___x_2256_);
v___x_2342_ = v___x_2338_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_k_2062_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_v_2063_);
lean_ctor_set(v_reuseFailAlloc_2347_, 3, v_r_2313_);
lean_ctor_set(v_reuseFailAlloc_2347_, 4, v_r_2313_);
v___x_2342_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
lean_object* v___x_2344_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 3, v_r_2313_);
lean_ctor_set(v___x_2333_, 0, v___x_2256_);
v___x_2344_ = v___x_2333_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_k_2330_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_v_2331_);
lean_ctor_set(v_reuseFailAlloc_2346_, 3, v_r_2313_);
lean_ctor_set(v_reuseFailAlloc_2346_, 4, v_r_2313_);
v___x_2344_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2345_; 
v___x_2345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2340_);
lean_ctor_set(v___x_2345_, 1, v_k_2335_);
lean_ctor_set(v___x_2345_, 2, v_v_2336_);
lean_ctor_set(v___x_2345_, 3, v___x_2342_);
lean_ctor_set(v___x_2345_, 4, v___x_2344_);
return v___x_2345_;
}
}
}
}
}
}
else
{
lean_object* v_r_2356_; 
v_r_2356_ = lean_ctor_get(v_r_2065_, 4);
lean_inc(v_r_2356_);
if (lean_obj_tag(v_r_2356_) == 0)
{
lean_object* v_k_2357_; lean_object* v_v_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2367_; 
v_k_2357_ = lean_ctor_get(v_r_2065_, 1);
v_v_2358_ = lean_ctor_get(v_r_2065_, 2);
v_isSharedCheck_2367_ = !lean_is_exclusive(v_r_2065_);
if (v_isSharedCheck_2367_ == 0)
{
lean_object* v_unused_2368_; lean_object* v_unused_2369_; lean_object* v_unused_2370_; 
v_unused_2368_ = lean_ctor_get(v_r_2065_, 4);
lean_dec(v_unused_2368_);
v_unused_2369_ = lean_ctor_get(v_r_2065_, 3);
lean_dec(v_unused_2369_);
v_unused_2370_ = lean_ctor_get(v_r_2065_, 0);
lean_dec(v_unused_2370_);
v___x_2360_ = v_r_2065_;
v_isShared_2361_ = v_isSharedCheck_2367_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_v_2358_);
lean_inc(v_k_2357_);
lean_dec(v_r_2065_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2367_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2364_; 
v___x_2362_ = lean_unsigned_to_nat(3u);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 4, v_l_2312_);
lean_ctor_set(v___x_2360_, 2, v_v_2063_);
lean_ctor_set(v___x_2360_, 1, v_k_2062_);
lean_ctor_set(v___x_2360_, 0, v___x_2256_);
v___x_2364_ = v___x_2360_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_k_2062_);
lean_ctor_set(v_reuseFailAlloc_2366_, 2, v_v_2063_);
lean_ctor_set(v_reuseFailAlloc_2366_, 3, v_l_2312_);
lean_ctor_set(v_reuseFailAlloc_2366_, 4, v_l_2312_);
v___x_2364_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2365_; 
v___x_2365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2362_);
lean_ctor_set(v___x_2365_, 1, v_k_2357_);
lean_ctor_set(v___x_2365_, 2, v_v_2358_);
lean_ctor_set(v___x_2365_, 3, v___x_2364_);
lean_ctor_set(v___x_2365_, 4, v_r_2356_);
return v___x_2365_;
}
}
}
else
{
lean_object* v_size_2371_; lean_object* v_k_2372_; lean_object* v_v_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2382_; 
v_size_2371_ = lean_ctor_get(v_r_2065_, 0);
v_k_2372_ = lean_ctor_get(v_r_2065_, 1);
v_v_2373_ = lean_ctor_get(v_r_2065_, 2);
v_isSharedCheck_2382_ = !lean_is_exclusive(v_r_2065_);
if (v_isSharedCheck_2382_ == 0)
{
lean_object* v_unused_2383_; lean_object* v_unused_2384_; 
v_unused_2383_ = lean_ctor_get(v_r_2065_, 4);
lean_dec(v_unused_2383_);
v_unused_2384_ = lean_ctor_get(v_r_2065_, 3);
lean_dec(v_unused_2384_);
v___x_2375_ = v_r_2065_;
v_isShared_2376_ = v_isSharedCheck_2382_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_v_2373_);
lean_inc(v_k_2372_);
lean_inc(v_size_2371_);
lean_dec(v_r_2065_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2382_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 3, v_r_2356_);
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_size_2371_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v_k_2372_);
lean_ctor_set(v_reuseFailAlloc_2381_, 2, v_v_2373_);
lean_ctor_set(v_reuseFailAlloc_2381_, 3, v_r_2356_);
lean_ctor_set(v_reuseFailAlloc_2381_, 4, v_r_2356_);
v___x_2378_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_unsigned_to_nat(2u);
v___x_2380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
lean_ctor_set(v___x_2380_, 1, v_k_2062_);
lean_ctor_set(v___x_2380_, 2, v_v_2063_);
lean_ctor_set(v___x_2380_, 3, v_r_2356_);
lean_ctor_set(v___x_2380_, 4, v___x_2378_);
return v___x_2380_;
}
}
}
}
}
else
{
lean_object* v___x_2385_; 
v___x_2385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2256_);
lean_ctor_set(v___x_2385_, 1, v_k_2062_);
lean_ctor_set(v___x_2385_, 2, v_v_2063_);
lean_ctor_set(v___x_2385_, 3, v_r_2065_);
lean_ctor_set(v___x_2385_, 4, v_r_2065_);
return v___x_2385_;
}
}
}
}
}
else
{
return v_t_2047_;
}
v___jp_2048_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2059_ = lean_nat_add(v___y_2056_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec(v___y_2056_);
v___x_2060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
lean_ctor_set(v___x_2060_, 1, v___y_2054_);
lean_ctor_set(v___x_2060_, 2, v___y_2051_);
lean_ctor_set(v___x_2060_, 3, v___y_2052_);
lean_ctor_set(v___x_2060_, 4, v___y_2057_);
v___x_2061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2061_, 0, v___y_2050_);
lean_ctor_set(v___x_2061_, 1, v___y_2049_);
lean_ctor_set(v___x_2061_, 2, v___y_2053_);
lean_ctor_set(v___x_2061_, 3, v___y_2055_);
lean_ctor_set(v___x_2061_, 4, v___x_2060_);
return v___x_2061_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg___boxed(lean_object* v_k_2710_, lean_object* v_t_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v_k_2710_, v_t_2711_);
lean_dec_ref(v_k_2710_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(lean_object* v_k_2713_, lean_object* v_v_2714_, lean_object* v_t_2715_){
_start:
{
lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; 
if (lean_obj_tag(v_t_2715_) == 0)
{
lean_object* v_size_2730_; lean_object* v_k_2731_; lean_object* v_v_2732_; lean_object* v_l_2733_; lean_object* v_r_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2999_; 
v_size_2730_ = lean_ctor_get(v_t_2715_, 0);
v_k_2731_ = lean_ctor_get(v_t_2715_, 1);
v_v_2732_ = lean_ctor_get(v_t_2715_, 2);
v_l_2733_ = lean_ctor_get(v_t_2715_, 3);
v_r_2734_ = lean_ctor_get(v_t_2715_, 4);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_t_2715_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2736_ = v_t_2715_;
v_isShared_2737_ = v_isSharedCheck_2999_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_r_2734_);
lean_inc(v_l_2733_);
lean_inc(v_v_2732_);
lean_inc(v_k_2731_);
lean_inc(v_size_2730_);
lean_dec(v_t_2715_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2999_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v_fst_2987_; lean_object* v_snd_2988_; lean_object* v_fst_2989_; lean_object* v_snd_2990_; double v___x_2991_; double v___x_2992_; uint8_t v___x_2993_; 
v_fst_2987_ = lean_ctor_get(v_k_2713_, 0);
v_snd_2988_ = lean_ctor_get(v_k_2713_, 1);
v_fst_2989_ = lean_ctor_get(v_k_2731_, 0);
v_snd_2990_ = lean_ctor_get(v_k_2731_, 1);
v___x_2991_ = lean_unbox_float(v_fst_2987_);
v___x_2992_ = lean_unbox_float(v_fst_2989_);
v___x_2993_ = lean_float_decLt(v___x_2991_, v___x_2992_);
if (v___x_2993_ == 0)
{
double v___x_2994_; double v___x_2995_; uint8_t v___x_2996_; 
v___x_2994_ = lean_unbox_float(v_fst_2989_);
v___x_2995_ = lean_unbox_float(v_fst_2987_);
v___x_2996_ = lean_float_decLt(v___x_2994_, v___x_2995_);
if (v___x_2996_ == 0)
{
uint8_t v___x_2997_; 
v___x_2997_ = l_Lean_Name_cmp(v_snd_2988_, v_snd_2990_);
switch(v___x_2997_)
{
case 0:
{
lean_del_object(v___x_2736_);
lean_dec(v_size_2730_);
goto v___jp_2886_;
}
case 1:
{
lean_object* v___x_2998_; 
lean_del_object(v___x_2736_);
lean_dec(v_v_2732_);
lean_dec(v_k_2731_);
v___x_2998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2998_, 0, v_size_2730_);
lean_ctor_set(v___x_2998_, 1, v_k_2713_);
lean_ctor_set(v___x_2998_, 2, v_v_2714_);
lean_ctor_set(v___x_2998_, 3, v_l_2733_);
lean_ctor_set(v___x_2998_, 4, v_r_2734_);
return v___x_2998_;
}
default: 
{
lean_dec(v_size_2730_);
goto v___jp_2758_;
}
}
}
else
{
lean_dec(v_size_2730_);
goto v___jp_2758_;
}
}
else
{
lean_del_object(v___x_2736_);
lean_dec(v_size_2730_);
goto v___jp_2886_;
}
v___jp_2738_:
{
lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2751_ = lean_nat_add(v___y_2742_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec(v___y_2742_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 4, v___y_2741_);
lean_ctor_set(v___x_2736_, 0, v___x_2751_);
v___x_2753_ = v___x_2736_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2751_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2757_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2757_, 3, v_l_2733_);
lean_ctor_set(v_reuseFailAlloc_2757_, 4, v___y_2741_);
v___x_2753_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___x_2754_; 
v___x_2754_ = lean_nat_add(v___y_2748_, v___y_2745_);
lean_dec(v___y_2745_);
if (lean_obj_tag(v___y_2739_) == 0)
{
lean_object* v_size_2755_; 
v_size_2755_ = lean_ctor_get(v___y_2739_, 0);
lean_inc(v_size_2755_);
v___y_2717_ = v___x_2754_;
v___y_2718_ = v___y_2740_;
v___y_2719_ = v___y_2739_;
v___y_2720_ = v___x_2753_;
v___y_2721_ = v___y_2743_;
v___y_2722_ = v___y_2744_;
v___y_2723_ = v___y_2747_;
v___y_2724_ = v___y_2746_;
v___y_2725_ = v___y_2749_;
v___y_2726_ = v_size_2755_;
goto v___jp_2716_;
}
else
{
lean_object* v___x_2756_; 
v___x_2756_ = lean_unsigned_to_nat(0u);
v___y_2717_ = v___x_2754_;
v___y_2718_ = v___y_2740_;
v___y_2719_ = v___y_2739_;
v___y_2720_ = v___x_2753_;
v___y_2721_ = v___y_2743_;
v___y_2722_ = v___y_2744_;
v___y_2723_ = v___y_2747_;
v___y_2724_ = v___y_2746_;
v___y_2725_ = v___y_2749_;
v___y_2726_ = v___x_2756_;
goto v___jp_2716_;
}
}
}
v___jp_2758_:
{
lean_object* v_impl_2759_; lean_object* v___x_2760_; 
v_impl_2759_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(v_k_2713_, v_v_2714_, v_r_2734_);
v___x_2760_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2733_) == 0)
{
lean_object* v_size_2761_; lean_object* v_size_2762_; lean_object* v_k_2763_; lean_object* v_v_2764_; lean_object* v_l_2765_; lean_object* v_r_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; uint8_t v___x_2769_; 
v_size_2761_ = lean_ctor_get(v_l_2733_, 0);
v_size_2762_ = lean_ctor_get(v_impl_2759_, 0);
lean_inc(v_size_2762_);
v_k_2763_ = lean_ctor_get(v_impl_2759_, 1);
lean_inc(v_k_2763_);
v_v_2764_ = lean_ctor_get(v_impl_2759_, 2);
lean_inc(v_v_2764_);
v_l_2765_ = lean_ctor_get(v_impl_2759_, 3);
lean_inc(v_l_2765_);
v_r_2766_ = lean_ctor_get(v_impl_2759_, 4);
lean_inc(v_r_2766_);
v___x_2767_ = lean_unsigned_to_nat(3u);
v___x_2768_ = lean_nat_mul(v___x_2767_, v_size_2761_);
v___x_2769_ = lean_nat_dec_lt(v___x_2768_, v_size_2762_);
lean_dec(v___x_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
lean_dec(v_r_2766_);
lean_dec(v_l_2765_);
lean_dec(v_v_2764_);
lean_dec(v_k_2763_);
lean_del_object(v___x_2736_);
v___x_2770_ = lean_nat_add(v___x_2760_, v_size_2761_);
v___x_2771_ = lean_nat_add(v___x_2770_, v_size_2762_);
lean_dec(v_size_2762_);
lean_dec(v___x_2770_);
v___x_2772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
lean_ctor_set(v___x_2772_, 1, v_k_2731_);
lean_ctor_set(v___x_2772_, 2, v_v_2732_);
lean_ctor_set(v___x_2772_, 3, v_l_2733_);
lean_ctor_set(v___x_2772_, 4, v_impl_2759_);
return v___x_2772_;
}
else
{
lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2807_; 
v_isSharedCheck_2807_ = !lean_is_exclusive(v_impl_2759_);
if (v_isSharedCheck_2807_ == 0)
{
lean_object* v_unused_2808_; lean_object* v_unused_2809_; lean_object* v_unused_2810_; lean_object* v_unused_2811_; lean_object* v_unused_2812_; 
v_unused_2808_ = lean_ctor_get(v_impl_2759_, 4);
lean_dec(v_unused_2808_);
v_unused_2809_ = lean_ctor_get(v_impl_2759_, 3);
lean_dec(v_unused_2809_);
v_unused_2810_ = lean_ctor_get(v_impl_2759_, 2);
lean_dec(v_unused_2810_);
v_unused_2811_ = lean_ctor_get(v_impl_2759_, 1);
lean_dec(v_unused_2811_);
v_unused_2812_ = lean_ctor_get(v_impl_2759_, 0);
lean_dec(v_unused_2812_);
v___x_2774_ = v_impl_2759_;
v_isShared_2775_ = v_isSharedCheck_2807_;
goto v_resetjp_2773_;
}
else
{
lean_dec(v_impl_2759_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2807_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v_size_2776_; lean_object* v_k_2777_; lean_object* v_v_2778_; lean_object* v_l_2779_; lean_object* v_r_2780_; lean_object* v_size_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v_size_2776_ = lean_ctor_get(v_l_2765_, 0);
v_k_2777_ = lean_ctor_get(v_l_2765_, 1);
v_v_2778_ = lean_ctor_get(v_l_2765_, 2);
v_l_2779_ = lean_ctor_get(v_l_2765_, 3);
v_r_2780_ = lean_ctor_get(v_l_2765_, 4);
v_size_2781_ = lean_ctor_get(v_r_2766_, 0);
v___x_2782_ = lean_unsigned_to_nat(2u);
v___x_2783_ = lean_nat_mul(v___x_2782_, v_size_2781_);
v___x_2784_ = lean_nat_dec_lt(v_size_2776_, v___x_2783_);
lean_dec(v___x_2783_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_inc(v_size_2781_);
lean_inc(v_r_2780_);
lean_inc(v_l_2779_);
lean_inc(v_v_2778_);
lean_inc(v_k_2777_);
lean_del_object(v___x_2774_);
lean_dec(v_l_2765_);
v___x_2785_ = lean_nat_add(v___x_2760_, v_size_2761_);
v___x_2786_ = lean_nat_add(v___x_2785_, v_size_2762_);
lean_dec(v_size_2762_);
if (lean_obj_tag(v_l_2779_) == 0)
{
lean_object* v_size_2787_; 
v_size_2787_ = lean_ctor_get(v_l_2779_, 0);
lean_inc(v_size_2787_);
v___y_2739_ = v_r_2780_;
v___y_2740_ = v_k_2777_;
v___y_2741_ = v_l_2779_;
v___y_2742_ = v___x_2785_;
v___y_2743_ = v_k_2763_;
v___y_2744_ = v_r_2766_;
v___y_2745_ = v_size_2781_;
v___y_2746_ = v___x_2786_;
v___y_2747_ = v_v_2778_;
v___y_2748_ = v___x_2760_;
v___y_2749_ = v_v_2764_;
v___y_2750_ = v_size_2787_;
goto v___jp_2738_;
}
else
{
lean_object* v___x_2788_; 
v___x_2788_ = lean_unsigned_to_nat(0u);
v___y_2739_ = v_r_2780_;
v___y_2740_ = v_k_2777_;
v___y_2741_ = v_l_2779_;
v___y_2742_ = v___x_2785_;
v___y_2743_ = v_k_2763_;
v___y_2744_ = v_r_2766_;
v___y_2745_ = v_size_2781_;
v___y_2746_ = v___x_2786_;
v___y_2747_ = v_v_2778_;
v___y_2748_ = v___x_2760_;
v___y_2749_ = v_v_2764_;
v___y_2750_ = v___x_2788_;
goto v___jp_2738_;
}
}
else
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2793_; 
lean_del_object(v___x_2736_);
v___x_2789_ = lean_nat_add(v___x_2760_, v_size_2761_);
v___x_2790_ = lean_nat_add(v___x_2789_, v_size_2762_);
lean_dec(v_size_2762_);
v___x_2791_ = lean_nat_add(v___x_2789_, v_size_2776_);
lean_dec(v___x_2789_);
lean_inc_ref(v_l_2733_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 4, v_l_2765_);
lean_ctor_set(v___x_2774_, 3, v_l_2733_);
lean_ctor_set(v___x_2774_, 2, v_v_2732_);
lean_ctor_set(v___x_2774_, 1, v_k_2731_);
lean_ctor_set(v___x_2774_, 0, v___x_2791_);
v___x_2793_ = v___x_2774_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2791_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2806_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2806_, 3, v_l_2733_);
lean_ctor_set(v_reuseFailAlloc_2806_, 4, v_l_2765_);
v___x_2793_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
v_isSharedCheck_2800_ = !lean_is_exclusive(v_l_2733_);
if (v_isSharedCheck_2800_ == 0)
{
lean_object* v_unused_2801_; lean_object* v_unused_2802_; lean_object* v_unused_2803_; lean_object* v_unused_2804_; lean_object* v_unused_2805_; 
v_unused_2801_ = lean_ctor_get(v_l_2733_, 4);
lean_dec(v_unused_2801_);
v_unused_2802_ = lean_ctor_get(v_l_2733_, 3);
lean_dec(v_unused_2802_);
v_unused_2803_ = lean_ctor_get(v_l_2733_, 2);
lean_dec(v_unused_2803_);
v_unused_2804_ = lean_ctor_get(v_l_2733_, 1);
lean_dec(v_unused_2804_);
v_unused_2805_ = lean_ctor_get(v_l_2733_, 0);
lean_dec(v_unused_2805_);
v___x_2795_ = v_l_2733_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_dec(v_l_2733_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 4, v_r_2766_);
lean_ctor_set(v___x_2795_, 3, v___x_2793_);
lean_ctor_set(v___x_2795_, 2, v_v_2764_);
lean_ctor_set(v___x_2795_, 1, v_k_2763_);
lean_ctor_set(v___x_2795_, 0, v___x_2790_);
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_k_2763_);
lean_ctor_set(v_reuseFailAlloc_2799_, 2, v_v_2764_);
lean_ctor_set(v_reuseFailAlloc_2799_, 3, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2799_, 4, v_r_2766_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2813_; 
lean_del_object(v___x_2736_);
v_l_2813_ = lean_ctor_get(v_impl_2759_, 3);
lean_inc(v_l_2813_);
if (lean_obj_tag(v_l_2813_) == 0)
{
lean_object* v_r_2814_; lean_object* v_k_2815_; lean_object* v_v_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2837_; 
v_r_2814_ = lean_ctor_get(v_impl_2759_, 4);
v_k_2815_ = lean_ctor_get(v_impl_2759_, 1);
v_v_2816_ = lean_ctor_get(v_impl_2759_, 2);
v_isSharedCheck_2837_ = !lean_is_exclusive(v_impl_2759_);
if (v_isSharedCheck_2837_ == 0)
{
lean_object* v_unused_2838_; lean_object* v_unused_2839_; 
v_unused_2838_ = lean_ctor_get(v_impl_2759_, 3);
lean_dec(v_unused_2838_);
v_unused_2839_ = lean_ctor_get(v_impl_2759_, 0);
lean_dec(v_unused_2839_);
v___x_2818_ = v_impl_2759_;
v_isShared_2819_ = v_isSharedCheck_2837_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_r_2814_);
lean_inc(v_v_2816_);
lean_inc(v_k_2815_);
lean_dec(v_impl_2759_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2837_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v_k_2820_; lean_object* v_v_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2833_; 
v_k_2820_ = lean_ctor_get(v_l_2813_, 1);
v_v_2821_ = lean_ctor_get(v_l_2813_, 2);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_l_2813_);
if (v_isSharedCheck_2833_ == 0)
{
lean_object* v_unused_2834_; lean_object* v_unused_2835_; lean_object* v_unused_2836_; 
v_unused_2834_ = lean_ctor_get(v_l_2813_, 4);
lean_dec(v_unused_2834_);
v_unused_2835_ = lean_ctor_get(v_l_2813_, 3);
lean_dec(v_unused_2835_);
v_unused_2836_ = lean_ctor_get(v_l_2813_, 0);
lean_dec(v_unused_2836_);
v___x_2823_ = v_l_2813_;
v_isShared_2824_ = v_isSharedCheck_2833_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_v_2821_);
lean_inc(v_k_2820_);
lean_dec(v_l_2813_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2833_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2825_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2814_, 2);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 4, v_r_2814_);
lean_ctor_set(v___x_2823_, 3, v_r_2814_);
lean_ctor_set(v___x_2823_, 2, v_v_2732_);
lean_ctor_set(v___x_2823_, 1, v_k_2731_);
lean_ctor_set(v___x_2823_, 0, v___x_2760_);
v___x_2827_ = v___x_2823_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2832_, 3, v_r_2814_);
lean_ctor_set(v_reuseFailAlloc_2832_, 4, v_r_2814_);
v___x_2827_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
lean_object* v___x_2829_; 
lean_inc(v_r_2814_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 3, v_r_2814_);
lean_ctor_set(v___x_2818_, 0, v___x_2760_);
v___x_2829_ = v___x_2818_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_k_2815_);
lean_ctor_set(v_reuseFailAlloc_2831_, 2, v_v_2816_);
lean_ctor_set(v_reuseFailAlloc_2831_, 3, v_r_2814_);
lean_ctor_set(v_reuseFailAlloc_2831_, 4, v_r_2814_);
v___x_2829_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
lean_object* v___x_2830_; 
v___x_2830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2825_);
lean_ctor_set(v___x_2830_, 1, v_k_2820_);
lean_ctor_set(v___x_2830_, 2, v_v_2821_);
lean_ctor_set(v___x_2830_, 3, v___x_2827_);
lean_ctor_set(v___x_2830_, 4, v___x_2829_);
return v___x_2830_;
}
}
}
}
}
else
{
lean_object* v_r_2840_; 
v_r_2840_ = lean_ctor_get(v_impl_2759_, 4);
lean_inc(v_r_2840_);
if (lean_obj_tag(v_r_2840_) == 0)
{
lean_object* v_k_2841_; lean_object* v_v_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2851_; 
v_k_2841_ = lean_ctor_get(v_impl_2759_, 1);
v_v_2842_ = lean_ctor_get(v_impl_2759_, 2);
v_isSharedCheck_2851_ = !lean_is_exclusive(v_impl_2759_);
if (v_isSharedCheck_2851_ == 0)
{
lean_object* v_unused_2852_; lean_object* v_unused_2853_; lean_object* v_unused_2854_; 
v_unused_2852_ = lean_ctor_get(v_impl_2759_, 4);
lean_dec(v_unused_2852_);
v_unused_2853_ = lean_ctor_get(v_impl_2759_, 3);
lean_dec(v_unused_2853_);
v_unused_2854_ = lean_ctor_get(v_impl_2759_, 0);
lean_dec(v_unused_2854_);
v___x_2844_ = v_impl_2759_;
v_isShared_2845_ = v_isSharedCheck_2851_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_v_2842_);
lean_inc(v_k_2841_);
lean_dec(v_impl_2759_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2851_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2846_; lean_object* v___x_2848_; 
v___x_2846_ = lean_unsigned_to_nat(3u);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 4, v_l_2813_);
lean_ctor_set(v___x_2844_, 2, v_v_2732_);
lean_ctor_set(v___x_2844_, 1, v_k_2731_);
lean_ctor_set(v___x_2844_, 0, v___x_2760_);
v___x_2848_ = v___x_2844_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2850_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2850_, 3, v_l_2813_);
lean_ctor_set(v_reuseFailAlloc_2850_, 4, v_l_2813_);
v___x_2848_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
lean_object* v___x_2849_; 
v___x_2849_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2846_);
lean_ctor_set(v___x_2849_, 1, v_k_2841_);
lean_ctor_set(v___x_2849_, 2, v_v_2842_);
lean_ctor_set(v___x_2849_, 3, v___x_2848_);
lean_ctor_set(v___x_2849_, 4, v_r_2840_);
return v___x_2849_;
}
}
}
else
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = lean_unsigned_to_nat(2u);
v___x_2856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
lean_ctor_set(v___x_2856_, 1, v_k_2731_);
lean_ctor_set(v___x_2856_, 2, v_v_2732_);
lean_ctor_set(v___x_2856_, 3, v_r_2840_);
lean_ctor_set(v___x_2856_, 4, v_impl_2759_);
return v___x_2856_;
}
}
}
}
v___jp_2857_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2865_ = lean_nat_add(v___y_2859_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec(v___y_2859_);
v___x_2866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
lean_ctor_set(v___x_2866_, 1, v_k_2731_);
lean_ctor_set(v___x_2866_, 2, v_v_2732_);
lean_ctor_set(v___x_2866_, 3, v___y_2863_);
lean_ctor_set(v___x_2866_, 4, v_r_2734_);
v___x_2867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2867_, 0, v___y_2861_);
lean_ctor_set(v___x_2867_, 1, v___y_2860_);
lean_ctor_set(v___x_2867_, 2, v___y_2862_);
lean_ctor_set(v___x_2867_, 3, v___y_2858_);
lean_ctor_set(v___x_2867_, 4, v___x_2866_);
return v___x_2867_;
}
v___jp_2868_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2881_ = lean_nat_add(v___y_2870_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec(v___y_2870_);
v___x_2882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v___y_2879_);
lean_ctor_set(v___x_2882_, 2, v___y_2871_);
lean_ctor_set(v___x_2882_, 3, v___y_2876_);
lean_ctor_set(v___x_2882_, 4, v___y_2872_);
v___x_2883_ = lean_nat_add(v___y_2869_, v___y_2873_);
lean_dec(v___y_2873_);
if (lean_obj_tag(v___y_2877_) == 0)
{
lean_object* v_size_2884_; 
v_size_2884_ = lean_ctor_get(v___y_2877_, 0);
lean_inc(v_size_2884_);
v___y_2858_ = v___x_2882_;
v___y_2859_ = v___x_2883_;
v___y_2860_ = v___y_2875_;
v___y_2861_ = v___y_2874_;
v___y_2862_ = v___y_2878_;
v___y_2863_ = v___y_2877_;
v___y_2864_ = v_size_2884_;
goto v___jp_2857_;
}
else
{
lean_object* v___x_2885_; 
v___x_2885_ = lean_unsigned_to_nat(0u);
v___y_2858_ = v___x_2882_;
v___y_2859_ = v___x_2883_;
v___y_2860_ = v___y_2875_;
v___y_2861_ = v___y_2874_;
v___y_2862_ = v___y_2878_;
v___y_2863_ = v___y_2877_;
v___y_2864_ = v___x_2885_;
goto v___jp_2857_;
}
}
v___jp_2886_:
{
lean_object* v_impl_2887_; lean_object* v___x_2888_; 
v_impl_2887_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(v_k_2713_, v_v_2714_, v_l_2733_);
v___x_2888_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2734_) == 0)
{
lean_object* v_size_2889_; lean_object* v_size_2890_; lean_object* v_k_2891_; lean_object* v_v_2892_; lean_object* v_l_2893_; lean_object* v_r_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; uint8_t v___x_2897_; 
v_size_2889_ = lean_ctor_get(v_r_2734_, 0);
v_size_2890_ = lean_ctor_get(v_impl_2887_, 0);
lean_inc(v_size_2890_);
v_k_2891_ = lean_ctor_get(v_impl_2887_, 1);
lean_inc(v_k_2891_);
v_v_2892_ = lean_ctor_get(v_impl_2887_, 2);
lean_inc(v_v_2892_);
v_l_2893_ = lean_ctor_get(v_impl_2887_, 3);
lean_inc(v_l_2893_);
v_r_2894_ = lean_ctor_get(v_impl_2887_, 4);
lean_inc(v_r_2894_);
v___x_2895_ = lean_unsigned_to_nat(3u);
v___x_2896_ = lean_nat_mul(v___x_2895_, v_size_2889_);
v___x_2897_ = lean_nat_dec_lt(v___x_2896_, v_size_2890_);
lean_dec(v___x_2896_);
if (v___x_2897_ == 0)
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
lean_dec(v_r_2894_);
lean_dec(v_l_2893_);
lean_dec(v_v_2892_);
lean_dec(v_k_2891_);
v___x_2898_ = lean_nat_add(v___x_2888_, v_size_2890_);
lean_dec(v_size_2890_);
v___x_2899_ = lean_nat_add(v___x_2898_, v_size_2889_);
lean_dec(v___x_2898_);
v___x_2900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
lean_ctor_set(v___x_2900_, 1, v_k_2731_);
lean_ctor_set(v___x_2900_, 2, v_v_2732_);
lean_ctor_set(v___x_2900_, 3, v_impl_2887_);
lean_ctor_set(v___x_2900_, 4, v_r_2734_);
return v___x_2900_;
}
else
{
lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2937_; 
v_isSharedCheck_2937_ = !lean_is_exclusive(v_impl_2887_);
if (v_isSharedCheck_2937_ == 0)
{
lean_object* v_unused_2938_; lean_object* v_unused_2939_; lean_object* v_unused_2940_; lean_object* v_unused_2941_; lean_object* v_unused_2942_; 
v_unused_2938_ = lean_ctor_get(v_impl_2887_, 4);
lean_dec(v_unused_2938_);
v_unused_2939_ = lean_ctor_get(v_impl_2887_, 3);
lean_dec(v_unused_2939_);
v_unused_2940_ = lean_ctor_get(v_impl_2887_, 2);
lean_dec(v_unused_2940_);
v_unused_2941_ = lean_ctor_get(v_impl_2887_, 1);
lean_dec(v_unused_2941_);
v_unused_2942_ = lean_ctor_get(v_impl_2887_, 0);
lean_dec(v_unused_2942_);
v___x_2902_ = v_impl_2887_;
v_isShared_2903_ = v_isSharedCheck_2937_;
goto v_resetjp_2901_;
}
else
{
lean_dec(v_impl_2887_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2937_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v_size_2904_; lean_object* v_size_2905_; lean_object* v_k_2906_; lean_object* v_v_2907_; lean_object* v_l_2908_; lean_object* v_r_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; uint8_t v___x_2912_; 
v_size_2904_ = lean_ctor_get(v_l_2893_, 0);
v_size_2905_ = lean_ctor_get(v_r_2894_, 0);
v_k_2906_ = lean_ctor_get(v_r_2894_, 1);
v_v_2907_ = lean_ctor_get(v_r_2894_, 2);
v_l_2908_ = lean_ctor_get(v_r_2894_, 3);
v_r_2909_ = lean_ctor_get(v_r_2894_, 4);
v___x_2910_ = lean_unsigned_to_nat(2u);
v___x_2911_ = lean_nat_mul(v___x_2910_, v_size_2904_);
v___x_2912_ = lean_nat_dec_lt(v_size_2905_, v___x_2911_);
lean_dec(v___x_2911_);
if (v___x_2912_ == 0)
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
lean_inc(v_r_2909_);
lean_inc(v_l_2908_);
lean_inc(v_v_2907_);
lean_inc(v_k_2906_);
lean_del_object(v___x_2902_);
lean_dec(v_r_2894_);
v___x_2913_ = lean_nat_add(v___x_2888_, v_size_2890_);
lean_dec(v_size_2890_);
v___x_2914_ = lean_nat_add(v___x_2913_, v_size_2889_);
lean_dec(v___x_2913_);
v___x_2915_ = lean_nat_add(v___x_2888_, v_size_2904_);
if (lean_obj_tag(v_l_2908_) == 0)
{
lean_object* v_size_2916_; 
v_size_2916_ = lean_ctor_get(v_l_2908_, 0);
lean_inc(v_size_2916_);
lean_inc(v_size_2889_);
v___y_2869_ = v___x_2888_;
v___y_2870_ = v___x_2915_;
v___y_2871_ = v_v_2892_;
v___y_2872_ = v_l_2908_;
v___y_2873_ = v_size_2889_;
v___y_2874_ = v___x_2914_;
v___y_2875_ = v_k_2906_;
v___y_2876_ = v_l_2893_;
v___y_2877_ = v_r_2909_;
v___y_2878_ = v_v_2907_;
v___y_2879_ = v_k_2891_;
v___y_2880_ = v_size_2916_;
goto v___jp_2868_;
}
else
{
lean_object* v___x_2917_; 
v___x_2917_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_2889_);
v___y_2869_ = v___x_2888_;
v___y_2870_ = v___x_2915_;
v___y_2871_ = v_v_2892_;
v___y_2872_ = v_l_2908_;
v___y_2873_ = v_size_2889_;
v___y_2874_ = v___x_2914_;
v___y_2875_ = v_k_2906_;
v___y_2876_ = v_l_2893_;
v___y_2877_ = v_r_2909_;
v___y_2878_ = v_v_2907_;
v___y_2879_ = v_k_2891_;
v___y_2880_ = v___x_2917_;
goto v___jp_2868_;
}
}
else
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2923_; 
v___x_2918_ = lean_nat_add(v___x_2888_, v_size_2890_);
lean_dec(v_size_2890_);
v___x_2919_ = lean_nat_add(v___x_2918_, v_size_2889_);
lean_dec(v___x_2918_);
v___x_2920_ = lean_nat_add(v___x_2888_, v_size_2889_);
v___x_2921_ = lean_nat_add(v___x_2920_, v_size_2905_);
lean_dec(v___x_2920_);
lean_inc_ref(v_r_2734_);
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 4, v_r_2734_);
lean_ctor_set(v___x_2902_, 3, v_r_2894_);
lean_ctor_set(v___x_2902_, 2, v_v_2732_);
lean_ctor_set(v___x_2902_, 1, v_k_2731_);
lean_ctor_set(v___x_2902_, 0, v___x_2921_);
v___x_2923_ = v___x_2902_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2921_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2936_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2936_, 3, v_r_2894_);
lean_ctor_set(v_reuseFailAlloc_2936_, 4, v_r_2734_);
v___x_2923_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
v_isSharedCheck_2930_ = !lean_is_exclusive(v_r_2734_);
if (v_isSharedCheck_2930_ == 0)
{
lean_object* v_unused_2931_; lean_object* v_unused_2932_; lean_object* v_unused_2933_; lean_object* v_unused_2934_; lean_object* v_unused_2935_; 
v_unused_2931_ = lean_ctor_get(v_r_2734_, 4);
lean_dec(v_unused_2931_);
v_unused_2932_ = lean_ctor_get(v_r_2734_, 3);
lean_dec(v_unused_2932_);
v_unused_2933_ = lean_ctor_get(v_r_2734_, 2);
lean_dec(v_unused_2933_);
v_unused_2934_ = lean_ctor_get(v_r_2734_, 1);
lean_dec(v_unused_2934_);
v_unused_2935_ = lean_ctor_get(v_r_2734_, 0);
lean_dec(v_unused_2935_);
v___x_2925_ = v_r_2734_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_dec(v_r_2734_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 4, v___x_2923_);
lean_ctor_set(v___x_2925_, 3, v_l_2893_);
lean_ctor_set(v___x_2925_, 2, v_v_2892_);
lean_ctor_set(v___x_2925_, 1, v_k_2891_);
lean_ctor_set(v___x_2925_, 0, v___x_2919_);
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2919_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_k_2891_);
lean_ctor_set(v_reuseFailAlloc_2929_, 2, v_v_2892_);
lean_ctor_set(v_reuseFailAlloc_2929_, 3, v_l_2893_);
lean_ctor_set(v_reuseFailAlloc_2929_, 4, v___x_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2943_; 
v_l_2943_ = lean_ctor_get(v_impl_2887_, 3);
lean_inc(v_l_2943_);
if (lean_obj_tag(v_l_2943_) == 0)
{
lean_object* v_r_2944_; lean_object* v_k_2945_; lean_object* v_v_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2955_; 
v_r_2944_ = lean_ctor_get(v_impl_2887_, 4);
v_k_2945_ = lean_ctor_get(v_impl_2887_, 1);
v_v_2946_ = lean_ctor_get(v_impl_2887_, 2);
v_isSharedCheck_2955_ = !lean_is_exclusive(v_impl_2887_);
if (v_isSharedCheck_2955_ == 0)
{
lean_object* v_unused_2956_; lean_object* v_unused_2957_; 
v_unused_2956_ = lean_ctor_get(v_impl_2887_, 3);
lean_dec(v_unused_2956_);
v_unused_2957_ = lean_ctor_get(v_impl_2887_, 0);
lean_dec(v_unused_2957_);
v___x_2948_ = v_impl_2887_;
v_isShared_2949_ = v_isSharedCheck_2955_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_r_2944_);
lean_inc(v_v_2946_);
lean_inc(v_k_2945_);
lean_dec(v_impl_2887_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2955_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2950_; lean_object* v___x_2952_; 
v___x_2950_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2944_);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 3, v_r_2944_);
lean_ctor_set(v___x_2948_, 2, v_v_2732_);
lean_ctor_set(v___x_2948_, 1, v_k_2731_);
lean_ctor_set(v___x_2948_, 0, v___x_2888_);
v___x_2952_ = v___x_2948_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2888_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2954_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2954_, 3, v_r_2944_);
lean_ctor_set(v_reuseFailAlloc_2954_, 4, v_r_2944_);
v___x_2952_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2953_; 
v___x_2953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2950_);
lean_ctor_set(v___x_2953_, 1, v_k_2945_);
lean_ctor_set(v___x_2953_, 2, v_v_2946_);
lean_ctor_set(v___x_2953_, 3, v_l_2943_);
lean_ctor_set(v___x_2953_, 4, v___x_2952_);
return v___x_2953_;
}
}
}
else
{
lean_object* v_r_2958_; 
v_r_2958_ = lean_ctor_get(v_impl_2887_, 4);
lean_inc(v_r_2958_);
if (lean_obj_tag(v_r_2958_) == 0)
{
lean_object* v_k_2959_; lean_object* v_v_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2981_; 
v_k_2959_ = lean_ctor_get(v_impl_2887_, 1);
v_v_2960_ = lean_ctor_get(v_impl_2887_, 2);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_impl_2887_);
if (v_isSharedCheck_2981_ == 0)
{
lean_object* v_unused_2982_; lean_object* v_unused_2983_; lean_object* v_unused_2984_; 
v_unused_2982_ = lean_ctor_get(v_impl_2887_, 4);
lean_dec(v_unused_2982_);
v_unused_2983_ = lean_ctor_get(v_impl_2887_, 3);
lean_dec(v_unused_2983_);
v_unused_2984_ = lean_ctor_get(v_impl_2887_, 0);
lean_dec(v_unused_2984_);
v___x_2962_ = v_impl_2887_;
v_isShared_2963_ = v_isSharedCheck_2981_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_v_2960_);
lean_inc(v_k_2959_);
lean_dec(v_impl_2887_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2981_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v_k_2964_; lean_object* v_v_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2977_; 
v_k_2964_ = lean_ctor_get(v_r_2958_, 1);
v_v_2965_ = lean_ctor_get(v_r_2958_, 2);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_r_2958_);
if (v_isSharedCheck_2977_ == 0)
{
lean_object* v_unused_2978_; lean_object* v_unused_2979_; lean_object* v_unused_2980_; 
v_unused_2978_ = lean_ctor_get(v_r_2958_, 4);
lean_dec(v_unused_2978_);
v_unused_2979_ = lean_ctor_get(v_r_2958_, 3);
lean_dec(v_unused_2979_);
v_unused_2980_ = lean_ctor_get(v_r_2958_, 0);
lean_dec(v_unused_2980_);
v___x_2967_ = v_r_2958_;
v_isShared_2968_ = v_isSharedCheck_2977_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_v_2965_);
lean_inc(v_k_2964_);
lean_dec(v_r_2958_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2977_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; lean_object* v___x_2971_; 
v___x_2969_ = lean_unsigned_to_nat(3u);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 4, v_l_2943_);
lean_ctor_set(v___x_2967_, 3, v_l_2943_);
lean_ctor_set(v___x_2967_, 2, v_v_2960_);
lean_ctor_set(v___x_2967_, 1, v_k_2959_);
lean_ctor_set(v___x_2967_, 0, v___x_2888_);
v___x_2971_ = v___x_2967_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2888_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_k_2959_);
lean_ctor_set(v_reuseFailAlloc_2976_, 2, v_v_2960_);
lean_ctor_set(v_reuseFailAlloc_2976_, 3, v_l_2943_);
lean_ctor_set(v_reuseFailAlloc_2976_, 4, v_l_2943_);
v___x_2971_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2973_; 
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 4, v_l_2943_);
lean_ctor_set(v___x_2962_, 2, v_v_2732_);
lean_ctor_set(v___x_2962_, 1, v_k_2731_);
lean_ctor_set(v___x_2962_, 0, v___x_2888_);
v___x_2973_ = v___x_2962_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2888_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_k_2731_);
lean_ctor_set(v_reuseFailAlloc_2975_, 2, v_v_2732_);
lean_ctor_set(v_reuseFailAlloc_2975_, 3, v_l_2943_);
lean_ctor_set(v_reuseFailAlloc_2975_, 4, v_l_2943_);
v___x_2973_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2974_; 
v___x_2974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2969_);
lean_ctor_set(v___x_2974_, 1, v_k_2964_);
lean_ctor_set(v___x_2974_, 2, v_v_2965_);
lean_ctor_set(v___x_2974_, 3, v___x_2971_);
lean_ctor_set(v___x_2974_, 4, v___x_2973_);
return v___x_2974_;
}
}
}
}
}
else
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = lean_unsigned_to_nat(2u);
v___x_2986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
lean_ctor_set(v___x_2986_, 1, v_k_2731_);
lean_ctor_set(v___x_2986_, 2, v_v_2732_);
lean_ctor_set(v___x_2986_, 3, v_impl_2887_);
lean_ctor_set(v___x_2986_, 4, v_r_2958_);
return v___x_2986_;
}
}
}
}
}
}
else
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = lean_unsigned_to_nat(1u);
v___x_3001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
lean_ctor_set(v___x_3001_, 1, v_k_2713_);
lean_ctor_set(v___x_3001_, 2, v_v_2714_);
lean_ctor_set(v___x_3001_, 3, v_t_2715_);
lean_ctor_set(v___x_3001_, 4, v_t_2715_);
return v___x_3001_;
}
v___jp_2716_:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2727_ = lean_nat_add(v___y_2717_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec(v___y_2717_);
v___x_2728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
lean_ctor_set(v___x_2728_, 1, v___y_2721_);
lean_ctor_set(v___x_2728_, 2, v___y_2725_);
lean_ctor_set(v___x_2728_, 3, v___y_2719_);
lean_ctor_set(v___x_2728_, 4, v___y_2722_);
v___x_2729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2729_, 0, v___y_2724_);
lean_ctor_set(v___x_2729_, 1, v___y_2718_);
lean_ctor_set(v___x_2729_, 2, v___y_2723_);
lean_ctor_set(v___x_2729_, 3, v___y_2720_);
lean_ctor_set(v___x_2729_, 4, v___x_2728_);
return v___x_2729_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg(lean_object* v_k_3002_, lean_object* v_t_3003_){
_start:
{
if (lean_obj_tag(v_t_3003_) == 0)
{
lean_object* v_k_3004_; lean_object* v_l_3005_; lean_object* v_r_3006_; lean_object* v_fst_3007_; lean_object* v_snd_3008_; lean_object* v_fst_3009_; lean_object* v_snd_3010_; double v___x_3011_; double v___x_3012_; uint8_t v___x_3013_; 
v_k_3004_ = lean_ctor_get(v_t_3003_, 1);
v_l_3005_ = lean_ctor_get(v_t_3003_, 3);
v_r_3006_ = lean_ctor_get(v_t_3003_, 4);
v_fst_3007_ = lean_ctor_get(v_k_3002_, 0);
v_snd_3008_ = lean_ctor_get(v_k_3002_, 1);
v_fst_3009_ = lean_ctor_get(v_k_3004_, 0);
v_snd_3010_ = lean_ctor_get(v_k_3004_, 1);
v___x_3011_ = lean_unbox_float(v_fst_3007_);
v___x_3012_ = lean_unbox_float(v_fst_3009_);
v___x_3013_ = lean_float_decLt(v___x_3011_, v___x_3012_);
if (v___x_3013_ == 0)
{
double v___x_3014_; double v___x_3015_; uint8_t v___x_3016_; 
v___x_3014_ = lean_unbox_float(v_fst_3009_);
v___x_3015_ = lean_unbox_float(v_fst_3007_);
v___x_3016_ = lean_float_decLt(v___x_3014_, v___x_3015_);
if (v___x_3016_ == 0)
{
uint8_t v___x_3017_; 
v___x_3017_ = l_Lean_Name_cmp(v_snd_3008_, v_snd_3010_);
switch(v___x_3017_)
{
case 0:
{
v_t_3003_ = v_l_3005_;
goto _start;
}
case 1:
{
uint8_t v___x_3019_; 
v___x_3019_ = 1;
return v___x_3019_;
}
default: 
{
v_t_3003_ = v_r_3006_;
goto _start;
}
}
}
else
{
v_t_3003_ = v_r_3006_;
goto _start;
}
}
else
{
v_t_3003_ = v_l_3005_;
goto _start;
}
}
else
{
uint8_t v___x_3023_; 
v___x_3023_ = 0;
return v___x_3023_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg___boxed(lean_object* v_k_3024_, lean_object* v_t_3025_){
_start:
{
uint8_t v_res_3026_; lean_object* v_r_3027_; 
v_res_3026_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg(v_k_3024_, v_t_3025_);
lean_dec(v_t_3025_);
lean_dec_ref(v_k_3024_);
v_r_3027_ = lean_box(v_res_3026_);
return v_r_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg(double v_frequencyWeight_3028_, double v_fst_3029_, double v_depthFactor_3030_, lean_object* v_denyList_3031_, lean_object* v_as_3032_, size_t v_i_3033_, size_t v_stop_3034_, lean_object* v_b_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v_a_3039_; lean_object* v___y_3044_; lean_object* v___y_3045_; uint8_t v___x_3047_; 
v___x_3047_ = lean_usize_dec_eq(v_i_3033_, v_stop_3034_);
if (v___x_3047_ == 0)
{
lean_object* v_fst_3048_; lean_object* v_snd_3049_; lean_object* v___x_3050_; uint8_t v___y_3052_; uint8_t v___x_3080_; 
v_fst_3048_ = lean_ctor_get(v_b_3035_, 0);
v_snd_3049_ = lean_ctor_get(v_b_3035_, 1);
v___x_3050_ = lean_array_uget_borrowed(v_as_3032_, v_i_3033_);
v___x_3080_ = l_Lean_NameSet_contains(v_fst_3048_, v___x_3050_);
if (v___x_3080_ == 0)
{
uint8_t v___x_3081_; 
v___x_3081_ = l_Lean_NameSet_contains(v_denyList_3031_, v___x_3050_);
v___y_3052_ = v___x_3081_;
goto v___jp_3051_;
}
else
{
v___y_3052_ = v___x_3080_;
goto v___jp_3051_;
}
v___jp_3051_:
{
if (v___y_3052_ == 0)
{
lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3077_; 
lean_inc(v_snd_3049_);
lean_inc(v_fst_3048_);
v_isSharedCheck_3077_ = !lean_is_exclusive(v_b_3035_);
if (v_isSharedCheck_3077_ == 0)
{
lean_object* v_unused_3078_; lean_object* v_unused_3079_; 
v_unused_3078_ = lean_ctor_get(v_b_3035_, 1);
lean_dec(v_unused_3078_);
v_unused_3079_ = lean_ctor_get(v_b_3035_, 0);
lean_dec(v_unused_3079_);
v___x_3054_ = v_b_3035_;
v_isShared_3055_ = v_isSharedCheck_3077_;
goto v_resetjp_3053_;
}
else
{
lean_dec(v_b_3035_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3077_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3056_; 
v___x_3056_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg(v___x_3050_, v_frequencyWeight_3028_, v___y_3036_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v___x_3058_; double v___x_3059_; double v___x_3060_; double v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3064_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3057_);
lean_dec_ref(v___x_3056_);
lean_inc(v___x_3050_);
v___x_3058_ = l_Lean_NameSet_insert(v_fst_3048_, v___x_3050_);
v___x_3059_ = lean_float_mul(v_fst_3029_, v_depthFactor_3030_);
v___x_3060_ = lean_unbox_float(v_a_3057_);
lean_dec(v_a_3057_);
v___x_3061_ = lean_float_mul(v___x_3059_, v___x_3060_);
v___x_3062_ = lean_box_float(v___x_3061_);
lean_inc(v___x_3050_);
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 1, v___x_3050_);
lean_ctor_set(v___x_3054_, 0, v___x_3062_);
v___x_3064_ = v___x_3054_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3062_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v___x_3050_);
v___x_3064_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
uint8_t v___x_3065_; 
v___x_3065_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg(v___x_3064_, v_snd_3049_);
if (v___x_3065_ == 0)
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = lean_box(0);
v___x_3067_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(v___x_3064_, v___x_3066_, v_snd_3049_);
v___y_3044_ = v___x_3058_;
v___y_3045_ = v___x_3067_;
goto v___jp_3043_;
}
else
{
lean_dec_ref(v___x_3064_);
v___y_3044_ = v___x_3058_;
v___y_3045_ = v_snd_3049_;
goto v___jp_3043_;
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_del_object(v___x_3054_);
lean_dec(v_snd_3049_);
lean_dec(v_fst_3048_);
v_a_3069_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3056_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3056_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
}
else
{
v_a_3039_ = v_b_3035_;
goto v___jp_3038_;
}
}
}
else
{
lean_object* v___x_3082_; 
v___x_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3082_, 0, v_b_3035_);
return v___x_3082_;
}
v___jp_3038_:
{
size_t v___x_3040_; size_t v___x_3041_; 
v___x_3040_ = ((size_t)1ULL);
v___x_3041_ = lean_usize_add(v_i_3033_, v___x_3040_);
v_i_3033_ = v___x_3041_;
v_b_3035_ = v_a_3039_;
goto _start;
}
v___jp_3043_:
{
lean_object* v___x_3046_; 
v___x_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___y_3044_);
lean_ctor_set(v___x_3046_, 1, v___y_3045_);
v_a_3039_ = v___x_3046_;
goto v___jp_3038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg___boxed(lean_object* v_frequencyWeight_3083_, lean_object* v_fst_3084_, lean_object* v_depthFactor_3085_, lean_object* v_denyList_3086_, lean_object* v_as_3087_, lean_object* v_i_3088_, lean_object* v_stop_3089_, lean_object* v_b_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
double v_frequencyWeight_boxed_3093_; double v_fst_11007__boxed_3094_; double v_depthFactor_boxed_3095_; size_t v_i_boxed_3096_; size_t v_stop_boxed_3097_; lean_object* v_res_3098_; 
v_frequencyWeight_boxed_3093_ = lean_unbox_float(v_frequencyWeight_3083_);
lean_dec_ref(v_frequencyWeight_3083_);
v_fst_11007__boxed_3094_ = lean_unbox_float(v_fst_3084_);
lean_dec_ref(v_fst_3084_);
v_depthFactor_boxed_3095_ = lean_unbox_float(v_depthFactor_3085_);
lean_dec_ref(v_depthFactor_3085_);
v_i_boxed_3096_ = lean_unbox_usize(v_i_3088_);
lean_dec(v_i_3088_);
v_stop_boxed_3097_ = lean_unbox_usize(v_stop_3089_);
lean_dec(v_stop_3089_);
v_res_3098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg(v_frequencyWeight_boxed_3093_, v_fst_11007__boxed_3094_, v_depthFactor_boxed_3095_, v_denyList_3086_, v_as_3087_, v_i_boxed_3096_, v_stop_boxed_3097_, v_b_3090_, v___y_3091_);
lean_dec(v___y_3091_);
lean_dec_ref(v_as_3087_);
lean_dec(v_denyList_3086_);
return v_res_3098_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__1));
v___x_3103_ = l_Lean_MessageData_ofFormat(v___x_3102_);
return v___x_3103_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__3(void){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = lean_box(1);
v___x_3105_ = l_Lean_MessageData_ofFormat(v___x_3104_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6(lean_object* v_a_3106_, lean_object* v_a_3107_){
_start:
{
if (lean_obj_tag(v_a_3106_) == 0)
{
lean_object* v___x_3108_; 
v___x_3108_ = l_List_reverse___redArg(v_a_3107_);
return v___x_3108_;
}
else
{
lean_object* v_head_3109_; lean_object* v_tail_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3137_; 
v_head_3109_ = lean_ctor_get(v_a_3106_, 0);
v_tail_3110_ = lean_ctor_get(v_a_3106_, 1);
v_isSharedCheck_3137_ = !lean_is_exclusive(v_a_3106_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3112_ = v_a_3106_;
v_isShared_3113_ = v_isSharedCheck_3137_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_tail_3110_);
lean_inc(v_head_3109_);
lean_dec(v_a_3106_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3137_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v_fst_3114_; lean_object* v_snd_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3136_; 
v_fst_3114_ = lean_ctor_get(v_head_3109_, 0);
v_snd_3115_ = lean_ctor_get(v_head_3109_, 1);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_head_3109_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3117_ = v_head_3109_;
v_isShared_3118_ = v_isSharedCheck_3136_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_snd_3115_);
lean_inc(v_fst_3114_);
lean_dec(v_head_3109_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3136_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3122_; 
v___x_3119_ = l_Lean_MessageData_ofName(v_fst_3114_);
v___x_3120_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__2, &l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__2);
if (v_isShared_3118_ == 0)
{
lean_ctor_set_tag(v___x_3117_, 7);
lean_ctor_set(v___x_3117_, 1, v___x_3120_);
lean_ctor_set(v___x_3117_, 0, v___x_3119_);
v___x_3122_ = v___x_3117_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3119_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v___x_3120_);
v___x_3122_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; double v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3123_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__3, &l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__3);
v___x_3124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3122_);
lean_ctor_set(v___x_3124_, 1, v___x_3123_);
v___x_3125_ = lean_unbox_float(v_snd_3115_);
lean_dec(v_snd_3115_);
v___x_3126_ = lean_float_to_string(v___x_3125_);
v___x_3127_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
v___x_3128_ = l_Lean_MessageData_ofFormat(v___x_3127_);
v___x_3129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3124_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = l_Lean_MessageData_paren(v___x_3129_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 1, v_a_3107_);
lean_ctor_set(v___x_3112_, 0, v___x_3130_);
v___x_3132_ = v___x_3112_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3130_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v_a_3107_);
v___x_3132_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
v_a_3106_ = v_tail_3110_;
v_a_3107_ = v___x_3132_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9(lean_object* v_init_3138_, lean_object* v_x_3139_){
_start:
{
if (lean_obj_tag(v_x_3139_) == 0)
{
lean_object* v_k_3140_; lean_object* v_l_3141_; lean_object* v_r_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v_k_3140_ = lean_ctor_get(v_x_3139_, 1);
v_l_3141_ = lean_ctor_get(v_x_3139_, 3);
v_r_3142_ = lean_ctor_get(v_x_3139_, 4);
v___x_3143_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9(v_init_3138_, v_r_3142_);
lean_inc(v_k_3140_);
v___x_3144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3144_, 0, v_k_3140_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v_init_3138_ = v___x_3144_;
v_x_3139_ = v_l_3141_;
goto _start;
}
else
{
return v_init_3138_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9___boxed(lean_object* v_init_3146_, lean_object* v_x_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9(v_init_3146_, v_x_3147_);
lean_dec(v_x_3147_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10(lean_object* v_a_3149_, lean_object* v_a_3150_){
_start:
{
if (lean_obj_tag(v_a_3149_) == 0)
{
lean_object* v___x_3151_; 
v___x_3151_ = l_List_reverse___redArg(v_a_3150_);
return v___x_3151_;
}
else
{
lean_object* v_head_3152_; lean_object* v_tail_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3180_; 
v_head_3152_ = lean_ctor_get(v_a_3149_, 0);
v_tail_3153_ = lean_ctor_get(v_a_3149_, 1);
v_isSharedCheck_3180_ = !lean_is_exclusive(v_a_3149_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3155_ = v_a_3149_;
v_isShared_3156_ = v_isSharedCheck_3180_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_tail_3153_);
lean_inc(v_head_3152_);
lean_dec(v_a_3149_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3180_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v_fst_3157_; lean_object* v_snd_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3179_; 
v_fst_3157_ = lean_ctor_get(v_head_3152_, 0);
v_snd_3158_ = lean_ctor_get(v_head_3152_, 1);
v_isSharedCheck_3179_ = !lean_is_exclusive(v_head_3152_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3160_ = v_head_3152_;
v_isShared_3161_ = v_isSharedCheck_3179_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_snd_3158_);
lean_inc(v_fst_3157_);
lean_dec(v_head_3152_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3179_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
double v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3168_; 
v___x_3162_ = lean_unbox_float(v_fst_3157_);
lean_dec(v_fst_3157_);
v___x_3163_ = lean_float_to_string(v___x_3162_);
v___x_3164_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
v___x_3165_ = l_Lean_MessageData_ofFormat(v___x_3164_);
v___x_3166_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__2, &l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__2);
if (v_isShared_3161_ == 0)
{
lean_ctor_set_tag(v___x_3160_, 7);
lean_ctor_set(v___x_3160_, 1, v___x_3166_);
lean_ctor_set(v___x_3160_, 0, v___x_3165_);
v___x_3168_ = v___x_3160_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3178_, 1, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3175_; 
v___x_3169_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__3, &l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__3);
v___x_3170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3168_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = l_Lean_MessageData_ofName(v_snd_3158_);
v___x_3172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3170_);
lean_ctor_set(v___x_3172_, 1, v___x_3171_);
v___x_3173_ = l_Lean_MessageData_paren(v___x_3172_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 1, v_a_3150_);
lean_ctor_set(v___x_3155_, 0, v___x_3173_);
v___x_3175_ = v___x_3155_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3173_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v_a_3150_);
v___x_3175_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
v_a_3149_ = v_tail_3153_;
v_a_3150_ = v___x_3175_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__7(lean_object* v_init_3181_, lean_object* v_x_3182_){
_start:
{
if (lean_obj_tag(v_x_3182_) == 0)
{
lean_object* v_k_3183_; lean_object* v_l_3184_; lean_object* v_r_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v_k_3183_ = lean_ctor_get(v_x_3182_, 1);
v_l_3184_ = lean_ctor_get(v_x_3182_, 3);
v_r_3185_ = lean_ctor_get(v_x_3182_, 4);
v___x_3186_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__7(v_init_3181_, v_r_3185_);
lean_inc(v_k_3183_);
v___x_3187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3187_, 0, v_k_3183_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
v_init_3181_ = v___x_3187_;
v_x_3182_ = v_l_3184_;
goto _start;
}
else
{
return v_init_3181_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__7___boxed(lean_object* v_init_3189_, lean_object* v_x_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__7(v_init_3189_, v_x_3190_);
lean_dec(v_x_3190_);
return v_res_3191_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__0(void){
_start:
{
lean_object* v___x_3192_; double v___x_3193_; 
v___x_3192_ = lean_unsigned_to_nat(0u);
v___x_3193_ = lean_float_of_nat(v___x_3192_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11(lean_object* v_cls_3197_, lean_object* v_msg_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v_ref_3204_; lean_object* v___x_3205_; lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3250_; 
v_ref_3204_ = lean_ctor_get(v___y_3201_, 5);
v___x_3205_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9_spec__10(v_msg_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3250_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3250_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v_traceState_3211_; lean_object* v_env_3212_; lean_object* v_nextMacroScope_3213_; lean_object* v_ngen_3214_; lean_object* v_auxDeclNGen_3215_; lean_object* v_cache_3216_; lean_object* v_messages_3217_; lean_object* v_infoState_3218_; lean_object* v_snapshotTasks_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3249_; 
v___x_3210_ = lean_st_ref_take(v___y_3202_);
v_traceState_3211_ = lean_ctor_get(v___x_3210_, 4);
v_env_3212_ = lean_ctor_get(v___x_3210_, 0);
v_nextMacroScope_3213_ = lean_ctor_get(v___x_3210_, 1);
v_ngen_3214_ = lean_ctor_get(v___x_3210_, 2);
v_auxDeclNGen_3215_ = lean_ctor_get(v___x_3210_, 3);
v_cache_3216_ = lean_ctor_get(v___x_3210_, 5);
v_messages_3217_ = lean_ctor_get(v___x_3210_, 6);
v_infoState_3218_ = lean_ctor_get(v___x_3210_, 7);
v_snapshotTasks_3219_ = lean_ctor_get(v___x_3210_, 8);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3221_ = v___x_3210_;
v_isShared_3222_ = v_isSharedCheck_3249_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_snapshotTasks_3219_);
lean_inc(v_infoState_3218_);
lean_inc(v_messages_3217_);
lean_inc(v_cache_3216_);
lean_inc(v_traceState_3211_);
lean_inc(v_auxDeclNGen_3215_);
lean_inc(v_ngen_3214_);
lean_inc(v_nextMacroScope_3213_);
lean_inc(v_env_3212_);
lean_dec(v___x_3210_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3249_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
uint64_t v_tid_3223_; lean_object* v_traces_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3248_; 
v_tid_3223_ = lean_ctor_get_uint64(v_traceState_3211_, sizeof(void*)*1);
v_traces_3224_ = lean_ctor_get(v_traceState_3211_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_traceState_3211_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3226_ = v_traceState_3211_;
v_isShared_3227_ = v_isSharedCheck_3248_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_traces_3224_);
lean_dec(v_traceState_3211_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3248_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; double v___x_3229_; uint8_t v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3228_ = lean_box(0);
v___x_3229_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__0, &l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__0);
v___x_3230_ = 0;
v___x_3231_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__1));
v___x_3232_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3232_, 0, v_cls_3197_);
lean_ctor_set(v___x_3232_, 1, v___x_3228_);
lean_ctor_set(v___x_3232_, 2, v___x_3231_);
lean_ctor_set_float(v___x_3232_, sizeof(void*)*3, v___x_3229_);
lean_ctor_set_float(v___x_3232_, sizeof(void*)*3 + 8, v___x_3229_);
lean_ctor_set_uint8(v___x_3232_, sizeof(void*)*3 + 16, v___x_3230_);
v___x_3233_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__2));
v___x_3234_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3232_);
lean_ctor_set(v___x_3234_, 1, v_a_3206_);
lean_ctor_set(v___x_3234_, 2, v___x_3233_);
lean_inc(v_ref_3204_);
v___x_3235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3235_, 0, v_ref_3204_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___x_3236_ = l_Lean_PersistentArray_push___redArg(v_traces_3224_, v___x_3235_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v___x_3236_);
v___x_3238_ = v___x_3226_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3236_);
lean_ctor_set_uint64(v_reuseFailAlloc_3247_, sizeof(void*)*1, v_tid_3223_);
v___x_3238_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3240_; 
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 4, v___x_3238_);
v___x_3240_ = v___x_3221_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_env_3212_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_nextMacroScope_3213_);
lean_ctor_set(v_reuseFailAlloc_3246_, 2, v_ngen_3214_);
lean_ctor_set(v_reuseFailAlloc_3246_, 3, v_auxDeclNGen_3215_);
lean_ctor_set(v_reuseFailAlloc_3246_, 4, v___x_3238_);
lean_ctor_set(v_reuseFailAlloc_3246_, 5, v_cache_3216_);
lean_ctor_set(v_reuseFailAlloc_3246_, 6, v_messages_3217_);
lean_ctor_set(v_reuseFailAlloc_3246_, 7, v_infoState_3218_);
lean_ctor_set(v_reuseFailAlloc_3246_, 8, v_snapshotTasks_3219_);
v___x_3240_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3244_; 
v___x_3241_ = lean_st_ref_set(v___y_3202_, v___x_3240_);
v___x_3242_ = lean_box(0);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3242_);
v___x_3244_ = v___x_3208_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___boxed(lean_object* v_cls_3251_, lean_object* v_msg_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11(v_cls_3251_, v_msg_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__8(lean_object* v_a_3259_, lean_object* v_a_3260_){
_start:
{
if (lean_obj_tag(v_a_3259_) == 0)
{
lean_object* v___x_3261_; 
v___x_3261_ = l_List_reverse___redArg(v_a_3260_);
return v___x_3261_;
}
else
{
lean_object* v_head_3262_; lean_object* v_tail_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3272_; 
v_head_3262_ = lean_ctor_get(v_a_3259_, 0);
v_tail_3263_ = lean_ctor_get(v_a_3259_, 1);
v_isSharedCheck_3272_ = !lean_is_exclusive(v_a_3259_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3265_ = v_a_3259_;
v_isShared_3266_ = v_isSharedCheck_3272_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_tail_3263_);
lean_inc(v_head_3262_);
lean_dec(v_a_3259_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3272_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3267_; lean_object* v___x_3269_; 
v___x_3267_ = l_Lean_MessageData_ofName(v_head_3262_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 1, v_a_3260_);
lean_ctor_set(v___x_3265_, 0, v___x_3267_);
v___x_3269_ = v___x_3265_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3267_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_a_3260_);
v___x_3269_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
v_a_3259_ = v_tail_3263_;
v_a_3260_ = v___x_3269_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__4(double v_fst_3273_, lean_object* v_x_3274_, lean_object* v_x_3275_){
_start:
{
if (lean_obj_tag(v_x_3275_) == 0)
{
return v_x_3274_;
}
else
{
lean_object* v_head_3276_; lean_object* v_tail_3277_; lean_object* v_fst_3278_; lean_object* v_snd_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3294_; 
v_head_3276_ = lean_ctor_get(v_x_3275_, 0);
lean_inc(v_head_3276_);
v_tail_3277_ = lean_ctor_get(v_x_3275_, 1);
lean_inc(v_tail_3277_);
lean_dec_ref(v_x_3275_);
v_fst_3278_ = lean_ctor_get(v_head_3276_, 0);
v_snd_3279_ = lean_ctor_get(v_head_3276_, 1);
v_isSharedCheck_3294_ = !lean_is_exclusive(v_head_3276_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3281_ = v_head_3276_;
v_isShared_3282_ = v_isSharedCheck_3294_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_snd_3279_);
lean_inc(v_fst_3278_);
lean_dec(v_head_3276_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3294_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
double v___x_3283_; double v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3287_; 
v___x_3283_ = lean_unbox_float(v_snd_3279_);
lean_dec(v_snd_3279_);
v___x_3284_ = lean_float_mul(v___x_3283_, v_fst_3273_);
v___x_3285_ = lean_box_float(v___x_3284_);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 1, v_fst_3278_);
lean_ctor_set(v___x_3281_, 0, v___x_3285_);
v___x_3287_ = v___x_3281_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v___x_3285_);
lean_ctor_set(v_reuseFailAlloc_3293_, 1, v_fst_3278_);
v___x_3287_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
uint8_t v___x_3288_; 
v___x_3288_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg(v___x_3287_, v_x_3274_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = lean_box(0);
v___x_3290_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(v___x_3287_, v___x_3289_, v_x_3274_);
v_x_3274_ = v___x_3290_;
v_x_3275_ = v_tail_3277_;
goto _start;
}
else
{
lean_dec_ref(v___x_3287_);
v_x_3275_ = v_tail_3277_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__4___boxed(lean_object* v_fst_3295_, lean_object* v_x_3296_, lean_object* v_x_3297_){
_start:
{
double v_fst_11428__boxed_3298_; lean_object* v_res_3299_; 
v_fst_11428__boxed_3298_ = lean_unbox_float(v_fst_3295_);
lean_dec_ref(v_fst_3295_);
v_res_3299_ = l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__4(v_fst_11428__boxed_3298_, v_x_3296_, v_x_3297_);
return v_res_3299_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__1(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__0));
v___x_3302_ = l_Lean_stringToMessageData(v___x_3301_);
return v___x_3302_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__3(void){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__2));
v___x_3305_ = l_Lean_stringToMessageData(v___x_3304_);
return v___x_3305_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__5(void){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__4));
v___x_3308_ = l_Lean_stringToMessageData(v___x_3307_);
return v___x_3308_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__7(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__6));
v___x_3311_ = l_Lean_stringToMessageData(v___x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go(lean_object* v_maxSuggestions_3312_, double v_depthFactor_3313_, double v_frequencyWeight_3314_, lean_object* v_denyList_3315_, lean_object* v_pastTriggers_3316_, lean_object* v_triggerQueue_3317_, lean_object* v_acceptedTheorems_3318_, lean_object* v_queuedTheorems_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_){
_start:
{
lean_object* v___y_3326_; lean_object* v___y_3327_; double v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v_fst_3333_; lean_object* v_snd_3334_; lean_object* v___y_3341_; lean_object* v___y_3342_; double v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___x_3408_; uint8_t v___x_3409_; 
v___x_3408_ = lean_array_get_size(v_acceptedTheorems_3318_);
v___x_3409_ = lean_nat_dec_le(v_maxSuggestions_3312_, v___x_3408_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3410_; 
v___x_3410_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_triggerQueue_3317_);
if (lean_obj_tag(v___x_3410_) == 0)
{
v___y_3361_ = v_a_3320_;
v___y_3362_ = v_a_3321_;
v___y_3363_ = v_a_3322_;
v___y_3364_ = v_a_3323_;
goto v___jp_3360_;
}
else
{
lean_object* v_val_3411_; lean_object* v_fst_3412_; lean_object* v_snd_3413_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___x_3479_; 
v_val_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_val_3411_);
lean_dec_ref(v___x_3410_);
v_fst_3412_ = lean_ctor_get(v_val_3411_, 0);
lean_inc(v_fst_3412_);
v_snd_3413_ = lean_ctor_get(v_val_3411_, 1);
v___x_3479_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queuedTheorems_3319_);
if (lean_obj_tag(v___x_3479_) == 0)
{
goto v___jp_3433_;
}
else
{
lean_object* v_val_3480_; lean_object* v_fst_3481_; double v___x_3482_; double v___x_3483_; uint8_t v___x_3484_; 
v_val_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_val_3480_);
lean_dec_ref(v___x_3479_);
v_fst_3481_ = lean_ctor_get(v_val_3480_, 0);
lean_inc(v_fst_3481_);
lean_dec(v_val_3480_);
v___x_3482_ = lean_unbox_float(v_fst_3412_);
v___x_3483_ = lean_unbox_float(v_fst_3481_);
lean_dec(v_fst_3481_);
v___x_3484_ = lean_float_decLt(v___x_3482_, v___x_3483_);
if (v___x_3484_ == 0)
{
lean_dec(v_fst_3412_);
lean_dec(v_val_3411_);
v___y_3361_ = v_a_3320_;
v___y_3362_ = v_a_3321_;
v___y_3363_ = v_a_3322_;
v___y_3364_ = v_a_3323_;
goto v___jp_3360_;
}
else
{
goto v___jp_3433_;
}
}
v___jp_3414_:
{
lean_object* v___x_3419_; 
v___x_3419_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___redArg(v_snd_3413_, v___y_3418_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3421_; double v___x_3422_; lean_object* v___x_3423_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_a_3420_);
lean_dec_ref(v___x_3419_);
v___x_3421_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v_val_3411_, v_triggerQueue_3317_);
lean_dec(v_val_3411_);
v___x_3422_ = lean_unbox_float(v_fst_3412_);
lean_dec(v_fst_3412_);
v___x_3423_ = l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__4(v___x_3422_, v_queuedTheorems_3319_, v_a_3420_);
v_triggerQueue_3317_ = v___x_3421_;
v_queuedTheorems_3319_ = v___x_3423_;
v_a_3320_ = v___y_3415_;
v_a_3321_ = v___y_3416_;
v_a_3322_ = v___y_3417_;
v_a_3323_ = v___y_3418_;
goto _start;
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v_fst_3412_);
lean_dec(v_val_3411_);
lean_dec(v_queuedTheorems_3319_);
lean_dec_ref(v_acceptedTheorems_3318_);
lean_dec(v_triggerQueue_3317_);
lean_dec(v_pastTriggers_3316_);
v_a_3425_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3419_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3419_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
v___jp_3433_:
{
lean_object* v_cls_3434_; lean_object* v___x_3435_; 
v_cls_3434_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_));
v___x_3435_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg(v_cls_3434_, v_a_3322_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; uint8_t v___x_3437_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_a_3436_);
lean_dec_ref(v___x_3435_);
v___x_3437_ = lean_unbox(v_a_3436_);
lean_dec(v_a_3436_);
if (v___x_3437_ == 0)
{
v___y_3415_ = v_a_3320_;
v___y_3416_ = v_a_3321_;
v___y_3417_ = v_a_3322_;
v___y_3418_ = v_a_3323_;
goto v___jp_3414_;
}
else
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3438_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__1, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__1_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__1);
lean_inc_ref(v_acceptedTheorems_3318_);
v___x_3439_ = lean_array_to_list(v_acceptedTheorems_3318_);
v___x_3440_ = lean_box(0);
v___x_3441_ = l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6(v___x_3439_, v___x_3440_);
v___x_3442_ = l_Lean_MessageData_ofList(v___x_3441_);
v___x_3443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3438_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
v___x_3444_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__3, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__3_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__3);
v___x_3445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3443_);
lean_ctor_set(v___x_3445_, 1, v___x_3444_);
v___x_3446_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__7(v___x_3440_, v_pastTriggers_3316_);
v___x_3447_ = l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__8(v___x_3446_, v___x_3440_);
v___x_3448_ = l_Lean_MessageData_ofList(v___x_3447_);
v___x_3449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3445_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v___x_3450_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__5, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__5_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__5);
v___x_3451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3449_);
lean_ctor_set(v___x_3451_, 1, v___x_3450_);
v___x_3452_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9(v___x_3440_, v_triggerQueue_3317_);
v___x_3453_ = l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10(v___x_3452_, v___x_3440_);
v___x_3454_ = l_Lean_MessageData_ofList(v___x_3453_);
v___x_3455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3451_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
v___x_3456_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__7, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__7_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__7);
v___x_3457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3455_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
v___x_3458_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9(v___x_3440_, v_queuedTheorems_3319_);
v___x_3459_ = l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10(v___x_3458_, v___x_3440_);
v___x_3460_ = l_Lean_MessageData_ofList(v___x_3459_);
v___x_3461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3457_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
v___x_3462_ = l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11(v_cls_3434_, v___x_3461_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_dec_ref(v___x_3462_);
v___y_3415_ = v_a_3320_;
v___y_3416_ = v_a_3321_;
v___y_3417_ = v_a_3322_;
v___y_3418_ = v_a_3323_;
goto v___jp_3414_;
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_dec(v_fst_3412_);
lean_dec(v_val_3411_);
lean_dec(v_a_3323_);
lean_dec_ref(v_a_3322_);
lean_dec(v_a_3321_);
lean_dec_ref(v_a_3320_);
lean_dec(v_queuedTheorems_3319_);
lean_dec_ref(v_acceptedTheorems_3318_);
lean_dec(v_triggerQueue_3317_);
lean_dec(v_pastTriggers_3316_);
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3462_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec(v_fst_3412_);
lean_dec(v_val_3411_);
lean_dec(v_a_3323_);
lean_dec_ref(v_a_3322_);
lean_dec(v_a_3321_);
lean_dec_ref(v_a_3320_);
lean_dec(v_queuedTheorems_3319_);
lean_dec_ref(v_acceptedTheorems_3318_);
lean_dec(v_triggerQueue_3317_);
lean_dec(v_pastTriggers_3316_);
v_a_3471_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3435_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3435_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
}
}
else
{
lean_object* v___x_3485_; 
lean_dec(v_a_3323_);
lean_dec_ref(v_a_3322_);
lean_dec(v_a_3321_);
lean_dec_ref(v_a_3320_);
lean_dec(v_queuedTheorems_3319_);
lean_dec(v_triggerQueue_3317_);
lean_dec(v_pastTriggers_3316_);
v___x_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3485_, 0, v_acceptedTheorems_3318_);
return v___x_3485_;
}
v___jp_3325_:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3335_ = lean_box_float(v___y_3328_);
v___x_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___y_3327_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
v___x_3337_ = lean_array_push(v_acceptedTheorems_3318_, v___x_3336_);
v___x_3338_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v___y_3329_, v_queuedTheorems_3319_);
lean_dec_ref(v___y_3329_);
v_pastTriggers_3316_ = v_fst_3333_;
v_triggerQueue_3317_ = v_snd_3334_;
v_acceptedTheorems_3318_ = v___x_3337_;
v_queuedTheorems_3319_ = v___x_3338_;
v_a_3320_ = v___y_3326_;
v_a_3321_ = v___y_3331_;
v_a_3322_ = v___y_3332_;
v_a_3323_ = v___y_3330_;
goto _start;
}
v___jp_3340_:
{
if (lean_obj_tag(v___y_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v_fst_3350_; lean_object* v_snd_3351_; 
v_a_3349_ = lean_ctor_get(v___y_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref(v___y_3348_);
v_fst_3350_ = lean_ctor_get(v_a_3349_, 0);
lean_inc(v_fst_3350_);
v_snd_3351_ = lean_ctor_get(v_a_3349_, 1);
lean_inc(v_snd_3351_);
lean_dec(v_a_3349_);
v___y_3326_ = v___y_3341_;
v___y_3327_ = v___y_3342_;
v___y_3328_ = v___y_3343_;
v___y_3329_ = v___y_3344_;
v___y_3330_ = v___y_3345_;
v___y_3331_ = v___y_3346_;
v___y_3332_ = v___y_3347_;
v_fst_3333_ = v_fst_3350_;
v_snd_3334_ = v_snd_3351_;
goto v___jp_3325_;
}
else
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v_queuedTheorems_3319_);
lean_dec_ref(v_acceptedTheorems_3318_);
v_a_3352_ = lean_ctor_get(v___y_3348_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___y_3348_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___y_3348_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___y_3348_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
}
v___jp_3360_:
{
lean_object* v___x_3365_; 
v___x_3365_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queuedTheorems_3319_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v___x_3366_; 
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v_queuedTheorems_3319_);
lean_dec(v_triggerQueue_3317_);
lean_dec(v_pastTriggers_3316_);
v___x_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3366_, 0, v_acceptedTheorems_3318_);
return v___x_3366_;
}
else
{
lean_object* v_val_3367_; lean_object* v_fst_3368_; lean_object* v_snd_3369_; lean_object* v___x_3370_; 
v_val_3367_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_val_3367_);
lean_dec_ref(v___x_3365_);
v_fst_3368_ = lean_ctor_get(v_val_3367_, 0);
v_snd_3369_ = lean_ctor_get(v_val_3367_, 1);
lean_inc(v_snd_3369_);
lean_inc_ref(v___y_3363_);
lean_inc(v_snd_3369_);
v___x_3370_ = l_Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0(v_snd_3369_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3371_);
lean_dec_ref(v___x_3370_);
v___x_3372_ = l_Lean_ConstantInfo_type(v_a_3371_);
lean_dec(v_a_3371_);
lean_inc(v___y_3364_);
lean_inc_ref(v___y_3363_);
lean_inc(v___y_3362_);
lean_inc_ref(v___y_3361_);
v___x_3373_ = l_Lean_Expr_relevantConstants(v___x_3372_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; uint8_t v___x_3377_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_a_3374_);
lean_dec_ref(v___x_3373_);
v___x_3375_ = lean_unsigned_to_nat(0u);
v___x_3376_ = lean_array_get_size(v_a_3374_);
v___x_3377_ = lean_nat_dec_lt(v___x_3375_, v___x_3376_);
if (v___x_3377_ == 0)
{
double v___x_3378_; 
lean_dec(v_a_3374_);
v___x_3378_ = lean_unbox_float(v_fst_3368_);
v___y_3326_ = v___y_3361_;
v___y_3327_ = v_snd_3369_;
v___y_3328_ = v___x_3378_;
v___y_3329_ = v_val_3367_;
v___y_3330_ = v___y_3364_;
v___y_3331_ = v___y_3362_;
v___y_3332_ = v___y_3363_;
v_fst_3333_ = v_pastTriggers_3316_;
v_snd_3334_ = v_triggerQueue_3317_;
goto v___jp_3325_;
}
else
{
lean_object* v___x_3379_; uint8_t v___x_3380_; 
lean_inc(v_triggerQueue_3317_);
lean_inc(v_pastTriggers_3316_);
v___x_3379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3379_, 0, v_pastTriggers_3316_);
lean_ctor_set(v___x_3379_, 1, v_triggerQueue_3317_);
v___x_3380_ = lean_nat_dec_le(v___x_3376_, v___x_3376_);
if (v___x_3380_ == 0)
{
if (v___x_3377_ == 0)
{
double v___x_3381_; 
lean_dec_ref(v___x_3379_);
lean_dec(v_a_3374_);
v___x_3381_ = lean_unbox_float(v_fst_3368_);
v___y_3326_ = v___y_3361_;
v___y_3327_ = v_snd_3369_;
v___y_3328_ = v___x_3381_;
v___y_3329_ = v_val_3367_;
v___y_3330_ = v___y_3364_;
v___y_3331_ = v___y_3362_;
v___y_3332_ = v___y_3363_;
v_fst_3333_ = v_pastTriggers_3316_;
v_snd_3334_ = v_triggerQueue_3317_;
goto v___jp_3325_;
}
else
{
size_t v___x_3382_; size_t v___x_3383_; double v___x_3384_; lean_object* v___x_3385_; double v___x_3386_; 
lean_dec(v_triggerQueue_3317_);
lean_dec(v_pastTriggers_3316_);
v___x_3382_ = ((size_t)0ULL);
v___x_3383_ = lean_usize_of_nat(v___x_3376_);
v___x_3384_ = lean_unbox_float(v_fst_3368_);
v___x_3385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg(v_frequencyWeight_3314_, v___x_3384_, v_depthFactor_3313_, v_denyList_3315_, v_a_3374_, v___x_3382_, v___x_3383_, v___x_3379_, v___y_3364_);
lean_dec(v_a_3374_);
v___x_3386_ = lean_unbox_float(v_fst_3368_);
v___y_3341_ = v___y_3361_;
v___y_3342_ = v_snd_3369_;
v___y_3343_ = v___x_3386_;
v___y_3344_ = v_val_3367_;
v___y_3345_ = v___y_3364_;
v___y_3346_ = v___y_3362_;
v___y_3347_ = v___y_3363_;
v___y_3348_ = v___x_3385_;
goto v___jp_3340_;
}
}
else
{
size_t v___x_3387_; size_t v___x_3388_; double v___x_3389_; lean_object* v___x_3390_; double v___x_3391_; 
lean_dec(v_triggerQueue_3317_);
lean_dec(v_pastTriggers_3316_);
v___x_3387_ = ((size_t)0ULL);
v___x_3388_ = lean_usize_of_nat(v___x_3376_);
v___x_3389_ = lean_unbox_float(v_fst_3368_);
v___x_3390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg(v_frequencyWeight_3314_, v___x_3389_, v_depthFactor_3313_, v_denyList_3315_, v_a_3374_, v___x_3387_, v___x_3388_, v___x_3379_, v___y_3364_);
lean_dec(v_a_3374_);
v___x_3391_ = lean_unbox_float(v_fst_3368_);
v___y_3341_ = v___y_3361_;
v___y_3342_ = v_snd_3369_;
v___y_3343_ = v___x_3391_;
v___y_3344_ = v_val_3367_;
v___y_3345_ = v___y_3364_;
v___y_3346_ = v___y_3362_;
v___y_3347_ = v___y_3363_;
v___y_3348_ = v___x_3390_;
goto v___jp_3340_;
}
}
}
else
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_dec(v_snd_3369_);
lean_dec(v_val_3367_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v_queuedTheorems_3319_);
lean_dec_ref(v_acceptedTheorems_3318_);
lean_dec(v_triggerQueue_3317_);
lean_dec(v_pastTriggers_3316_);
v_a_3392_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3373_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3373_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec(v_snd_3369_);
lean_dec(v_val_3367_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v_queuedTheorems_3319_);
lean_dec_ref(v_acceptedTheorems_3318_);
lean_dec(v_triggerQueue_3317_);
lean_dec(v_pastTriggers_3316_);
v_a_3400_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3370_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3370_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___boxed(lean_object* v_maxSuggestions_3486_, lean_object* v_depthFactor_3487_, lean_object* v_frequencyWeight_3488_, lean_object* v_denyList_3489_, lean_object* v_pastTriggers_3490_, lean_object* v_triggerQueue_3491_, lean_object* v_acceptedTheorems_3492_, lean_object* v_queuedTheorems_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_){
_start:
{
double v_depthFactor_boxed_3499_; double v_frequencyWeight_boxed_3500_; lean_object* v_res_3501_; 
v_depthFactor_boxed_3499_ = lean_unbox_float(v_depthFactor_3487_);
lean_dec_ref(v_depthFactor_3487_);
v_frequencyWeight_boxed_3500_ = lean_unbox_float(v_frequencyWeight_3488_);
lean_dec_ref(v_frequencyWeight_3488_);
v_res_3501_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go(v_maxSuggestions_3486_, v_depthFactor_boxed_3499_, v_frequencyWeight_boxed_3500_, v_denyList_3489_, v_pastTriggers_3490_, v_triggerQueue_3491_, v_acceptedTheorems_3492_, v_queuedTheorems_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
lean_dec(v_denyList_3489_);
lean_dec(v_maxSuggestions_3486_);
return v_res_3501_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0(lean_object* v_00_u03b2_3502_, lean_object* v_k_3503_, lean_object* v_t_3504_){
_start:
{
uint8_t v___x_3505_; 
v___x_3505_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg(v_k_3503_, v_t_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___boxed(lean_object* v_00_u03b2_3506_, lean_object* v_k_3507_, lean_object* v_t_3508_){
_start:
{
uint8_t v_res_3509_; lean_object* v_r_3510_; 
v_res_3509_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0(v_00_u03b2_3506_, v_k_3507_, v_t_3508_);
lean_dec(v_t_3508_);
lean_dec_ref(v_k_3507_);
v_r_3510_ = lean_box(v_res_3509_);
return v_r_3510_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1(lean_object* v_00_u03b2_3511_, lean_object* v_k_3512_, lean_object* v_v_3513_, lean_object* v_t_3514_, lean_object* v_hl_3515_){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(v_k_3512_, v_v_3513_, v_t_3514_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2(lean_object* v_00_u03b2_3517_, lean_object* v_k_3518_, lean_object* v_t_3519_, lean_object* v_h_3520_){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v_k_3518_, v_t_3519_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___boxed(lean_object* v_00_u03b2_3522_, lean_object* v_k_3523_, lean_object* v_t_3524_, lean_object* v_h_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2(v_00_u03b2_3522_, v_k_3523_, v_t_3524_, v_h_3525_);
lean_dec_ref(v_k_3523_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3(double v_frequencyWeight_3527_, double v_fst_3528_, double v_depthFactor_3529_, lean_object* v_denyList_3530_, lean_object* v_as_3531_, size_t v_i_3532_, size_t v_stop_3533_, lean_object* v_b_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg(v_frequencyWeight_3527_, v_fst_3528_, v_depthFactor_3529_, v_denyList_3530_, v_as_3531_, v_i_3532_, v_stop_3533_, v_b_3534_, v___y_3538_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___boxed(lean_object* v_frequencyWeight_3541_, lean_object* v_fst_3542_, lean_object* v_depthFactor_3543_, lean_object* v_denyList_3544_, lean_object* v_as_3545_, lean_object* v_i_3546_, lean_object* v_stop_3547_, lean_object* v_b_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
double v_frequencyWeight_boxed_3554_; double v_fst_11856__boxed_3555_; double v_depthFactor_boxed_3556_; size_t v_i_boxed_3557_; size_t v_stop_boxed_3558_; lean_object* v_res_3559_; 
v_frequencyWeight_boxed_3554_ = lean_unbox_float(v_frequencyWeight_3541_);
lean_dec_ref(v_frequencyWeight_3541_);
v_fst_11856__boxed_3555_ = lean_unbox_float(v_fst_3542_);
lean_dec_ref(v_fst_3542_);
v_depthFactor_boxed_3556_ = lean_unbox_float(v_depthFactor_3543_);
lean_dec_ref(v_depthFactor_3543_);
v_i_boxed_3557_ = lean_unbox_usize(v_i_3546_);
lean_dec(v_i_3546_);
v_stop_boxed_3558_ = lean_unbox_usize(v_stop_3547_);
lean_dec(v_stop_3547_);
v_res_3559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3(v_frequencyWeight_boxed_3554_, v_fst_11856__boxed_3555_, v_depthFactor_boxed_3556_, v_denyList_3544_, v_as_3545_, v_i_boxed_3557_, v_stop_boxed_3558_, v_b_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec_ref(v_as_3545_);
lean_dec(v_denyList_3544_);
return v_res_3559_;
}
}
static double _init_l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3560_; uint8_t v___x_3561_; lean_object* v___x_3562_; double v___x_3563_; 
v___x_3560_ = lean_unsigned_to_nat(2u);
v___x_3561_ = 1;
v___x_3562_ = lean_unsigned_to_nat(1u);
v___x_3563_ = l_Float_ofScientific(v___x_3562_, v___x_3561_, v___x_3560_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg(lean_object* v_x_3564_, lean_object* v_x_3565_, lean_object* v___y_3566_){
_start:
{
if (lean_obj_tag(v_x_3564_) == 0)
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = l_List_reverse___redArg(v_x_3565_);
v___x_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3568_);
return v___x_3569_;
}
else
{
lean_object* v_head_3570_; lean_object* v_tail_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3591_; 
v_head_3570_ = lean_ctor_get(v_x_3564_, 0);
v_tail_3571_ = lean_ctor_get(v_x_3564_, 1);
v_isSharedCheck_3591_ = !lean_is_exclusive(v_x_3564_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3573_ = v_x_3564_;
v_isShared_3574_ = v_isSharedCheck_3591_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_tail_3571_);
lean_inc(v_head_3570_);
lean_dec(v_x_3564_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3591_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
double v___x_3575_; lean_object* v___x_3576_; 
v___x_3575_ = lean_float_once(&l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0, &l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0_once, _init_l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0);
v___x_3576_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg(v_head_3570_, v___x_3575_, v___y_3566_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_a_3577_; lean_object* v___x_3578_; lean_object* v___x_3580_; 
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_a_3577_);
lean_dec_ref(v___x_3576_);
v___x_3578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3578_, 0, v_a_3577_);
lean_ctor_set(v___x_3578_, 1, v_head_3570_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 1, v_x_3565_);
lean_ctor_set(v___x_3573_, 0, v___x_3578_);
v___x_3580_ = v___x_3573_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3578_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v_x_3565_);
v___x_3580_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
v_x_3564_ = v_tail_3571_;
v_x_3565_ = v___x_3580_;
goto _start;
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_del_object(v___x_3573_);
lean_dec(v_tail_3571_);
lean_dec(v_head_3570_);
lean_dec(v_x_3565_);
v_a_3583_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3576_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3576_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___boxed(lean_object* v_x_3592_, lean_object* v_x_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg(v_x_3592_, v_x_3593_, v___y_3594_);
lean_dec(v___y_3594_);
return v_res_3596_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3597_; double v___x_3598_; 
v___x_3597_ = lean_unsigned_to_nat(1u);
v___x_3598_ = lean_float_of_nat(v___x_3597_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3(size_t v_sz_3599_, size_t v_i_3600_, lean_object* v_bs_3601_){
_start:
{
uint8_t v___x_3602_; 
v___x_3602_ = lean_usize_dec_lt(v_i_3600_, v_sz_3599_);
if (v___x_3602_ == 0)
{
return v_bs_3601_;
}
else
{
lean_object* v_v_3603_; lean_object* v_fst_3604_; lean_object* v_snd_3605_; lean_object* v___x_3606_; lean_object* v_bs_x27_3607_; double v___x_3608_; double v___x_3609_; double v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; size_t v___x_3613_; size_t v___x_3614_; lean_object* v___x_3615_; 
v_v_3603_ = lean_array_uget_borrowed(v_bs_3601_, v_i_3600_);
v_fst_3604_ = lean_ctor_get(v_v_3603_, 0);
lean_inc(v_fst_3604_);
v_snd_3605_ = lean_ctor_get(v_v_3603_, 1);
lean_inc(v_snd_3605_);
v___x_3606_ = lean_unsigned_to_nat(0u);
v_bs_x27_3607_ = lean_array_uset(v_bs_3601_, v_i_3600_, v___x_3606_);
v___x_3608_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___closed__0);
v___x_3609_ = lean_unbox_float(v_snd_3605_);
lean_dec(v_snd_3605_);
v___x_3610_ = lean_float_div(v___x_3608_, v___x_3609_);
v___x_3611_ = lean_box(0);
v___x_3612_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3612_, 0, v_fst_3604_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
lean_ctor_set_float(v___x_3612_, sizeof(void*)*2, v___x_3610_);
v___x_3613_ = ((size_t)1ULL);
v___x_3614_ = lean_usize_add(v_i_3600_, v___x_3613_);
v___x_3615_ = lean_array_uset(v_bs_x27_3607_, v_i_3600_, v___x_3612_);
v_i_3600_ = v___x_3614_;
v_bs_3601_ = v___x_3615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___boxed(lean_object* v_sz_3617_, lean_object* v_i_3618_, lean_object* v_bs_3619_){
_start:
{
size_t v_sz_boxed_3620_; size_t v_i_boxed_3621_; lean_object* v_res_3622_; 
v_sz_boxed_3620_ = lean_unbox_usize(v_sz_3617_);
lean_dec(v_sz_3617_);
v_i_boxed_3621_ = lean_unbox_usize(v_i_3618_);
lean_dec(v_i_3618_);
v_res_3622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3(v_sz_boxed_3620_, v_i_boxed_3621_, v_bs_3619_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(lean_object* v_k_3623_, lean_object* v_t_3624_){
_start:
{
if (lean_obj_tag(v_t_3624_) == 0)
{
lean_object* v_k_3625_; lean_object* v_v_3626_; lean_object* v_l_3627_; lean_object* v_r_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_4282_; 
v_k_3625_ = lean_ctor_get(v_t_3624_, 1);
v_v_3626_ = lean_ctor_get(v_t_3624_, 2);
v_l_3627_ = lean_ctor_get(v_t_3624_, 3);
v_r_3628_ = lean_ctor_get(v_t_3624_, 4);
v_isSharedCheck_4282_ = !lean_is_exclusive(v_t_3624_);
if (v_isSharedCheck_4282_ == 0)
{
lean_object* v_unused_4283_; 
v_unused_4283_ = lean_ctor_get(v_t_3624_, 0);
lean_dec(v_unused_4283_);
v___x_3630_ = v_t_3624_;
v_isShared_3631_ = v_isSharedCheck_4282_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_r_3628_);
lean_inc(v_l_3627_);
lean_inc(v_v_3626_);
lean_inc(v_k_3625_);
lean_dec(v_t_3624_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_4282_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
uint8_t v___x_3632_; 
v___x_3632_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3623_, v_k_3625_);
switch(v___x_3632_)
{
case 0:
{
lean_object* v_impl_3633_; lean_object* v___x_3634_; 
v_impl_3633_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(v_k_3623_, v_l_3627_);
v___x_3634_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3633_) == 0)
{
if (lean_obj_tag(v_r_3628_) == 0)
{
lean_object* v_size_3635_; lean_object* v_size_3636_; lean_object* v_k_3637_; lean_object* v_v_3638_; lean_object* v_l_3639_; lean_object* v_r_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; uint8_t v___x_3643_; 
v_size_3635_ = lean_ctor_get(v_impl_3633_, 0);
lean_inc(v_size_3635_);
v_size_3636_ = lean_ctor_get(v_r_3628_, 0);
v_k_3637_ = lean_ctor_get(v_r_3628_, 1);
v_v_3638_ = lean_ctor_get(v_r_3628_, 2);
v_l_3639_ = lean_ctor_get(v_r_3628_, 3);
lean_inc(v_l_3639_);
v_r_3640_ = lean_ctor_get(v_r_3628_, 4);
v___x_3641_ = lean_unsigned_to_nat(3u);
v___x_3642_ = lean_nat_mul(v___x_3641_, v_size_3635_);
v___x_3643_ = lean_nat_dec_lt(v___x_3642_, v_size_3636_);
lean_dec(v___x_3642_);
if (v___x_3643_ == 0)
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3647_; 
lean_dec(v_l_3639_);
v___x_3644_ = lean_nat_add(v___x_3634_, v_size_3635_);
lean_dec(v_size_3635_);
v___x_3645_ = lean_nat_add(v___x_3644_, v_size_3636_);
lean_dec(v___x_3644_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 3, v_impl_3633_);
lean_ctor_set(v___x_3630_, 0, v___x_3645_);
v___x_3647_ = v___x_3630_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3645_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_3648_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_3648_, 3, v_impl_3633_);
lean_ctor_set(v_reuseFailAlloc_3648_, 4, v_r_3628_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
else
{
lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3712_; 
lean_inc(v_r_3640_);
lean_inc(v_v_3638_);
lean_inc(v_k_3637_);
lean_inc(v_size_3636_);
v_isSharedCheck_3712_ = !lean_is_exclusive(v_r_3628_);
if (v_isSharedCheck_3712_ == 0)
{
lean_object* v_unused_3713_; lean_object* v_unused_3714_; lean_object* v_unused_3715_; lean_object* v_unused_3716_; lean_object* v_unused_3717_; 
v_unused_3713_ = lean_ctor_get(v_r_3628_, 4);
lean_dec(v_unused_3713_);
v_unused_3714_ = lean_ctor_get(v_r_3628_, 3);
lean_dec(v_unused_3714_);
v_unused_3715_ = lean_ctor_get(v_r_3628_, 2);
lean_dec(v_unused_3715_);
v_unused_3716_ = lean_ctor_get(v_r_3628_, 1);
lean_dec(v_unused_3716_);
v_unused_3717_ = lean_ctor_get(v_r_3628_, 0);
lean_dec(v_unused_3717_);
v___x_3650_ = v_r_3628_;
v_isShared_3651_ = v_isSharedCheck_3712_;
goto v_resetjp_3649_;
}
else
{
lean_dec(v_r_3628_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3712_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v_size_3652_; lean_object* v_k_3653_; lean_object* v_v_3654_; lean_object* v_l_3655_; lean_object* v_r_3656_; lean_object* v_size_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; uint8_t v___x_3660_; 
v_size_3652_ = lean_ctor_get(v_l_3639_, 0);
v_k_3653_ = lean_ctor_get(v_l_3639_, 1);
v_v_3654_ = lean_ctor_get(v_l_3639_, 2);
v_l_3655_ = lean_ctor_get(v_l_3639_, 3);
v_r_3656_ = lean_ctor_get(v_l_3639_, 4);
v_size_3657_ = lean_ctor_get(v_r_3640_, 0);
v___x_3658_ = lean_unsigned_to_nat(2u);
v___x_3659_ = lean_nat_mul(v___x_3658_, v_size_3657_);
v___x_3660_ = lean_nat_dec_lt(v_size_3652_, v___x_3659_);
lean_dec(v___x_3659_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3688_; 
lean_inc(v_r_3656_);
lean_inc(v_l_3655_);
lean_inc(v_v_3654_);
lean_inc(v_k_3653_);
v_isSharedCheck_3688_ = !lean_is_exclusive(v_l_3639_);
if (v_isSharedCheck_3688_ == 0)
{
lean_object* v_unused_3689_; lean_object* v_unused_3690_; lean_object* v_unused_3691_; lean_object* v_unused_3692_; lean_object* v_unused_3693_; 
v_unused_3689_ = lean_ctor_get(v_l_3639_, 4);
lean_dec(v_unused_3689_);
v_unused_3690_ = lean_ctor_get(v_l_3639_, 3);
lean_dec(v_unused_3690_);
v_unused_3691_ = lean_ctor_get(v_l_3639_, 2);
lean_dec(v_unused_3691_);
v_unused_3692_ = lean_ctor_get(v_l_3639_, 1);
lean_dec(v_unused_3692_);
v_unused_3693_ = lean_ctor_get(v_l_3639_, 0);
lean_dec(v_unused_3693_);
v___x_3662_ = v_l_3639_;
v_isShared_3663_ = v_isSharedCheck_3688_;
goto v_resetjp_3661_;
}
else
{
lean_dec(v_l_3639_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3688_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3678_; 
v___x_3664_ = lean_nat_add(v___x_3634_, v_size_3635_);
lean_dec(v_size_3635_);
v___x_3665_ = lean_nat_add(v___x_3664_, v_size_3636_);
lean_dec(v_size_3636_);
if (lean_obj_tag(v_l_3655_) == 0)
{
lean_object* v_size_3686_; 
v_size_3686_ = lean_ctor_get(v_l_3655_, 0);
lean_inc(v_size_3686_);
v___y_3678_ = v_size_3686_;
goto v___jp_3677_;
}
else
{
lean_object* v___x_3687_; 
v___x_3687_ = lean_unsigned_to_nat(0u);
v___y_3678_ = v___x_3687_;
goto v___jp_3677_;
}
v___jp_3666_:
{
lean_object* v___x_3670_; lean_object* v___x_3672_; 
v___x_3670_ = lean_nat_add(v___y_3667_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec(v___y_3667_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v_r_3640_);
lean_ctor_set(v___x_3662_, 3, v_r_3656_);
lean_ctor_set(v___x_3662_, 2, v_v_3638_);
lean_ctor_set(v___x_3662_, 1, v_k_3637_);
lean_ctor_set(v___x_3662_, 0, v___x_3670_);
v___x_3672_ = v___x_3662_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3670_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_k_3637_);
lean_ctor_set(v_reuseFailAlloc_3676_, 2, v_v_3638_);
lean_ctor_set(v_reuseFailAlloc_3676_, 3, v_r_3656_);
lean_ctor_set(v_reuseFailAlloc_3676_, 4, v_r_3640_);
v___x_3672_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3674_; 
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 4, v___x_3672_);
lean_ctor_set(v___x_3650_, 3, v___y_3668_);
lean_ctor_set(v___x_3650_, 2, v_v_3654_);
lean_ctor_set(v___x_3650_, 1, v_k_3653_);
lean_ctor_set(v___x_3650_, 0, v___x_3665_);
v___x_3674_ = v___x_3650_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3665_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_k_3653_);
lean_ctor_set(v_reuseFailAlloc_3675_, 2, v_v_3654_);
lean_ctor_set(v_reuseFailAlloc_3675_, 3, v___y_3668_);
lean_ctor_set(v_reuseFailAlloc_3675_, 4, v___x_3672_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
v___jp_3677_:
{
lean_object* v___x_3679_; lean_object* v___x_3681_; 
v___x_3679_ = lean_nat_add(v___x_3664_, v___y_3678_);
lean_dec(v___y_3678_);
lean_dec(v___x_3664_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 4, v_l_3655_);
lean_ctor_set(v___x_3630_, 3, v_impl_3633_);
lean_ctor_set(v___x_3630_, 0, v___x_3679_);
v___x_3681_ = v___x_3630_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3679_);
lean_ctor_set(v_reuseFailAlloc_3685_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_3685_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_3685_, 3, v_impl_3633_);
lean_ctor_set(v_reuseFailAlloc_3685_, 4, v_l_3655_);
v___x_3681_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
lean_object* v___x_3682_; 
v___x_3682_ = lean_nat_add(v___x_3634_, v_size_3657_);
if (lean_obj_tag(v_r_3656_) == 0)
{
lean_object* v_size_3683_; 
v_size_3683_ = lean_ctor_get(v_r_3656_, 0);
lean_inc(v_size_3683_);
v___y_3667_ = v___x_3682_;
v___y_3668_ = v___x_3681_;
v___y_3669_ = v_size_3683_;
goto v___jp_3666_;
}
else
{
lean_object* v___x_3684_; 
v___x_3684_ = lean_unsigned_to_nat(0u);
v___y_3667_ = v___x_3682_;
v___y_3668_ = v___x_3681_;
v___y_3669_ = v___x_3684_;
goto v___jp_3666_;
}
}
}
}
}
else
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3698_; 
lean_del_object(v___x_3630_);
v___x_3694_ = lean_nat_add(v___x_3634_, v_size_3635_);
lean_dec(v_size_3635_);
v___x_3695_ = lean_nat_add(v___x_3694_, v_size_3636_);
lean_dec(v_size_3636_);
v___x_3696_ = lean_nat_add(v___x_3694_, v_size_3652_);
lean_dec(v___x_3694_);
lean_inc_ref(v_impl_3633_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 4, v_l_3639_);
lean_ctor_set(v___x_3650_, 3, v_impl_3633_);
lean_ctor_set(v___x_3650_, 2, v_v_3626_);
lean_ctor_set(v___x_3650_, 1, v_k_3625_);
lean_ctor_set(v___x_3650_, 0, v___x_3696_);
v___x_3698_ = v___x_3650_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3696_);
lean_ctor_set(v_reuseFailAlloc_3711_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_3711_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_3711_, 3, v_impl_3633_);
lean_ctor_set(v_reuseFailAlloc_3711_, 4, v_l_3639_);
v___x_3698_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
v_isSharedCheck_3705_ = !lean_is_exclusive(v_impl_3633_);
if (v_isSharedCheck_3705_ == 0)
{
lean_object* v_unused_3706_; lean_object* v_unused_3707_; lean_object* v_unused_3708_; lean_object* v_unused_3709_; lean_object* v_unused_3710_; 
v_unused_3706_ = lean_ctor_get(v_impl_3633_, 4);
lean_dec(v_unused_3706_);
v_unused_3707_ = lean_ctor_get(v_impl_3633_, 3);
lean_dec(v_unused_3707_);
v_unused_3708_ = lean_ctor_get(v_impl_3633_, 2);
lean_dec(v_unused_3708_);
v_unused_3709_ = lean_ctor_get(v_impl_3633_, 1);
lean_dec(v_unused_3709_);
v_unused_3710_ = lean_ctor_get(v_impl_3633_, 0);
lean_dec(v_unused_3710_);
v___x_3700_ = v_impl_3633_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_dec(v_impl_3633_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 4, v_r_3640_);
lean_ctor_set(v___x_3700_, 3, v___x_3698_);
lean_ctor_set(v___x_3700_, 2, v_v_3638_);
lean_ctor_set(v___x_3700_, 1, v_k_3637_);
lean_ctor_set(v___x_3700_, 0, v___x_3695_);
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3695_);
lean_ctor_set(v_reuseFailAlloc_3704_, 1, v_k_3637_);
lean_ctor_set(v_reuseFailAlloc_3704_, 2, v_v_3638_);
lean_ctor_set(v_reuseFailAlloc_3704_, 3, v___x_3698_);
lean_ctor_set(v_reuseFailAlloc_3704_, 4, v_r_3640_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3718_; lean_object* v___x_3719_; lean_object* v___x_3721_; 
v_size_3718_ = lean_ctor_get(v_impl_3633_, 0);
lean_inc(v_size_3718_);
v___x_3719_ = lean_nat_add(v___x_3634_, v_size_3718_);
lean_dec(v_size_3718_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 3, v_impl_3633_);
lean_ctor_set(v___x_3630_, 0, v___x_3719_);
v___x_3721_ = v___x_3630_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3722_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_3722_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_3722_, 3, v_impl_3633_);
lean_ctor_set(v_reuseFailAlloc_3722_, 4, v_r_3628_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
else
{
if (lean_obj_tag(v_r_3628_) == 0)
{
lean_object* v_l_3723_; 
v_l_3723_ = lean_ctor_get(v_r_3628_, 3);
lean_inc(v_l_3723_);
if (lean_obj_tag(v_l_3723_) == 0)
{
lean_object* v_r_3724_; 
v_r_3724_ = lean_ctor_get(v_r_3628_, 4);
lean_inc(v_r_3724_);
if (lean_obj_tag(v_r_3724_) == 0)
{
lean_object* v_size_3725_; lean_object* v_k_3726_; lean_object* v_v_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3740_; 
v_size_3725_ = lean_ctor_get(v_r_3628_, 0);
v_k_3726_ = lean_ctor_get(v_r_3628_, 1);
v_v_3727_ = lean_ctor_get(v_r_3628_, 2);
v_isSharedCheck_3740_ = !lean_is_exclusive(v_r_3628_);
if (v_isSharedCheck_3740_ == 0)
{
lean_object* v_unused_3741_; lean_object* v_unused_3742_; 
v_unused_3741_ = lean_ctor_get(v_r_3628_, 4);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_r_3628_, 3);
lean_dec(v_unused_3742_);
v___x_3729_ = v_r_3628_;
v_isShared_3730_ = v_isSharedCheck_3740_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_v_3727_);
lean_inc(v_k_3726_);
lean_inc(v_size_3725_);
lean_dec(v_r_3628_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3740_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v_size_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3735_; 
v_size_3731_ = lean_ctor_get(v_l_3723_, 0);
v___x_3732_ = lean_nat_add(v___x_3634_, v_size_3725_);
lean_dec(v_size_3725_);
v___x_3733_ = lean_nat_add(v___x_3634_, v_size_3731_);
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 4, v_l_3723_);
lean_ctor_set(v___x_3729_, 3, v_impl_3633_);
lean_ctor_set(v___x_3729_, 2, v_v_3626_);
lean_ctor_set(v___x_3729_, 1, v_k_3625_);
lean_ctor_set(v___x_3729_, 0, v___x_3733_);
v___x_3735_ = v___x_3729_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3733_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_3739_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_3739_, 3, v_impl_3633_);
lean_ctor_set(v_reuseFailAlloc_3739_, 4, v_l_3723_);
v___x_3735_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
lean_object* v___x_3737_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 4, v_r_3724_);
lean_ctor_set(v___x_3630_, 3, v___x_3735_);
lean_ctor_set(v___x_3630_, 2, v_v_3727_);
lean_ctor_set(v___x_3630_, 1, v_k_3726_);
lean_ctor_set(v___x_3630_, 0, v___x_3732_);
v___x_3737_ = v___x_3630_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3732_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_k_3726_);
lean_ctor_set(v_reuseFailAlloc_3738_, 2, v_v_3727_);
lean_ctor_set(v_reuseFailAlloc_3738_, 3, v___x_3735_);
lean_ctor_set(v_reuseFailAlloc_3738_, 4, v_r_3724_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
else
{
lean_object* v_k_3743_; lean_object* v_v_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3767_; 
v_k_3743_ = lean_ctor_get(v_r_3628_, 1);
v_v_3744_ = lean_ctor_get(v_r_3628_, 2);
v_isSharedCheck_3767_ = !lean_is_exclusive(v_r_3628_);
if (v_isSharedCheck_3767_ == 0)
{
lean_object* v_unused_3768_; lean_object* v_unused_3769_; lean_object* v_unused_3770_; 
v_unused_3768_ = lean_ctor_get(v_r_3628_, 4);
lean_dec(v_unused_3768_);
v_unused_3769_ = lean_ctor_get(v_r_3628_, 3);
lean_dec(v_unused_3769_);
v_unused_3770_ = lean_ctor_get(v_r_3628_, 0);
lean_dec(v_unused_3770_);
v___x_3746_ = v_r_3628_;
v_isShared_3747_ = v_isSharedCheck_3767_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_v_3744_);
lean_inc(v_k_3743_);
lean_dec(v_r_3628_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3767_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v_k_3748_; lean_object* v_v_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3763_; 
v_k_3748_ = lean_ctor_get(v_l_3723_, 1);
v_v_3749_ = lean_ctor_get(v_l_3723_, 2);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_l_3723_);
if (v_isSharedCheck_3763_ == 0)
{
lean_object* v_unused_3764_; lean_object* v_unused_3765_; lean_object* v_unused_3766_; 
v_unused_3764_ = lean_ctor_get(v_l_3723_, 4);
lean_dec(v_unused_3764_);
v_unused_3765_ = lean_ctor_get(v_l_3723_, 3);
lean_dec(v_unused_3765_);
v_unused_3766_ = lean_ctor_get(v_l_3723_, 0);
lean_dec(v_unused_3766_);
v___x_3751_ = v_l_3723_;
v_isShared_3752_ = v_isSharedCheck_3763_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_v_3749_);
lean_inc(v_k_3748_);
lean_dec(v_l_3723_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3763_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3753_; lean_object* v___x_3755_; 
v___x_3753_ = lean_unsigned_to_nat(3u);
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 4, v_r_3724_);
lean_ctor_set(v___x_3751_, 3, v_r_3724_);
lean_ctor_set(v___x_3751_, 2, v_v_3626_);
lean_ctor_set(v___x_3751_, 1, v_k_3625_);
lean_ctor_set(v___x_3751_, 0, v___x_3634_);
v___x_3755_ = v___x_3751_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_3762_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_3762_, 3, v_r_3724_);
lean_ctor_set(v_reuseFailAlloc_3762_, 4, v_r_3724_);
v___x_3755_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
lean_object* v___x_3757_; 
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 3, v_r_3724_);
lean_ctor_set(v___x_3746_, 0, v___x_3634_);
v___x_3757_ = v___x_3746_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_k_3743_);
lean_ctor_set(v_reuseFailAlloc_3761_, 2, v_v_3744_);
lean_ctor_set(v_reuseFailAlloc_3761_, 3, v_r_3724_);
lean_ctor_set(v_reuseFailAlloc_3761_, 4, v_r_3724_);
v___x_3757_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
lean_object* v___x_3759_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 4, v___x_3757_);
lean_ctor_set(v___x_3630_, 3, v___x_3755_);
lean_ctor_set(v___x_3630_, 2, v_v_3749_);
lean_ctor_set(v___x_3630_, 1, v_k_3748_);
lean_ctor_set(v___x_3630_, 0, v___x_3753_);
v___x_3759_ = v___x_3630_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3753_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v_k_3748_);
lean_ctor_set(v_reuseFailAlloc_3760_, 2, v_v_3749_);
lean_ctor_set(v_reuseFailAlloc_3760_, 3, v___x_3755_);
lean_ctor_set(v_reuseFailAlloc_3760_, 4, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3771_; 
v_r_3771_ = lean_ctor_get(v_r_3628_, 4);
lean_inc(v_r_3771_);
if (lean_obj_tag(v_r_3771_) == 0)
{
lean_object* v_k_3772_; lean_object* v_v_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3784_; 
v_k_3772_ = lean_ctor_get(v_r_3628_, 1);
v_v_3773_ = lean_ctor_get(v_r_3628_, 2);
v_isSharedCheck_3784_ = !lean_is_exclusive(v_r_3628_);
if (v_isSharedCheck_3784_ == 0)
{
lean_object* v_unused_3785_; lean_object* v_unused_3786_; lean_object* v_unused_3787_; 
v_unused_3785_ = lean_ctor_get(v_r_3628_, 4);
lean_dec(v_unused_3785_);
v_unused_3786_ = lean_ctor_get(v_r_3628_, 3);
lean_dec(v_unused_3786_);
v_unused_3787_ = lean_ctor_get(v_r_3628_, 0);
lean_dec(v_unused_3787_);
v___x_3775_ = v_r_3628_;
v_isShared_3776_ = v_isSharedCheck_3784_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_v_3773_);
lean_inc(v_k_3772_);
lean_dec(v_r_3628_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3784_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3777_; lean_object* v___x_3779_; 
v___x_3777_ = lean_unsigned_to_nat(3u);
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 4, v_l_3723_);
lean_ctor_set(v___x_3775_, 2, v_v_3626_);
lean_ctor_set(v___x_3775_, 1, v_k_3625_);
lean_ctor_set(v___x_3775_, 0, v___x_3634_);
v___x_3779_ = v___x_3775_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3783_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_3783_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_3783_, 3, v_l_3723_);
lean_ctor_set(v_reuseFailAlloc_3783_, 4, v_l_3723_);
v___x_3779_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
lean_object* v___x_3781_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 4, v_r_3771_);
lean_ctor_set(v___x_3630_, 3, v___x_3779_);
lean_ctor_set(v___x_3630_, 2, v_v_3773_);
lean_ctor_set(v___x_3630_, 1, v_k_3772_);
lean_ctor_set(v___x_3630_, 0, v___x_3777_);
v___x_3781_ = v___x_3630_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3777_);
lean_ctor_set(v_reuseFailAlloc_3782_, 1, v_k_3772_);
lean_ctor_set(v_reuseFailAlloc_3782_, 2, v_v_3773_);
lean_ctor_set(v_reuseFailAlloc_3782_, 3, v___x_3779_);
lean_ctor_set(v_reuseFailAlloc_3782_, 4, v_r_3771_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
else
{
lean_object* v_size_3788_; lean_object* v_k_3789_; lean_object* v_v_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3801_; 
v_size_3788_ = lean_ctor_get(v_r_3628_, 0);
v_k_3789_ = lean_ctor_get(v_r_3628_, 1);
v_v_3790_ = lean_ctor_get(v_r_3628_, 2);
v_isSharedCheck_3801_ = !lean_is_exclusive(v_r_3628_);
if (v_isSharedCheck_3801_ == 0)
{
lean_object* v_unused_3802_; lean_object* v_unused_3803_; 
v_unused_3802_ = lean_ctor_get(v_r_3628_, 4);
lean_dec(v_unused_3802_);
v_unused_3803_ = lean_ctor_get(v_r_3628_, 3);
lean_dec(v_unused_3803_);
v___x_3792_ = v_r_3628_;
v_isShared_3793_ = v_isSharedCheck_3801_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_v_3790_);
lean_inc(v_k_3789_);
lean_inc(v_size_3788_);
lean_dec(v_r_3628_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3801_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 3, v_r_3771_);
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_size_3788_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v_k_3789_);
lean_ctor_set(v_reuseFailAlloc_3800_, 2, v_v_3790_);
lean_ctor_set(v_reuseFailAlloc_3800_, 3, v_r_3771_);
lean_ctor_set(v_reuseFailAlloc_3800_, 4, v_r_3771_);
v___x_3795_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
lean_object* v___x_3796_; lean_object* v___x_3798_; 
v___x_3796_ = lean_unsigned_to_nat(2u);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 4, v___x_3795_);
lean_ctor_set(v___x_3630_, 3, v_r_3771_);
lean_ctor_set(v___x_3630_, 0, v___x_3796_);
v___x_3798_ = v___x_3630_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3796_);
lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_3799_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_3799_, 3, v_r_3771_);
lean_ctor_set(v_reuseFailAlloc_3799_, 4, v___x_3795_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
}
}
else
{
lean_object* v___x_3805_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 3, v_r_3628_);
lean_ctor_set(v___x_3630_, 0, v___x_3634_);
v___x_3805_ = v___x_3630_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3806_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_3806_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_3806_, 3, v_r_3628_);
lean_ctor_set(v_reuseFailAlloc_3806_, 4, v_r_3628_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3630_);
lean_dec(v_v_3626_);
lean_dec(v_k_3625_);
if (lean_obj_tag(v_l_3627_) == 0)
{
if (lean_obj_tag(v_r_3628_) == 0)
{
lean_object* v_size_3807_; lean_object* v_k_3808_; lean_object* v_v_3809_; lean_object* v_l_3810_; lean_object* v_r_3811_; lean_object* v_size_3812_; lean_object* v_k_3813_; lean_object* v_v_3814_; lean_object* v_l_3815_; lean_object* v_r_3816_; lean_object* v___x_3817_; uint8_t v___x_3818_; 
v_size_3807_ = lean_ctor_get(v_l_3627_, 0);
v_k_3808_ = lean_ctor_get(v_l_3627_, 1);
v_v_3809_ = lean_ctor_get(v_l_3627_, 2);
v_l_3810_ = lean_ctor_get(v_l_3627_, 3);
v_r_3811_ = lean_ctor_get(v_l_3627_, 4);
lean_inc(v_r_3811_);
v_size_3812_ = lean_ctor_get(v_r_3628_, 0);
v_k_3813_ = lean_ctor_get(v_r_3628_, 1);
v_v_3814_ = lean_ctor_get(v_r_3628_, 2);
v_l_3815_ = lean_ctor_get(v_r_3628_, 3);
lean_inc(v_l_3815_);
v_r_3816_ = lean_ctor_get(v_r_3628_, 4);
v___x_3817_ = lean_unsigned_to_nat(1u);
v___x_3818_ = lean_nat_dec_lt(v_size_3807_, v_size_3812_);
if (v___x_3818_ == 0)
{
lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3954_; 
lean_inc(v_l_3810_);
lean_inc(v_v_3809_);
lean_inc(v_k_3808_);
v_isSharedCheck_3954_ = !lean_is_exclusive(v_l_3627_);
if (v_isSharedCheck_3954_ == 0)
{
lean_object* v_unused_3955_; lean_object* v_unused_3956_; lean_object* v_unused_3957_; lean_object* v_unused_3958_; lean_object* v_unused_3959_; 
v_unused_3955_ = lean_ctor_get(v_l_3627_, 4);
lean_dec(v_unused_3955_);
v_unused_3956_ = lean_ctor_get(v_l_3627_, 3);
lean_dec(v_unused_3956_);
v_unused_3957_ = lean_ctor_get(v_l_3627_, 2);
lean_dec(v_unused_3957_);
v_unused_3958_ = lean_ctor_get(v_l_3627_, 1);
lean_dec(v_unused_3958_);
v_unused_3959_ = lean_ctor_get(v_l_3627_, 0);
lean_dec(v_unused_3959_);
v___x_3820_ = v_l_3627_;
v_isShared_3821_ = v_isSharedCheck_3954_;
goto v_resetjp_3819_;
}
else
{
lean_dec(v_l_3627_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3954_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3822_; lean_object* v_tree_3823_; 
v___x_3822_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3808_, v_v_3809_, v_l_3810_, v_r_3811_);
v_tree_3823_ = lean_ctor_get(v___x_3822_, 2);
lean_inc(v_tree_3823_);
if (lean_obj_tag(v_tree_3823_) == 0)
{
lean_object* v_k_3824_; lean_object* v_v_3825_; lean_object* v_size_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; uint8_t v___x_3829_; 
v_k_3824_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_k_3824_);
v_v_3825_ = lean_ctor_get(v___x_3822_, 1);
lean_inc(v_v_3825_);
lean_dec_ref(v___x_3822_);
v_size_3826_ = lean_ctor_get(v_tree_3823_, 0);
v___x_3827_ = lean_unsigned_to_nat(3u);
v___x_3828_ = lean_nat_mul(v___x_3827_, v_size_3826_);
v___x_3829_ = lean_nat_dec_lt(v___x_3828_, v_size_3812_);
lean_dec(v___x_3828_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3833_; 
lean_dec(v_l_3815_);
v___x_3830_ = lean_nat_add(v___x_3817_, v_size_3826_);
v___x_3831_ = lean_nat_add(v___x_3830_, v_size_3812_);
lean_dec(v___x_3830_);
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 4, v_r_3628_);
lean_ctor_set(v___x_3820_, 3, v_tree_3823_);
lean_ctor_set(v___x_3820_, 2, v_v_3825_);
lean_ctor_set(v___x_3820_, 1, v_k_3824_);
lean_ctor_set(v___x_3820_, 0, v___x_3831_);
v___x_3833_ = v___x_3820_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3831_);
lean_ctor_set(v_reuseFailAlloc_3834_, 1, v_k_3824_);
lean_ctor_set(v_reuseFailAlloc_3834_, 2, v_v_3825_);
lean_ctor_set(v_reuseFailAlloc_3834_, 3, v_tree_3823_);
lean_ctor_set(v_reuseFailAlloc_3834_, 4, v_r_3628_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
else
{
lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3889_; 
lean_inc(v_r_3816_);
lean_inc(v_v_3814_);
lean_inc(v_k_3813_);
lean_inc(v_size_3812_);
v_isSharedCheck_3889_ = !lean_is_exclusive(v_r_3628_);
if (v_isSharedCheck_3889_ == 0)
{
lean_object* v_unused_3890_; lean_object* v_unused_3891_; lean_object* v_unused_3892_; lean_object* v_unused_3893_; lean_object* v_unused_3894_; 
v_unused_3890_ = lean_ctor_get(v_r_3628_, 4);
lean_dec(v_unused_3890_);
v_unused_3891_ = lean_ctor_get(v_r_3628_, 3);
lean_dec(v_unused_3891_);
v_unused_3892_ = lean_ctor_get(v_r_3628_, 2);
lean_dec(v_unused_3892_);
v_unused_3893_ = lean_ctor_get(v_r_3628_, 1);
lean_dec(v_unused_3893_);
v_unused_3894_ = lean_ctor_get(v_r_3628_, 0);
lean_dec(v_unused_3894_);
v___x_3836_ = v_r_3628_;
v_isShared_3837_ = v_isSharedCheck_3889_;
goto v_resetjp_3835_;
}
else
{
lean_dec(v_r_3628_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3889_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v_size_3838_; lean_object* v_k_3839_; lean_object* v_v_3840_; lean_object* v_l_3841_; lean_object* v_r_3842_; lean_object* v_size_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; uint8_t v___x_3846_; 
v_size_3838_ = lean_ctor_get(v_l_3815_, 0);
v_k_3839_ = lean_ctor_get(v_l_3815_, 1);
v_v_3840_ = lean_ctor_get(v_l_3815_, 2);
v_l_3841_ = lean_ctor_get(v_l_3815_, 3);
v_r_3842_ = lean_ctor_get(v_l_3815_, 4);
v_size_3843_ = lean_ctor_get(v_r_3816_, 0);
v___x_3844_ = lean_unsigned_to_nat(2u);
v___x_3845_ = lean_nat_mul(v___x_3844_, v_size_3843_);
v___x_3846_ = lean_nat_dec_lt(v_size_3838_, v___x_3845_);
lean_dec(v___x_3845_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3874_; 
lean_inc(v_r_3842_);
lean_inc(v_l_3841_);
lean_inc(v_v_3840_);
lean_inc(v_k_3839_);
v_isSharedCheck_3874_ = !lean_is_exclusive(v_l_3815_);
if (v_isSharedCheck_3874_ == 0)
{
lean_object* v_unused_3875_; lean_object* v_unused_3876_; lean_object* v_unused_3877_; lean_object* v_unused_3878_; lean_object* v_unused_3879_; 
v_unused_3875_ = lean_ctor_get(v_l_3815_, 4);
lean_dec(v_unused_3875_);
v_unused_3876_ = lean_ctor_get(v_l_3815_, 3);
lean_dec(v_unused_3876_);
v_unused_3877_ = lean_ctor_get(v_l_3815_, 2);
lean_dec(v_unused_3877_);
v_unused_3878_ = lean_ctor_get(v_l_3815_, 1);
lean_dec(v_unused_3878_);
v_unused_3879_ = lean_ctor_get(v_l_3815_, 0);
lean_dec(v_unused_3879_);
v___x_3848_ = v_l_3815_;
v_isShared_3849_ = v_isSharedCheck_3874_;
goto v_resetjp_3847_;
}
else
{
lean_dec(v_l_3815_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3874_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3864_; 
v___x_3850_ = lean_nat_add(v___x_3817_, v_size_3826_);
v___x_3851_ = lean_nat_add(v___x_3850_, v_size_3812_);
lean_dec(v_size_3812_);
if (lean_obj_tag(v_l_3841_) == 0)
{
lean_object* v_size_3872_; 
v_size_3872_ = lean_ctor_get(v_l_3841_, 0);
lean_inc(v_size_3872_);
v___y_3864_ = v_size_3872_;
goto v___jp_3863_;
}
else
{
lean_object* v___x_3873_; 
v___x_3873_ = lean_unsigned_to_nat(0u);
v___y_3864_ = v___x_3873_;
goto v___jp_3863_;
}
v___jp_3852_:
{
lean_object* v___x_3856_; lean_object* v___x_3858_; 
v___x_3856_ = lean_nat_add(v___y_3853_, v___y_3855_);
lean_dec(v___y_3855_);
lean_dec(v___y_3853_);
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 4, v_r_3816_);
lean_ctor_set(v___x_3848_, 3, v_r_3842_);
lean_ctor_set(v___x_3848_, 2, v_v_3814_);
lean_ctor_set(v___x_3848_, 1, v_k_3813_);
lean_ctor_set(v___x_3848_, 0, v___x_3856_);
v___x_3858_ = v___x_3848_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3856_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_k_3813_);
lean_ctor_set(v_reuseFailAlloc_3862_, 2, v_v_3814_);
lean_ctor_set(v_reuseFailAlloc_3862_, 3, v_r_3842_);
lean_ctor_set(v_reuseFailAlloc_3862_, 4, v_r_3816_);
v___x_3858_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
lean_object* v___x_3860_; 
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 4, v___x_3858_);
lean_ctor_set(v___x_3836_, 3, v___y_3854_);
lean_ctor_set(v___x_3836_, 2, v_v_3840_);
lean_ctor_set(v___x_3836_, 1, v_k_3839_);
lean_ctor_set(v___x_3836_, 0, v___x_3851_);
v___x_3860_ = v___x_3836_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v___x_3851_);
lean_ctor_set(v_reuseFailAlloc_3861_, 1, v_k_3839_);
lean_ctor_set(v_reuseFailAlloc_3861_, 2, v_v_3840_);
lean_ctor_set(v_reuseFailAlloc_3861_, 3, v___y_3854_);
lean_ctor_set(v_reuseFailAlloc_3861_, 4, v___x_3858_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
v___jp_3863_:
{
lean_object* v___x_3865_; lean_object* v___x_3867_; 
v___x_3865_ = lean_nat_add(v___x_3850_, v___y_3864_);
lean_dec(v___y_3864_);
lean_dec(v___x_3850_);
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 4, v_l_3841_);
lean_ctor_set(v___x_3820_, 3, v_tree_3823_);
lean_ctor_set(v___x_3820_, 2, v_v_3825_);
lean_ctor_set(v___x_3820_, 1, v_k_3824_);
lean_ctor_set(v___x_3820_, 0, v___x_3865_);
v___x_3867_ = v___x_3820_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3865_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v_k_3824_);
lean_ctor_set(v_reuseFailAlloc_3871_, 2, v_v_3825_);
lean_ctor_set(v_reuseFailAlloc_3871_, 3, v_tree_3823_);
lean_ctor_set(v_reuseFailAlloc_3871_, 4, v_l_3841_);
v___x_3867_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
lean_object* v___x_3868_; 
v___x_3868_ = lean_nat_add(v___x_3817_, v_size_3843_);
if (lean_obj_tag(v_r_3842_) == 0)
{
lean_object* v_size_3869_; 
v_size_3869_ = lean_ctor_get(v_r_3842_, 0);
lean_inc(v_size_3869_);
v___y_3853_ = v___x_3868_;
v___y_3854_ = v___x_3867_;
v___y_3855_ = v_size_3869_;
goto v___jp_3852_;
}
else
{
lean_object* v___x_3870_; 
v___x_3870_ = lean_unsigned_to_nat(0u);
v___y_3853_ = v___x_3868_;
v___y_3854_ = v___x_3867_;
v___y_3855_ = v___x_3870_;
goto v___jp_3852_;
}
}
}
}
}
else
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3884_; 
v___x_3880_ = lean_nat_add(v___x_3817_, v_size_3826_);
v___x_3881_ = lean_nat_add(v___x_3880_, v_size_3812_);
lean_dec(v_size_3812_);
v___x_3882_ = lean_nat_add(v___x_3880_, v_size_3838_);
lean_dec(v___x_3880_);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 4, v_l_3815_);
lean_ctor_set(v___x_3836_, 3, v_tree_3823_);
lean_ctor_set(v___x_3836_, 2, v_v_3825_);
lean_ctor_set(v___x_3836_, 1, v_k_3824_);
lean_ctor_set(v___x_3836_, 0, v___x_3882_);
v___x_3884_ = v___x_3836_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3882_);
lean_ctor_set(v_reuseFailAlloc_3888_, 1, v_k_3824_);
lean_ctor_set(v_reuseFailAlloc_3888_, 2, v_v_3825_);
lean_ctor_set(v_reuseFailAlloc_3888_, 3, v_tree_3823_);
lean_ctor_set(v_reuseFailAlloc_3888_, 4, v_l_3815_);
v___x_3884_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
lean_object* v___x_3886_; 
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 4, v_r_3816_);
lean_ctor_set(v___x_3820_, 3, v___x_3884_);
lean_ctor_set(v___x_3820_, 2, v_v_3814_);
lean_ctor_set(v___x_3820_, 1, v_k_3813_);
lean_ctor_set(v___x_3820_, 0, v___x_3881_);
v___x_3886_ = v___x_3820_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3881_);
lean_ctor_set(v_reuseFailAlloc_3887_, 1, v_k_3813_);
lean_ctor_set(v_reuseFailAlloc_3887_, 2, v_v_3814_);
lean_ctor_set(v_reuseFailAlloc_3887_, 3, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3887_, 4, v_r_3816_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
}
}
else
{
lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3948_; 
lean_inc(v_r_3816_);
lean_inc(v_v_3814_);
lean_inc(v_k_3813_);
lean_inc(v_size_3812_);
v_isSharedCheck_3948_ = !lean_is_exclusive(v_r_3628_);
if (v_isSharedCheck_3948_ == 0)
{
lean_object* v_unused_3949_; lean_object* v_unused_3950_; lean_object* v_unused_3951_; lean_object* v_unused_3952_; lean_object* v_unused_3953_; 
v_unused_3949_ = lean_ctor_get(v_r_3628_, 4);
lean_dec(v_unused_3949_);
v_unused_3950_ = lean_ctor_get(v_r_3628_, 3);
lean_dec(v_unused_3950_);
v_unused_3951_ = lean_ctor_get(v_r_3628_, 2);
lean_dec(v_unused_3951_);
v_unused_3952_ = lean_ctor_get(v_r_3628_, 1);
lean_dec(v_unused_3952_);
v_unused_3953_ = lean_ctor_get(v_r_3628_, 0);
lean_dec(v_unused_3953_);
v___x_3896_ = v_r_3628_;
v_isShared_3897_ = v_isSharedCheck_3948_;
goto v_resetjp_3895_;
}
else
{
lean_dec(v_r_3628_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3948_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
if (lean_obj_tag(v_l_3815_) == 0)
{
if (lean_obj_tag(v_r_3816_) == 0)
{
lean_object* v_k_3898_; lean_object* v_v_3899_; lean_object* v_size_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3904_; 
v_k_3898_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_k_3898_);
v_v_3899_ = lean_ctor_get(v___x_3822_, 1);
lean_inc(v_v_3899_);
lean_dec_ref(v___x_3822_);
v_size_3900_ = lean_ctor_get(v_l_3815_, 0);
v___x_3901_ = lean_nat_add(v___x_3817_, v_size_3812_);
lean_dec(v_size_3812_);
v___x_3902_ = lean_nat_add(v___x_3817_, v_size_3900_);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 4, v_l_3815_);
lean_ctor_set(v___x_3896_, 3, v_tree_3823_);
lean_ctor_set(v___x_3896_, 2, v_v_3899_);
lean_ctor_set(v___x_3896_, 1, v_k_3898_);
lean_ctor_set(v___x_3896_, 0, v___x_3902_);
v___x_3904_ = v___x_3896_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3902_);
lean_ctor_set(v_reuseFailAlloc_3908_, 1, v_k_3898_);
lean_ctor_set(v_reuseFailAlloc_3908_, 2, v_v_3899_);
lean_ctor_set(v_reuseFailAlloc_3908_, 3, v_tree_3823_);
lean_ctor_set(v_reuseFailAlloc_3908_, 4, v_l_3815_);
v___x_3904_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
lean_object* v___x_3906_; 
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 4, v_r_3816_);
lean_ctor_set(v___x_3820_, 3, v___x_3904_);
lean_ctor_set(v___x_3820_, 2, v_v_3814_);
lean_ctor_set(v___x_3820_, 1, v_k_3813_);
lean_ctor_set(v___x_3820_, 0, v___x_3901_);
v___x_3906_ = v___x_3820_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3901_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v_k_3813_);
lean_ctor_set(v_reuseFailAlloc_3907_, 2, v_v_3814_);
lean_ctor_set(v_reuseFailAlloc_3907_, 3, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3907_, 4, v_r_3816_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
else
{
lean_object* v_k_3909_; lean_object* v_v_3910_; lean_object* v_k_3911_; lean_object* v_v_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3926_; 
lean_dec(v_size_3812_);
v_k_3909_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_k_3909_);
v_v_3910_ = lean_ctor_get(v___x_3822_, 1);
lean_inc(v_v_3910_);
lean_dec_ref(v___x_3822_);
v_k_3911_ = lean_ctor_get(v_l_3815_, 1);
v_v_3912_ = lean_ctor_get(v_l_3815_, 2);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_l_3815_);
if (v_isSharedCheck_3926_ == 0)
{
lean_object* v_unused_3927_; lean_object* v_unused_3928_; lean_object* v_unused_3929_; 
v_unused_3927_ = lean_ctor_get(v_l_3815_, 4);
lean_dec(v_unused_3927_);
v_unused_3928_ = lean_ctor_get(v_l_3815_, 3);
lean_dec(v_unused_3928_);
v_unused_3929_ = lean_ctor_get(v_l_3815_, 0);
lean_dec(v_unused_3929_);
v___x_3914_ = v_l_3815_;
v_isShared_3915_ = v_isSharedCheck_3926_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_v_3912_);
lean_inc(v_k_3911_);
lean_dec(v_l_3815_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3926_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3916_; lean_object* v___x_3918_; 
v___x_3916_ = lean_unsigned_to_nat(3u);
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 4, v_r_3816_);
lean_ctor_set(v___x_3914_, 3, v_r_3816_);
lean_ctor_set(v___x_3914_, 2, v_v_3910_);
lean_ctor_set(v___x_3914_, 1, v_k_3909_);
lean_ctor_set(v___x_3914_, 0, v___x_3817_);
v___x_3918_ = v___x_3914_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3817_);
lean_ctor_set(v_reuseFailAlloc_3925_, 1, v_k_3909_);
lean_ctor_set(v_reuseFailAlloc_3925_, 2, v_v_3910_);
lean_ctor_set(v_reuseFailAlloc_3925_, 3, v_r_3816_);
lean_ctor_set(v_reuseFailAlloc_3925_, 4, v_r_3816_);
v___x_3918_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
lean_object* v___x_3920_; 
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 3, v_r_3816_);
lean_ctor_set(v___x_3896_, 0, v___x_3817_);
v___x_3920_ = v___x_3896_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3817_);
lean_ctor_set(v_reuseFailAlloc_3924_, 1, v_k_3813_);
lean_ctor_set(v_reuseFailAlloc_3924_, 2, v_v_3814_);
lean_ctor_set(v_reuseFailAlloc_3924_, 3, v_r_3816_);
lean_ctor_set(v_reuseFailAlloc_3924_, 4, v_r_3816_);
v___x_3920_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
lean_object* v___x_3922_; 
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 4, v___x_3920_);
lean_ctor_set(v___x_3820_, 3, v___x_3918_);
lean_ctor_set(v___x_3820_, 2, v_v_3912_);
lean_ctor_set(v___x_3820_, 1, v_k_3911_);
lean_ctor_set(v___x_3820_, 0, v___x_3916_);
v___x_3922_ = v___x_3820_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3916_);
lean_ctor_set(v_reuseFailAlloc_3923_, 1, v_k_3911_);
lean_ctor_set(v_reuseFailAlloc_3923_, 2, v_v_3912_);
lean_ctor_set(v_reuseFailAlloc_3923_, 3, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3923_, 4, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3816_) == 0)
{
lean_object* v_k_3930_; lean_object* v_v_3931_; lean_object* v___x_3932_; lean_object* v___x_3934_; 
lean_dec(v_size_3812_);
v_k_3930_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_k_3930_);
v_v_3931_ = lean_ctor_get(v___x_3822_, 1);
lean_inc(v_v_3931_);
lean_dec_ref(v___x_3822_);
v___x_3932_ = lean_unsigned_to_nat(3u);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 4, v_l_3815_);
lean_ctor_set(v___x_3896_, 2, v_v_3931_);
lean_ctor_set(v___x_3896_, 1, v_k_3930_);
lean_ctor_set(v___x_3896_, 0, v___x_3817_);
v___x_3934_ = v___x_3896_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3817_);
lean_ctor_set(v_reuseFailAlloc_3938_, 1, v_k_3930_);
lean_ctor_set(v_reuseFailAlloc_3938_, 2, v_v_3931_);
lean_ctor_set(v_reuseFailAlloc_3938_, 3, v_l_3815_);
lean_ctor_set(v_reuseFailAlloc_3938_, 4, v_l_3815_);
v___x_3934_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3936_; 
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 4, v_r_3816_);
lean_ctor_set(v___x_3820_, 3, v___x_3934_);
lean_ctor_set(v___x_3820_, 2, v_v_3814_);
lean_ctor_set(v___x_3820_, 1, v_k_3813_);
lean_ctor_set(v___x_3820_, 0, v___x_3932_);
v___x_3936_ = v___x_3820_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3932_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v_k_3813_);
lean_ctor_set(v_reuseFailAlloc_3937_, 2, v_v_3814_);
lean_ctor_set(v_reuseFailAlloc_3937_, 3, v___x_3934_);
lean_ctor_set(v_reuseFailAlloc_3937_, 4, v_r_3816_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
else
{
lean_object* v_k_3939_; lean_object* v_v_3940_; lean_object* v___x_3942_; 
v_k_3939_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_k_3939_);
v_v_3940_ = lean_ctor_get(v___x_3822_, 1);
lean_inc(v_v_3940_);
lean_dec_ref(v___x_3822_);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 3, v_r_3816_);
v___x_3942_ = v___x_3896_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_size_3812_);
lean_ctor_set(v_reuseFailAlloc_3947_, 1, v_k_3813_);
lean_ctor_set(v_reuseFailAlloc_3947_, 2, v_v_3814_);
lean_ctor_set(v_reuseFailAlloc_3947_, 3, v_r_3816_);
lean_ctor_set(v_reuseFailAlloc_3947_, 4, v_r_3816_);
v___x_3942_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
lean_object* v___x_3943_; lean_object* v___x_3945_; 
v___x_3943_ = lean_unsigned_to_nat(2u);
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 4, v___x_3942_);
lean_ctor_set(v___x_3820_, 3, v_r_3816_);
lean_ctor_set(v___x_3820_, 2, v_v_3940_);
lean_ctor_set(v___x_3820_, 1, v_k_3939_);
lean_ctor_set(v___x_3820_, 0, v___x_3943_);
v___x_3945_ = v___x_3820_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3943_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v_k_3939_);
lean_ctor_set(v_reuseFailAlloc_3946_, 2, v_v_3940_);
lean_ctor_set(v_reuseFailAlloc_3946_, 3, v_r_3816_);
lean_ctor_set(v_reuseFailAlloc_3946_, 4, v___x_3942_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
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
lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_4112_; 
lean_inc(v_r_3816_);
lean_inc(v_v_3814_);
lean_inc(v_k_3813_);
v_isSharedCheck_4112_ = !lean_is_exclusive(v_r_3628_);
if (v_isSharedCheck_4112_ == 0)
{
lean_object* v_unused_4113_; lean_object* v_unused_4114_; lean_object* v_unused_4115_; lean_object* v_unused_4116_; lean_object* v_unused_4117_; 
v_unused_4113_ = lean_ctor_get(v_r_3628_, 4);
lean_dec(v_unused_4113_);
v_unused_4114_ = lean_ctor_get(v_r_3628_, 3);
lean_dec(v_unused_4114_);
v_unused_4115_ = lean_ctor_get(v_r_3628_, 2);
lean_dec(v_unused_4115_);
v_unused_4116_ = lean_ctor_get(v_r_3628_, 1);
lean_dec(v_unused_4116_);
v_unused_4117_ = lean_ctor_get(v_r_3628_, 0);
lean_dec(v_unused_4117_);
v___x_3961_ = v_r_3628_;
v_isShared_3962_ = v_isSharedCheck_4112_;
goto v_resetjp_3960_;
}
else
{
lean_dec(v_r_3628_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_4112_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3963_; lean_object* v_tree_3964_; 
v___x_3963_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3813_, v_v_3814_, v_l_3815_, v_r_3816_);
v_tree_3964_ = lean_ctor_get(v___x_3963_, 2);
lean_inc(v_tree_3964_);
if (lean_obj_tag(v_tree_3964_) == 0)
{
lean_object* v_k_3965_; lean_object* v_v_3966_; lean_object* v_size_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; uint8_t v___x_3970_; 
v_k_3965_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_k_3965_);
v_v_3966_ = lean_ctor_get(v___x_3963_, 1);
lean_inc(v_v_3966_);
lean_dec_ref(v___x_3963_);
v_size_3967_ = lean_ctor_get(v_tree_3964_, 0);
v___x_3968_ = lean_unsigned_to_nat(3u);
v___x_3969_ = lean_nat_mul(v___x_3968_, v_size_3967_);
v___x_3970_ = lean_nat_dec_lt(v___x_3969_, v_size_3807_);
lean_dec(v___x_3969_);
if (v___x_3970_ == 0)
{
lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3974_; 
lean_dec(v_r_3811_);
v___x_3971_ = lean_nat_add(v___x_3817_, v_size_3807_);
v___x_3972_ = lean_nat_add(v___x_3971_, v_size_3967_);
lean_dec(v___x_3971_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 4, v_tree_3964_);
lean_ctor_set(v___x_3961_, 3, v_l_3627_);
lean_ctor_set(v___x_3961_, 2, v_v_3966_);
lean_ctor_set(v___x_3961_, 1, v_k_3965_);
lean_ctor_set(v___x_3961_, 0, v___x_3972_);
v___x_3974_ = v___x_3961_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3972_);
lean_ctor_set(v_reuseFailAlloc_3975_, 1, v_k_3965_);
lean_ctor_set(v_reuseFailAlloc_3975_, 2, v_v_3966_);
lean_ctor_set(v_reuseFailAlloc_3975_, 3, v_l_3627_);
lean_ctor_set(v_reuseFailAlloc_3975_, 4, v_tree_3964_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
else
{
lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_4041_; 
lean_inc(v_l_3810_);
lean_inc(v_v_3809_);
lean_inc(v_k_3808_);
lean_inc(v_size_3807_);
v_isSharedCheck_4041_ = !lean_is_exclusive(v_l_3627_);
if (v_isSharedCheck_4041_ == 0)
{
lean_object* v_unused_4042_; lean_object* v_unused_4043_; lean_object* v_unused_4044_; lean_object* v_unused_4045_; lean_object* v_unused_4046_; 
v_unused_4042_ = lean_ctor_get(v_l_3627_, 4);
lean_dec(v_unused_4042_);
v_unused_4043_ = lean_ctor_get(v_l_3627_, 3);
lean_dec(v_unused_4043_);
v_unused_4044_ = lean_ctor_get(v_l_3627_, 2);
lean_dec(v_unused_4044_);
v_unused_4045_ = lean_ctor_get(v_l_3627_, 1);
lean_dec(v_unused_4045_);
v_unused_4046_ = lean_ctor_get(v_l_3627_, 0);
lean_dec(v_unused_4046_);
v___x_3977_ = v_l_3627_;
v_isShared_3978_ = v_isSharedCheck_4041_;
goto v_resetjp_3976_;
}
else
{
lean_dec(v_l_3627_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_4041_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v_size_3979_; lean_object* v_size_3980_; lean_object* v_k_3981_; lean_object* v_v_3982_; lean_object* v_l_3983_; lean_object* v_r_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; uint8_t v___x_3987_; 
v_size_3979_ = lean_ctor_get(v_l_3810_, 0);
v_size_3980_ = lean_ctor_get(v_r_3811_, 0);
v_k_3981_ = lean_ctor_get(v_r_3811_, 1);
v_v_3982_ = lean_ctor_get(v_r_3811_, 2);
v_l_3983_ = lean_ctor_get(v_r_3811_, 3);
v_r_3984_ = lean_ctor_get(v_r_3811_, 4);
v___x_3985_ = lean_unsigned_to_nat(2u);
v___x_3986_ = lean_nat_mul(v___x_3985_, v_size_3979_);
v___x_3987_ = lean_nat_dec_lt(v_size_3980_, v___x_3986_);
lean_dec(v___x_3986_);
if (v___x_3987_ == 0)
{
lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_4025_; 
lean_inc(v_r_3984_);
lean_inc(v_l_3983_);
lean_inc(v_v_3982_);
lean_inc(v_k_3981_);
lean_del_object(v___x_3977_);
v_isSharedCheck_4025_ = !lean_is_exclusive(v_r_3811_);
if (v_isSharedCheck_4025_ == 0)
{
lean_object* v_unused_4026_; lean_object* v_unused_4027_; lean_object* v_unused_4028_; lean_object* v_unused_4029_; lean_object* v_unused_4030_; 
v_unused_4026_ = lean_ctor_get(v_r_3811_, 4);
lean_dec(v_unused_4026_);
v_unused_4027_ = lean_ctor_get(v_r_3811_, 3);
lean_dec(v_unused_4027_);
v_unused_4028_ = lean_ctor_get(v_r_3811_, 2);
lean_dec(v_unused_4028_);
v_unused_4029_ = lean_ctor_get(v_r_3811_, 1);
lean_dec(v_unused_4029_);
v_unused_4030_ = lean_ctor_get(v_r_3811_, 0);
lean_dec(v_unused_4030_);
v___x_3989_ = v_r_3811_;
v_isShared_3990_ = v_isSharedCheck_4025_;
goto v_resetjp_3988_;
}
else
{
lean_dec(v_r_3811_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_4025_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___x_4013_; lean_object* v___y_4015_; 
v___x_3991_ = lean_nat_add(v___x_3817_, v_size_3807_);
lean_dec(v_size_3807_);
v___x_3992_ = lean_nat_add(v___x_3991_, v_size_3967_);
lean_dec(v___x_3991_);
v___x_4013_ = lean_nat_add(v___x_3817_, v_size_3979_);
if (lean_obj_tag(v_l_3983_) == 0)
{
lean_object* v_size_4023_; 
v_size_4023_ = lean_ctor_get(v_l_3983_, 0);
lean_inc(v_size_4023_);
v___y_4015_ = v_size_4023_;
goto v___jp_4014_;
}
else
{
lean_object* v___x_4024_; 
v___x_4024_ = lean_unsigned_to_nat(0u);
v___y_4015_ = v___x_4024_;
goto v___jp_4014_;
}
v___jp_3993_:
{
lean_object* v___x_3997_; lean_object* v___x_3999_; 
v___x_3997_ = lean_nat_add(v___y_3995_, v___y_3996_);
lean_dec(v___y_3996_);
lean_dec(v___y_3995_);
lean_inc_ref(v_tree_3964_);
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 4, v_tree_3964_);
lean_ctor_set(v___x_3989_, 3, v_r_3984_);
lean_ctor_set(v___x_3989_, 2, v_v_3966_);
lean_ctor_set(v___x_3989_, 1, v_k_3965_);
lean_ctor_set(v___x_3989_, 0, v___x_3997_);
v___x_3999_ = v___x_3989_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_3997_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v_k_3965_);
lean_ctor_set(v_reuseFailAlloc_4012_, 2, v_v_3966_);
lean_ctor_set(v_reuseFailAlloc_4012_, 3, v_r_3984_);
lean_ctor_set(v_reuseFailAlloc_4012_, 4, v_tree_3964_);
v___x_3999_ = v_reuseFailAlloc_4012_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
v_isSharedCheck_4006_ = !lean_is_exclusive(v_tree_3964_);
if (v_isSharedCheck_4006_ == 0)
{
lean_object* v_unused_4007_; lean_object* v_unused_4008_; lean_object* v_unused_4009_; lean_object* v_unused_4010_; lean_object* v_unused_4011_; 
v_unused_4007_ = lean_ctor_get(v_tree_3964_, 4);
lean_dec(v_unused_4007_);
v_unused_4008_ = lean_ctor_get(v_tree_3964_, 3);
lean_dec(v_unused_4008_);
v_unused_4009_ = lean_ctor_get(v_tree_3964_, 2);
lean_dec(v_unused_4009_);
v_unused_4010_ = lean_ctor_get(v_tree_3964_, 1);
lean_dec(v_unused_4010_);
v_unused_4011_ = lean_ctor_get(v_tree_3964_, 0);
lean_dec(v_unused_4011_);
v___x_4001_ = v_tree_3964_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_dec(v_tree_3964_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 4, v___x_3999_);
lean_ctor_set(v___x_4001_, 3, v___y_3994_);
lean_ctor_set(v___x_4001_, 2, v_v_3982_);
lean_ctor_set(v___x_4001_, 1, v_k_3981_);
lean_ctor_set(v___x_4001_, 0, v___x_3992_);
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_3992_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v_k_3981_);
lean_ctor_set(v_reuseFailAlloc_4005_, 2, v_v_3982_);
lean_ctor_set(v_reuseFailAlloc_4005_, 3, v___y_3994_);
lean_ctor_set(v_reuseFailAlloc_4005_, 4, v___x_3999_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
}
v___jp_4014_:
{
lean_object* v___x_4016_; lean_object* v___x_4018_; 
v___x_4016_ = lean_nat_add(v___x_4013_, v___y_4015_);
lean_dec(v___y_4015_);
lean_dec(v___x_4013_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 4, v_l_3983_);
lean_ctor_set(v___x_3961_, 3, v_l_3810_);
lean_ctor_set(v___x_3961_, 2, v_v_3809_);
lean_ctor_set(v___x_3961_, 1, v_k_3808_);
lean_ctor_set(v___x_3961_, 0, v___x_4016_);
v___x_4018_ = v___x_3961_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_4016_);
lean_ctor_set(v_reuseFailAlloc_4022_, 1, v_k_3808_);
lean_ctor_set(v_reuseFailAlloc_4022_, 2, v_v_3809_);
lean_ctor_set(v_reuseFailAlloc_4022_, 3, v_l_3810_);
lean_ctor_set(v_reuseFailAlloc_4022_, 4, v_l_3983_);
v___x_4018_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
lean_object* v___x_4019_; 
v___x_4019_ = lean_nat_add(v___x_3817_, v_size_3967_);
if (lean_obj_tag(v_r_3984_) == 0)
{
lean_object* v_size_4020_; 
v_size_4020_ = lean_ctor_get(v_r_3984_, 0);
lean_inc(v_size_4020_);
v___y_3994_ = v___x_4018_;
v___y_3995_ = v___x_4019_;
v___y_3996_ = v_size_4020_;
goto v___jp_3993_;
}
else
{
lean_object* v___x_4021_; 
v___x_4021_ = lean_unsigned_to_nat(0u);
v___y_3994_ = v___x_4018_;
v___y_3995_ = v___x_4019_;
v___y_3996_ = v___x_4021_;
goto v___jp_3993_;
}
}
}
}
}
else
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4036_; 
v___x_4031_ = lean_nat_add(v___x_3817_, v_size_3807_);
lean_dec(v_size_3807_);
v___x_4032_ = lean_nat_add(v___x_4031_, v_size_3967_);
lean_dec(v___x_4031_);
v___x_4033_ = lean_nat_add(v___x_3817_, v_size_3967_);
v___x_4034_ = lean_nat_add(v___x_4033_, v_size_3980_);
lean_dec(v___x_4033_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 4, v_tree_3964_);
lean_ctor_set(v___x_3961_, 3, v_r_3811_);
lean_ctor_set(v___x_3961_, 2, v_v_3966_);
lean_ctor_set(v___x_3961_, 1, v_k_3965_);
lean_ctor_set(v___x_3961_, 0, v___x_4034_);
v___x_4036_ = v___x_3961_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4034_);
lean_ctor_set(v_reuseFailAlloc_4040_, 1, v_k_3965_);
lean_ctor_set(v_reuseFailAlloc_4040_, 2, v_v_3966_);
lean_ctor_set(v_reuseFailAlloc_4040_, 3, v_r_3811_);
lean_ctor_set(v_reuseFailAlloc_4040_, 4, v_tree_3964_);
v___x_4036_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
lean_object* v___x_4038_; 
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 4, v___x_4036_);
lean_ctor_set(v___x_3977_, 0, v___x_4032_);
v___x_4038_ = v___x_3977_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v___x_4032_);
lean_ctor_set(v_reuseFailAlloc_4039_, 1, v_k_3808_);
lean_ctor_set(v_reuseFailAlloc_4039_, 2, v_v_3809_);
lean_ctor_set(v_reuseFailAlloc_4039_, 3, v_l_3810_);
lean_ctor_set(v_reuseFailAlloc_4039_, 4, v___x_4036_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3810_) == 0)
{
lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4070_; 
lean_inc_ref(v_l_3810_);
lean_inc(v_v_3809_);
lean_inc(v_k_3808_);
lean_inc(v_size_3807_);
v_isSharedCheck_4070_ = !lean_is_exclusive(v_l_3627_);
if (v_isSharedCheck_4070_ == 0)
{
lean_object* v_unused_4071_; lean_object* v_unused_4072_; lean_object* v_unused_4073_; lean_object* v_unused_4074_; lean_object* v_unused_4075_; 
v_unused_4071_ = lean_ctor_get(v_l_3627_, 4);
lean_dec(v_unused_4071_);
v_unused_4072_ = lean_ctor_get(v_l_3627_, 3);
lean_dec(v_unused_4072_);
v_unused_4073_ = lean_ctor_get(v_l_3627_, 2);
lean_dec(v_unused_4073_);
v_unused_4074_ = lean_ctor_get(v_l_3627_, 1);
lean_dec(v_unused_4074_);
v_unused_4075_ = lean_ctor_get(v_l_3627_, 0);
lean_dec(v_unused_4075_);
v___x_4048_ = v_l_3627_;
v_isShared_4049_ = v_isSharedCheck_4070_;
goto v_resetjp_4047_;
}
else
{
lean_dec(v_l_3627_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4070_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
if (lean_obj_tag(v_r_3811_) == 0)
{
lean_object* v_k_4050_; lean_object* v_v_4051_; lean_object* v_size_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4056_; 
v_k_4050_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_k_4050_);
v_v_4051_ = lean_ctor_get(v___x_3963_, 1);
lean_inc(v_v_4051_);
lean_dec_ref(v___x_3963_);
v_size_4052_ = lean_ctor_get(v_r_3811_, 0);
v___x_4053_ = lean_nat_add(v___x_3817_, v_size_3807_);
lean_dec(v_size_3807_);
v___x_4054_ = lean_nat_add(v___x_3817_, v_size_4052_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 4, v_tree_3964_);
lean_ctor_set(v___x_3961_, 3, v_r_3811_);
lean_ctor_set(v___x_3961_, 2, v_v_4051_);
lean_ctor_set(v___x_3961_, 1, v_k_4050_);
lean_ctor_set(v___x_3961_, 0, v___x_4054_);
v___x_4056_ = v___x_3961_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4054_);
lean_ctor_set(v_reuseFailAlloc_4060_, 1, v_k_4050_);
lean_ctor_set(v_reuseFailAlloc_4060_, 2, v_v_4051_);
lean_ctor_set(v_reuseFailAlloc_4060_, 3, v_r_3811_);
lean_ctor_set(v_reuseFailAlloc_4060_, 4, v_tree_3964_);
v___x_4056_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
lean_object* v___x_4058_; 
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 4, v___x_4056_);
lean_ctor_set(v___x_4048_, 0, v___x_4053_);
v___x_4058_ = v___x_4048_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v___x_4053_);
lean_ctor_set(v_reuseFailAlloc_4059_, 1, v_k_3808_);
lean_ctor_set(v_reuseFailAlloc_4059_, 2, v_v_3809_);
lean_ctor_set(v_reuseFailAlloc_4059_, 3, v_l_3810_);
lean_ctor_set(v_reuseFailAlloc_4059_, 4, v___x_4056_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
else
{
lean_object* v_k_4061_; lean_object* v_v_4062_; lean_object* v___x_4063_; lean_object* v___x_4065_; 
lean_dec(v_size_3807_);
v_k_4061_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_k_4061_);
v_v_4062_ = lean_ctor_get(v___x_3963_, 1);
lean_inc(v_v_4062_);
lean_dec_ref(v___x_3963_);
v___x_4063_ = lean_unsigned_to_nat(3u);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 4, v_r_3811_);
lean_ctor_set(v___x_3961_, 3, v_r_3811_);
lean_ctor_set(v___x_3961_, 2, v_v_4062_);
lean_ctor_set(v___x_3961_, 1, v_k_4061_);
lean_ctor_set(v___x_3961_, 0, v___x_3817_);
v___x_4065_ = v___x_3961_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_3817_);
lean_ctor_set(v_reuseFailAlloc_4069_, 1, v_k_4061_);
lean_ctor_set(v_reuseFailAlloc_4069_, 2, v_v_4062_);
lean_ctor_set(v_reuseFailAlloc_4069_, 3, v_r_3811_);
lean_ctor_set(v_reuseFailAlloc_4069_, 4, v_r_3811_);
v___x_4065_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
lean_object* v___x_4067_; 
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 4, v___x_4065_);
lean_ctor_set(v___x_4048_, 0, v___x_4063_);
v___x_4067_ = v___x_4048_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4063_);
lean_ctor_set(v_reuseFailAlloc_4068_, 1, v_k_3808_);
lean_ctor_set(v_reuseFailAlloc_4068_, 2, v_v_3809_);
lean_ctor_set(v_reuseFailAlloc_4068_, 3, v_l_3810_);
lean_ctor_set(v_reuseFailAlloc_4068_, 4, v___x_4065_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3811_) == 0)
{
lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4100_; 
lean_inc(v_l_3810_);
lean_inc(v_v_3809_);
lean_inc(v_k_3808_);
v_isSharedCheck_4100_ = !lean_is_exclusive(v_l_3627_);
if (v_isSharedCheck_4100_ == 0)
{
lean_object* v_unused_4101_; lean_object* v_unused_4102_; lean_object* v_unused_4103_; lean_object* v_unused_4104_; lean_object* v_unused_4105_; 
v_unused_4101_ = lean_ctor_get(v_l_3627_, 4);
lean_dec(v_unused_4101_);
v_unused_4102_ = lean_ctor_get(v_l_3627_, 3);
lean_dec(v_unused_4102_);
v_unused_4103_ = lean_ctor_get(v_l_3627_, 2);
lean_dec(v_unused_4103_);
v_unused_4104_ = lean_ctor_get(v_l_3627_, 1);
lean_dec(v_unused_4104_);
v_unused_4105_ = lean_ctor_get(v_l_3627_, 0);
lean_dec(v_unused_4105_);
v___x_4077_ = v_l_3627_;
v_isShared_4078_ = v_isSharedCheck_4100_;
goto v_resetjp_4076_;
}
else
{
lean_dec(v_l_3627_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4100_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v_k_4079_; lean_object* v_v_4080_; lean_object* v_k_4081_; lean_object* v_v_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4096_; 
v_k_4079_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_k_4079_);
v_v_4080_ = lean_ctor_get(v___x_3963_, 1);
lean_inc(v_v_4080_);
lean_dec_ref(v___x_3963_);
v_k_4081_ = lean_ctor_get(v_r_3811_, 1);
v_v_4082_ = lean_ctor_get(v_r_3811_, 2);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_r_3811_);
if (v_isSharedCheck_4096_ == 0)
{
lean_object* v_unused_4097_; lean_object* v_unused_4098_; lean_object* v_unused_4099_; 
v_unused_4097_ = lean_ctor_get(v_r_3811_, 4);
lean_dec(v_unused_4097_);
v_unused_4098_ = lean_ctor_get(v_r_3811_, 3);
lean_dec(v_unused_4098_);
v_unused_4099_ = lean_ctor_get(v_r_3811_, 0);
lean_dec(v_unused_4099_);
v___x_4084_ = v_r_3811_;
v_isShared_4085_ = v_isSharedCheck_4096_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_v_4082_);
lean_inc(v_k_4081_);
lean_dec(v_r_3811_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4096_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4086_; lean_object* v___x_4088_; 
v___x_4086_ = lean_unsigned_to_nat(3u);
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 4, v_l_3810_);
lean_ctor_set(v___x_4084_, 3, v_l_3810_);
lean_ctor_set(v___x_4084_, 2, v_v_3809_);
lean_ctor_set(v___x_4084_, 1, v_k_3808_);
lean_ctor_set(v___x_4084_, 0, v___x_3817_);
v___x_4088_ = v___x_4084_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v___x_3817_);
lean_ctor_set(v_reuseFailAlloc_4095_, 1, v_k_3808_);
lean_ctor_set(v_reuseFailAlloc_4095_, 2, v_v_3809_);
lean_ctor_set(v_reuseFailAlloc_4095_, 3, v_l_3810_);
lean_ctor_set(v_reuseFailAlloc_4095_, 4, v_l_3810_);
v___x_4088_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
lean_object* v___x_4090_; 
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 4, v_l_3810_);
lean_ctor_set(v___x_3961_, 3, v_l_3810_);
lean_ctor_set(v___x_3961_, 2, v_v_4080_);
lean_ctor_set(v___x_3961_, 1, v_k_4079_);
lean_ctor_set(v___x_3961_, 0, v___x_3817_);
v___x_4090_ = v___x_3961_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v___x_3817_);
lean_ctor_set(v_reuseFailAlloc_4094_, 1, v_k_4079_);
lean_ctor_set(v_reuseFailAlloc_4094_, 2, v_v_4080_);
lean_ctor_set(v_reuseFailAlloc_4094_, 3, v_l_3810_);
lean_ctor_set(v_reuseFailAlloc_4094_, 4, v_l_3810_);
v___x_4090_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
lean_object* v___x_4092_; 
if (v_isShared_4078_ == 0)
{
lean_ctor_set(v___x_4077_, 4, v___x_4090_);
lean_ctor_set(v___x_4077_, 3, v___x_4088_);
lean_ctor_set(v___x_4077_, 2, v_v_4082_);
lean_ctor_set(v___x_4077_, 1, v_k_4081_);
lean_ctor_set(v___x_4077_, 0, v___x_4086_);
v___x_4092_ = v___x_4077_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4086_);
lean_ctor_set(v_reuseFailAlloc_4093_, 1, v_k_4081_);
lean_ctor_set(v_reuseFailAlloc_4093_, 2, v_v_4082_);
lean_ctor_set(v_reuseFailAlloc_4093_, 3, v___x_4088_);
lean_ctor_set(v_reuseFailAlloc_4093_, 4, v___x_4090_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
}
}
}
else
{
lean_object* v_k_4106_; lean_object* v_v_4107_; lean_object* v___x_4108_; lean_object* v___x_4110_; 
v_k_4106_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_k_4106_);
v_v_4107_ = lean_ctor_get(v___x_3963_, 1);
lean_inc(v_v_4107_);
lean_dec_ref(v___x_3963_);
v___x_4108_ = lean_unsigned_to_nat(2u);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 4, v_r_3811_);
lean_ctor_set(v___x_3961_, 3, v_l_3627_);
lean_ctor_set(v___x_3961_, 2, v_v_4107_);
lean_ctor_set(v___x_3961_, 1, v_k_4106_);
lean_ctor_set(v___x_3961_, 0, v___x_4108_);
v___x_4110_ = v___x_3961_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v___x_4108_);
lean_ctor_set(v_reuseFailAlloc_4111_, 1, v_k_4106_);
lean_ctor_set(v_reuseFailAlloc_4111_, 2, v_v_4107_);
lean_ctor_set(v_reuseFailAlloc_4111_, 3, v_l_3627_);
lean_ctor_set(v_reuseFailAlloc_4111_, 4, v_r_3811_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
}
}
}
else
{
return v_l_3627_;
}
}
else
{
return v_r_3628_;
}
}
default: 
{
lean_object* v_impl_4118_; lean_object* v___x_4119_; 
v_impl_4118_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(v_k_3623_, v_r_3628_);
v___x_4119_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_4118_) == 0)
{
if (lean_obj_tag(v_l_3627_) == 0)
{
lean_object* v_size_4120_; lean_object* v_size_4121_; lean_object* v_k_4122_; lean_object* v_v_4123_; lean_object* v_l_4124_; lean_object* v_r_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; uint8_t v___x_4128_; 
v_size_4120_ = lean_ctor_get(v_impl_4118_, 0);
lean_inc(v_size_4120_);
v_size_4121_ = lean_ctor_get(v_l_3627_, 0);
v_k_4122_ = lean_ctor_get(v_l_3627_, 1);
v_v_4123_ = lean_ctor_get(v_l_3627_, 2);
v_l_4124_ = lean_ctor_get(v_l_3627_, 3);
v_r_4125_ = lean_ctor_get(v_l_3627_, 4);
lean_inc(v_r_4125_);
v___x_4126_ = lean_unsigned_to_nat(3u);
v___x_4127_ = lean_nat_mul(v___x_4126_, v_size_4120_);
v___x_4128_ = lean_nat_dec_lt(v___x_4127_, v_size_4121_);
lean_dec(v___x_4127_);
if (v___x_4128_ == 0)
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4132_; 
lean_dec(v_r_4125_);
v___x_4129_ = lean_nat_add(v___x_4119_, v_size_4121_);
v___x_4130_ = lean_nat_add(v___x_4129_, v_size_4120_);
lean_dec(v_size_4120_);
lean_dec(v___x_4129_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 4, v_impl_4118_);
lean_ctor_set(v___x_3630_, 0, v___x_4130_);
v___x_4132_ = v___x_3630_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4130_);
lean_ctor_set(v_reuseFailAlloc_4133_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_4133_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_4133_, 3, v_l_3627_);
lean_ctor_set(v_reuseFailAlloc_4133_, 4, v_impl_4118_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
else
{
lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4199_; 
lean_inc(v_l_4124_);
lean_inc(v_v_4123_);
lean_inc(v_k_4122_);
lean_inc(v_size_4121_);
v_isSharedCheck_4199_ = !lean_is_exclusive(v_l_3627_);
if (v_isSharedCheck_4199_ == 0)
{
lean_object* v_unused_4200_; lean_object* v_unused_4201_; lean_object* v_unused_4202_; lean_object* v_unused_4203_; lean_object* v_unused_4204_; 
v_unused_4200_ = lean_ctor_get(v_l_3627_, 4);
lean_dec(v_unused_4200_);
v_unused_4201_ = lean_ctor_get(v_l_3627_, 3);
lean_dec(v_unused_4201_);
v_unused_4202_ = lean_ctor_get(v_l_3627_, 2);
lean_dec(v_unused_4202_);
v_unused_4203_ = lean_ctor_get(v_l_3627_, 1);
lean_dec(v_unused_4203_);
v_unused_4204_ = lean_ctor_get(v_l_3627_, 0);
lean_dec(v_unused_4204_);
v___x_4135_ = v_l_3627_;
v_isShared_4136_ = v_isSharedCheck_4199_;
goto v_resetjp_4134_;
}
else
{
lean_dec(v_l_3627_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4199_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v_size_4137_; lean_object* v_size_4138_; lean_object* v_k_4139_; lean_object* v_v_4140_; lean_object* v_l_4141_; lean_object* v_r_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; uint8_t v___x_4145_; 
v_size_4137_ = lean_ctor_get(v_l_4124_, 0);
v_size_4138_ = lean_ctor_get(v_r_4125_, 0);
v_k_4139_ = lean_ctor_get(v_r_4125_, 1);
v_v_4140_ = lean_ctor_get(v_r_4125_, 2);
v_l_4141_ = lean_ctor_get(v_r_4125_, 3);
v_r_4142_ = lean_ctor_get(v_r_4125_, 4);
v___x_4143_ = lean_unsigned_to_nat(2u);
v___x_4144_ = lean_nat_mul(v___x_4143_, v_size_4137_);
v___x_4145_ = lean_nat_dec_lt(v_size_4138_, v___x_4144_);
lean_dec(v___x_4144_);
if (v___x_4145_ == 0)
{
lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4174_; 
lean_inc(v_r_4142_);
lean_inc(v_l_4141_);
lean_inc(v_v_4140_);
lean_inc(v_k_4139_);
v_isSharedCheck_4174_ = !lean_is_exclusive(v_r_4125_);
if (v_isSharedCheck_4174_ == 0)
{
lean_object* v_unused_4175_; lean_object* v_unused_4176_; lean_object* v_unused_4177_; lean_object* v_unused_4178_; lean_object* v_unused_4179_; 
v_unused_4175_ = lean_ctor_get(v_r_4125_, 4);
lean_dec(v_unused_4175_);
v_unused_4176_ = lean_ctor_get(v_r_4125_, 3);
lean_dec(v_unused_4176_);
v_unused_4177_ = lean_ctor_get(v_r_4125_, 2);
lean_dec(v_unused_4177_);
v_unused_4178_ = lean_ctor_get(v_r_4125_, 1);
lean_dec(v_unused_4178_);
v_unused_4179_ = lean_ctor_get(v_r_4125_, 0);
lean_dec(v_unused_4179_);
v___x_4147_ = v_r_4125_;
v_isShared_4148_ = v_isSharedCheck_4174_;
goto v_resetjp_4146_;
}
else
{
lean_dec(v_r_4125_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4174_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___x_4162_; lean_object* v___y_4164_; 
v___x_4149_ = lean_nat_add(v___x_4119_, v_size_4121_);
lean_dec(v_size_4121_);
v___x_4150_ = lean_nat_add(v___x_4149_, v_size_4120_);
lean_dec(v___x_4149_);
v___x_4162_ = lean_nat_add(v___x_4119_, v_size_4137_);
if (lean_obj_tag(v_l_4141_) == 0)
{
lean_object* v_size_4172_; 
v_size_4172_ = lean_ctor_get(v_l_4141_, 0);
lean_inc(v_size_4172_);
v___y_4164_ = v_size_4172_;
goto v___jp_4163_;
}
else
{
lean_object* v___x_4173_; 
v___x_4173_ = lean_unsigned_to_nat(0u);
v___y_4164_ = v___x_4173_;
goto v___jp_4163_;
}
v___jp_4151_:
{
lean_object* v___x_4155_; lean_object* v___x_4157_; 
v___x_4155_ = lean_nat_add(v___y_4153_, v___y_4154_);
lean_dec(v___y_4154_);
lean_dec(v___y_4153_);
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 4, v_impl_4118_);
lean_ctor_set(v___x_4147_, 3, v_r_4142_);
lean_ctor_set(v___x_4147_, 2, v_v_3626_);
lean_ctor_set(v___x_4147_, 1, v_k_3625_);
lean_ctor_set(v___x_4147_, 0, v___x_4155_);
v___x_4157_ = v___x_4147_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4155_);
lean_ctor_set(v_reuseFailAlloc_4161_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_4161_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_4161_, 3, v_r_4142_);
lean_ctor_set(v_reuseFailAlloc_4161_, 4, v_impl_4118_);
v___x_4157_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
lean_object* v___x_4159_; 
if (v_isShared_4136_ == 0)
{
lean_ctor_set(v___x_4135_, 4, v___x_4157_);
lean_ctor_set(v___x_4135_, 3, v___y_4152_);
lean_ctor_set(v___x_4135_, 2, v_v_4140_);
lean_ctor_set(v___x_4135_, 1, v_k_4139_);
lean_ctor_set(v___x_4135_, 0, v___x_4150_);
v___x_4159_ = v___x_4135_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4150_);
lean_ctor_set(v_reuseFailAlloc_4160_, 1, v_k_4139_);
lean_ctor_set(v_reuseFailAlloc_4160_, 2, v_v_4140_);
lean_ctor_set(v_reuseFailAlloc_4160_, 3, v___y_4152_);
lean_ctor_set(v_reuseFailAlloc_4160_, 4, v___x_4157_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
v___jp_4163_:
{
lean_object* v___x_4165_; lean_object* v___x_4167_; 
v___x_4165_ = lean_nat_add(v___x_4162_, v___y_4164_);
lean_dec(v___y_4164_);
lean_dec(v___x_4162_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 4, v_l_4141_);
lean_ctor_set(v___x_3630_, 3, v_l_4124_);
lean_ctor_set(v___x_3630_, 2, v_v_4123_);
lean_ctor_set(v___x_3630_, 1, v_k_4122_);
lean_ctor_set(v___x_3630_, 0, v___x_4165_);
v___x_4167_ = v___x_3630_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v___x_4165_);
lean_ctor_set(v_reuseFailAlloc_4171_, 1, v_k_4122_);
lean_ctor_set(v_reuseFailAlloc_4171_, 2, v_v_4123_);
lean_ctor_set(v_reuseFailAlloc_4171_, 3, v_l_4124_);
lean_ctor_set(v_reuseFailAlloc_4171_, 4, v_l_4141_);
v___x_4167_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
lean_object* v___x_4168_; 
v___x_4168_ = lean_nat_add(v___x_4119_, v_size_4120_);
lean_dec(v_size_4120_);
if (lean_obj_tag(v_r_4142_) == 0)
{
lean_object* v_size_4169_; 
v_size_4169_ = lean_ctor_get(v_r_4142_, 0);
lean_inc(v_size_4169_);
v___y_4152_ = v___x_4167_;
v___y_4153_ = v___x_4168_;
v___y_4154_ = v_size_4169_;
goto v___jp_4151_;
}
else
{
lean_object* v___x_4170_; 
v___x_4170_ = lean_unsigned_to_nat(0u);
v___y_4152_ = v___x_4167_;
v___y_4153_ = v___x_4168_;
v___y_4154_ = v___x_4170_;
goto v___jp_4151_;
}
}
}
}
}
else
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4185_; 
lean_del_object(v___x_3630_);
v___x_4180_ = lean_nat_add(v___x_4119_, v_size_4121_);
lean_dec(v_size_4121_);
v___x_4181_ = lean_nat_add(v___x_4180_, v_size_4120_);
lean_dec(v___x_4180_);
v___x_4182_ = lean_nat_add(v___x_4119_, v_size_4120_);
lean_dec(v_size_4120_);
v___x_4183_ = lean_nat_add(v___x_4182_, v_size_4138_);
lean_dec(v___x_4182_);
lean_inc_ref(v_impl_4118_);
if (v_isShared_4136_ == 0)
{
lean_ctor_set(v___x_4135_, 4, v_impl_4118_);
lean_ctor_set(v___x_4135_, 3, v_r_4125_);
lean_ctor_set(v___x_4135_, 2, v_v_3626_);
lean_ctor_set(v___x_4135_, 1, v_k_3625_);
lean_ctor_set(v___x_4135_, 0, v___x_4183_);
v___x_4185_ = v___x_4135_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v___x_4183_);
lean_ctor_set(v_reuseFailAlloc_4198_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_4198_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_4198_, 3, v_r_4125_);
lean_ctor_set(v_reuseFailAlloc_4198_, 4, v_impl_4118_);
v___x_4185_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4192_; 
v_isSharedCheck_4192_ = !lean_is_exclusive(v_impl_4118_);
if (v_isSharedCheck_4192_ == 0)
{
lean_object* v_unused_4193_; lean_object* v_unused_4194_; lean_object* v_unused_4195_; lean_object* v_unused_4196_; lean_object* v_unused_4197_; 
v_unused_4193_ = lean_ctor_get(v_impl_4118_, 4);
lean_dec(v_unused_4193_);
v_unused_4194_ = lean_ctor_get(v_impl_4118_, 3);
lean_dec(v_unused_4194_);
v_unused_4195_ = lean_ctor_get(v_impl_4118_, 2);
lean_dec(v_unused_4195_);
v_unused_4196_ = lean_ctor_get(v_impl_4118_, 1);
lean_dec(v_unused_4196_);
v_unused_4197_ = lean_ctor_get(v_impl_4118_, 0);
lean_dec(v_unused_4197_);
v___x_4187_ = v_impl_4118_;
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
else
{
lean_dec(v_impl_4118_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4190_; 
if (v_isShared_4188_ == 0)
{
lean_ctor_set(v___x_4187_, 4, v___x_4185_);
lean_ctor_set(v___x_4187_, 3, v_l_4124_);
lean_ctor_set(v___x_4187_, 2, v_v_4123_);
lean_ctor_set(v___x_4187_, 1, v_k_4122_);
lean_ctor_set(v___x_4187_, 0, v___x_4181_);
v___x_4190_ = v___x_4187_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4181_);
lean_ctor_set(v_reuseFailAlloc_4191_, 1, v_k_4122_);
lean_ctor_set(v_reuseFailAlloc_4191_, 2, v_v_4123_);
lean_ctor_set(v_reuseFailAlloc_4191_, 3, v_l_4124_);
lean_ctor_set(v_reuseFailAlloc_4191_, 4, v___x_4185_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_4205_; lean_object* v___x_4206_; lean_object* v___x_4208_; 
v_size_4205_ = lean_ctor_get(v_impl_4118_, 0);
lean_inc(v_size_4205_);
v___x_4206_ = lean_nat_add(v___x_4119_, v_size_4205_);
lean_dec(v_size_4205_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 4, v_impl_4118_);
lean_ctor_set(v___x_3630_, 0, v___x_4206_);
v___x_4208_ = v___x_3630_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4206_);
lean_ctor_set(v_reuseFailAlloc_4209_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_4209_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_4209_, 3, v_l_3627_);
lean_ctor_set(v_reuseFailAlloc_4209_, 4, v_impl_4118_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
else
{
if (lean_obj_tag(v_l_3627_) == 0)
{
lean_object* v_l_4210_; 
v_l_4210_ = lean_ctor_get(v_l_3627_, 3);
if (lean_obj_tag(v_l_4210_) == 0)
{
lean_object* v_r_4211_; 
lean_inc_ref(v_l_4210_);
v_r_4211_ = lean_ctor_get(v_l_3627_, 4);
lean_inc(v_r_4211_);
if (lean_obj_tag(v_r_4211_) == 0)
{
lean_object* v_size_4212_; lean_object* v_k_4213_; lean_object* v_v_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4227_; 
v_size_4212_ = lean_ctor_get(v_l_3627_, 0);
v_k_4213_ = lean_ctor_get(v_l_3627_, 1);
v_v_4214_ = lean_ctor_get(v_l_3627_, 2);
v_isSharedCheck_4227_ = !lean_is_exclusive(v_l_3627_);
if (v_isSharedCheck_4227_ == 0)
{
lean_object* v_unused_4228_; lean_object* v_unused_4229_; 
v_unused_4228_ = lean_ctor_get(v_l_3627_, 4);
lean_dec(v_unused_4228_);
v_unused_4229_ = lean_ctor_get(v_l_3627_, 3);
lean_dec(v_unused_4229_);
v___x_4216_ = v_l_3627_;
v_isShared_4217_ = v_isSharedCheck_4227_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_v_4214_);
lean_inc(v_k_4213_);
lean_inc(v_size_4212_);
lean_dec(v_l_3627_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4227_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v_size_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4222_; 
v_size_4218_ = lean_ctor_get(v_r_4211_, 0);
v___x_4219_ = lean_nat_add(v___x_4119_, v_size_4212_);
lean_dec(v_size_4212_);
v___x_4220_ = lean_nat_add(v___x_4119_, v_size_4218_);
if (v_isShared_4217_ == 0)
{
lean_ctor_set(v___x_4216_, 4, v_impl_4118_);
lean_ctor_set(v___x_4216_, 3, v_r_4211_);
lean_ctor_set(v___x_4216_, 2, v_v_3626_);
lean_ctor_set(v___x_4216_, 1, v_k_3625_);
lean_ctor_set(v___x_4216_, 0, v___x_4220_);
v___x_4222_ = v___x_4216_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4220_);
lean_ctor_set(v_reuseFailAlloc_4226_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_4226_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_4226_, 3, v_r_4211_);
lean_ctor_set(v_reuseFailAlloc_4226_, 4, v_impl_4118_);
v___x_4222_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
lean_object* v___x_4224_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 4, v___x_4222_);
lean_ctor_set(v___x_3630_, 3, v_l_4210_);
lean_ctor_set(v___x_3630_, 2, v_v_4214_);
lean_ctor_set(v___x_3630_, 1, v_k_4213_);
lean_ctor_set(v___x_3630_, 0, v___x_4219_);
v___x_4224_ = v___x_3630_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4219_);
lean_ctor_set(v_reuseFailAlloc_4225_, 1, v_k_4213_);
lean_ctor_set(v_reuseFailAlloc_4225_, 2, v_v_4214_);
lean_ctor_set(v_reuseFailAlloc_4225_, 3, v_l_4210_);
lean_ctor_set(v_reuseFailAlloc_4225_, 4, v___x_4222_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
else
{
lean_object* v_k_4230_; lean_object* v_v_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4242_; 
v_k_4230_ = lean_ctor_get(v_l_3627_, 1);
v_v_4231_ = lean_ctor_get(v_l_3627_, 2);
v_isSharedCheck_4242_ = !lean_is_exclusive(v_l_3627_);
if (v_isSharedCheck_4242_ == 0)
{
lean_object* v_unused_4243_; lean_object* v_unused_4244_; lean_object* v_unused_4245_; 
v_unused_4243_ = lean_ctor_get(v_l_3627_, 4);
lean_dec(v_unused_4243_);
v_unused_4244_ = lean_ctor_get(v_l_3627_, 3);
lean_dec(v_unused_4244_);
v_unused_4245_ = lean_ctor_get(v_l_3627_, 0);
lean_dec(v_unused_4245_);
v___x_4233_ = v_l_3627_;
v_isShared_4234_ = v_isSharedCheck_4242_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_v_4231_);
lean_inc(v_k_4230_);
lean_dec(v_l_3627_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4242_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4235_; lean_object* v___x_4237_; 
v___x_4235_ = lean_unsigned_to_nat(3u);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 3, v_r_4211_);
lean_ctor_set(v___x_4233_, 2, v_v_3626_);
lean_ctor_set(v___x_4233_, 1, v_k_3625_);
lean_ctor_set(v___x_4233_, 0, v___x_4119_);
v___x_4237_ = v___x_4233_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v___x_4119_);
lean_ctor_set(v_reuseFailAlloc_4241_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_4241_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_4241_, 3, v_r_4211_);
lean_ctor_set(v_reuseFailAlloc_4241_, 4, v_r_4211_);
v___x_4237_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
lean_object* v___x_4239_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 4, v___x_4237_);
lean_ctor_set(v___x_3630_, 3, v_l_4210_);
lean_ctor_set(v___x_3630_, 2, v_v_4231_);
lean_ctor_set(v___x_3630_, 1, v_k_4230_);
lean_ctor_set(v___x_3630_, 0, v___x_4235_);
v___x_4239_ = v___x_3630_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4235_);
lean_ctor_set(v_reuseFailAlloc_4240_, 1, v_k_4230_);
lean_ctor_set(v_reuseFailAlloc_4240_, 2, v_v_4231_);
lean_ctor_set(v_reuseFailAlloc_4240_, 3, v_l_4210_);
lean_ctor_set(v_reuseFailAlloc_4240_, 4, v___x_4237_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
}
}
else
{
lean_object* v_r_4246_; 
v_r_4246_ = lean_ctor_get(v_l_3627_, 4);
lean_inc(v_r_4246_);
if (lean_obj_tag(v_r_4246_) == 0)
{
lean_object* v_k_4247_; lean_object* v_v_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4271_; 
lean_inc(v_l_4210_);
v_k_4247_ = lean_ctor_get(v_l_3627_, 1);
v_v_4248_ = lean_ctor_get(v_l_3627_, 2);
v_isSharedCheck_4271_ = !lean_is_exclusive(v_l_3627_);
if (v_isSharedCheck_4271_ == 0)
{
lean_object* v_unused_4272_; lean_object* v_unused_4273_; lean_object* v_unused_4274_; 
v_unused_4272_ = lean_ctor_get(v_l_3627_, 4);
lean_dec(v_unused_4272_);
v_unused_4273_ = lean_ctor_get(v_l_3627_, 3);
lean_dec(v_unused_4273_);
v_unused_4274_ = lean_ctor_get(v_l_3627_, 0);
lean_dec(v_unused_4274_);
v___x_4250_ = v_l_3627_;
v_isShared_4251_ = v_isSharedCheck_4271_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_v_4248_);
lean_inc(v_k_4247_);
lean_dec(v_l_3627_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4271_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v_k_4252_; lean_object* v_v_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4267_; 
v_k_4252_ = lean_ctor_get(v_r_4246_, 1);
v_v_4253_ = lean_ctor_get(v_r_4246_, 2);
v_isSharedCheck_4267_ = !lean_is_exclusive(v_r_4246_);
if (v_isSharedCheck_4267_ == 0)
{
lean_object* v_unused_4268_; lean_object* v_unused_4269_; lean_object* v_unused_4270_; 
v_unused_4268_ = lean_ctor_get(v_r_4246_, 4);
lean_dec(v_unused_4268_);
v_unused_4269_ = lean_ctor_get(v_r_4246_, 3);
lean_dec(v_unused_4269_);
v_unused_4270_ = lean_ctor_get(v_r_4246_, 0);
lean_dec(v_unused_4270_);
v___x_4255_ = v_r_4246_;
v_isShared_4256_ = v_isSharedCheck_4267_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_v_4253_);
lean_inc(v_k_4252_);
lean_dec(v_r_4246_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4267_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4257_; lean_object* v___x_4259_; 
v___x_4257_ = lean_unsigned_to_nat(3u);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 4, v_l_4210_);
lean_ctor_set(v___x_4255_, 3, v_l_4210_);
lean_ctor_set(v___x_4255_, 2, v_v_4248_);
lean_ctor_set(v___x_4255_, 1, v_k_4247_);
lean_ctor_set(v___x_4255_, 0, v___x_4119_);
v___x_4259_ = v___x_4255_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v___x_4119_);
lean_ctor_set(v_reuseFailAlloc_4266_, 1, v_k_4247_);
lean_ctor_set(v_reuseFailAlloc_4266_, 2, v_v_4248_);
lean_ctor_set(v_reuseFailAlloc_4266_, 3, v_l_4210_);
lean_ctor_set(v_reuseFailAlloc_4266_, 4, v_l_4210_);
v___x_4259_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
lean_object* v___x_4261_; 
if (v_isShared_4251_ == 0)
{
lean_ctor_set(v___x_4250_, 4, v_l_4210_);
lean_ctor_set(v___x_4250_, 2, v_v_3626_);
lean_ctor_set(v___x_4250_, 1, v_k_3625_);
lean_ctor_set(v___x_4250_, 0, v___x_4119_);
v___x_4261_ = v___x_4250_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v___x_4119_);
lean_ctor_set(v_reuseFailAlloc_4265_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_4265_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_4265_, 3, v_l_4210_);
lean_ctor_set(v_reuseFailAlloc_4265_, 4, v_l_4210_);
v___x_4261_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
lean_object* v___x_4263_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 4, v___x_4261_);
lean_ctor_set(v___x_3630_, 3, v___x_4259_);
lean_ctor_set(v___x_3630_, 2, v_v_4253_);
lean_ctor_set(v___x_3630_, 1, v_k_4252_);
lean_ctor_set(v___x_3630_, 0, v___x_4257_);
v___x_4263_ = v___x_3630_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4257_);
lean_ctor_set(v_reuseFailAlloc_4264_, 1, v_k_4252_);
lean_ctor_set(v_reuseFailAlloc_4264_, 2, v_v_4253_);
lean_ctor_set(v_reuseFailAlloc_4264_, 3, v___x_4259_);
lean_ctor_set(v_reuseFailAlloc_4264_, 4, v___x_4261_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
}
}
}
else
{
lean_object* v___x_4275_; lean_object* v___x_4277_; 
v___x_4275_ = lean_unsigned_to_nat(2u);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 4, v_r_4246_);
lean_ctor_set(v___x_3630_, 0, v___x_4275_);
v___x_4277_ = v___x_3630_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___x_4275_);
lean_ctor_set(v_reuseFailAlloc_4278_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_4278_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_4278_, 3, v_l_3627_);
lean_ctor_set(v_reuseFailAlloc_4278_, 4, v_r_4246_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
else
{
lean_object* v___x_4280_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 4, v_l_3627_);
lean_ctor_set(v___x_3630_, 0, v___x_4119_);
v___x_4280_ = v___x_3630_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v___x_4119_);
lean_ctor_set(v_reuseFailAlloc_4281_, 1, v_k_3625_);
lean_ctor_set(v_reuseFailAlloc_4281_, 2, v_v_3626_);
lean_ctor_set(v_reuseFailAlloc_4281_, 3, v_l_3627_);
lean_ctor_set(v_reuseFailAlloc_4281_, 4, v_l_3627_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
}
}
}
}
else
{
return v_t_3624_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg___boxed(lean_object* v_k_4284_, lean_object* v_t_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(v_k_4284_, v_t_4285_);
lean_dec(v_k_4284_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1(lean_object* v_init_4287_, lean_object* v_x_4288_){
_start:
{
if (lean_obj_tag(v_x_4288_) == 0)
{
lean_object* v_k_4289_; lean_object* v_l_4290_; lean_object* v_r_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v_k_4289_ = lean_ctor_get(v_x_4288_, 1);
v_l_4290_ = lean_ctor_get(v_x_4288_, 3);
v_r_4291_ = lean_ctor_get(v_x_4288_, 4);
v___x_4292_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1(v_init_4287_, v_l_4290_);
v___x_4293_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(v_k_4289_, v___x_4292_);
v_init_4287_ = v___x_4293_;
v_x_4288_ = v_r_4291_;
goto _start;
}
else
{
return v_init_4287_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1___boxed(lean_object* v_init_4295_, lean_object* v_x_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1(v_init_4295_, v_x_4296_);
lean_dec(v_x_4296_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNon(lean_object* v_names_4298_, lean_object* v_maxSuggestions_4299_, double v_depthFactor_4300_, double v_frequencyWeight_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_){
_start:
{
lean_object* v___x_4307_; lean_object* v_env_4308_; lean_object* v___x_4309_; lean_object* v_toEnvExtension_4310_; lean_object* v_asyncMode_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; 
v___x_4307_ = lean_st_ref_get(v_a_4305_);
v_env_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc_ref(v_env_4308_);
lean_dec(v___x_4307_);
v___x_4309_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerDenyListExt;
v_toEnvExtension_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc_ref(v_toEnvExtension_4310_);
v_asyncMode_4311_ = lean_ctor_get(v_toEnvExtension_4310_, 2);
lean_inc(v_asyncMode_4311_);
lean_dec_ref(v_toEnvExtension_4310_);
v___x_4312_ = lean_box(1);
v___x_4313_ = lean_box(0);
v___x_4314_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4312_, v___x_4309_, v_env_4308_, v_asyncMode_4311_, v___x_4313_);
lean_dec(v_asyncMode_4311_);
v___x_4315_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1(v_names_4298_, v___x_4314_);
v___x_4316_ = lean_box(0);
v___x_4317_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__7(v___x_4316_, v___x_4315_);
v___x_4318_ = l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg(v___x_4317_, v___x_4316_, v_a_4305_);
if (lean_obj_tag(v___x_4318_) == 0)
{
lean_object* v_a_4319_; lean_object* v___f_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
lean_inc(v_a_4319_);
lean_dec_ref(v___x_4318_);
v___f_4320_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___closed__0));
v___x_4321_ = l_Std_TreeSet_ofList___redArg(v_a_4319_, v___f_4320_);
v___x_4322_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1___closed__0));
v___x_4323_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go(v_maxSuggestions_4299_, v_depthFactor_4300_, v_frequencyWeight_4301_, v___x_4314_, v___x_4315_, v___x_4321_, v___x_4322_, v___x_4312_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_);
lean_dec(v___x_4314_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4334_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4326_ = v___x_4323_;
v_isShared_4327_ = v_isSharedCheck_4334_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4323_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4334_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
size_t v_sz_4328_; size_t v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4332_; 
v_sz_4328_ = lean_array_size(v_a_4324_);
v___x_4329_ = ((size_t)0ULL);
v___x_4330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3(v_sz_4328_, v___x_4329_, v_a_4324_);
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 0, v___x_4330_);
v___x_4332_ = v___x_4326_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v___x_4330_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
return v___x_4332_;
}
}
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
v_a_4335_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4323_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4323_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4338_ == 0)
{
v___x_4340_ = v___x_4337_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4335_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
lean_dec(v___x_4315_);
lean_dec(v___x_4314_);
lean_dec(v_a_4305_);
lean_dec_ref(v_a_4304_);
lean_dec(v_a_4303_);
lean_dec_ref(v_a_4302_);
v_a_4343_ = lean_ctor_get(v___x_4318_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___x_4318_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4318_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4348_; 
if (v_isShared_4346_ == 0)
{
v___x_4348_ = v___x_4345_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNon___boxed(lean_object* v_names_4351_, lean_object* v_maxSuggestions_4352_, lean_object* v_depthFactor_4353_, lean_object* v_frequencyWeight_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_){
_start:
{
double v_depthFactor_boxed_4360_; double v_frequencyWeight_boxed_4361_; lean_object* v_res_4362_; 
v_depthFactor_boxed_4360_ = lean_unbox_float(v_depthFactor_4353_);
lean_dec_ref(v_depthFactor_4353_);
v_frequencyWeight_boxed_4361_ = lean_unbox_float(v_frequencyWeight_4354_);
lean_dec_ref(v_frequencyWeight_4354_);
v_res_4362_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNon(v_names_4351_, v_maxSuggestions_4352_, v_depthFactor_boxed_4360_, v_frequencyWeight_boxed_4361_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
lean_dec(v_maxSuggestions_4352_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0(lean_object* v_00_u03b2_4363_, lean_object* v_k_4364_, lean_object* v_t_4365_, lean_object* v_h_4366_){
_start:
{
lean_object* v___x_4367_; 
v___x_4367_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(v_k_4364_, v_t_4365_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___boxed(lean_object* v_00_u03b2_4368_, lean_object* v_k_4369_, lean_object* v_t_4370_, lean_object* v_h_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0(v_00_u03b2_4368_, v_k_4369_, v_t_4370_, v_h_4371_);
lean_dec(v_k_4369_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1(lean_object* v_init_4373_, lean_object* v_t_4374_){
_start:
{
lean_object* v___x_4375_; 
v___x_4375_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1(v_init_4373_, v_t_4374_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1___boxed(lean_object* v_init_4376_, lean_object* v_t_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1(v_init_4376_, v_t_4377_);
lean_dec(v_t_4377_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2(lean_object* v_x_4379_, lean_object* v_x_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_){
_start:
{
lean_object* v___x_4386_; 
v___x_4386_ = l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg(v_x_4379_, v_x_4380_, v___y_4384_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___boxed(lean_object* v_x_4387_, lean_object* v_x_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2(v_x_4387_, v_x_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
return v_res_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_sineQuaNonSelector(double v_depthFactor_4395_, lean_object* v_g_4396_, lean_object* v_config_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_){
_start:
{
lean_object* v___x_4403_; 
lean_inc(v_a_4401_);
lean_inc_ref(v_a_4400_);
lean_inc(v_a_4399_);
lean_inc_ref(v_a_4398_);
v___x_4403_ = l_Lean_MVarId_getRelevantConstants(v_g_4396_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; lean_object* v_maxSuggestions_4405_; double v___x_4406_; lean_object* v___x_4407_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4404_);
lean_dec_ref(v___x_4403_);
v_maxSuggestions_4405_ = lean_ctor_get(v_config_4397_, 0);
lean_inc(v_maxSuggestions_4405_);
lean_dec_ref(v_config_4397_);
v___x_4406_ = lean_float_once(&l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0, &l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0_once, _init_l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0);
v___x_4407_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNon(v_a_4404_, v_maxSuggestions_4405_, v_depthFactor_4395_, v___x_4406_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4417_; 
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4410_ = v___x_4407_;
v_isShared_4411_ = v_isSharedCheck_4417_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4407_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4417_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4415_; 
v___x_4412_ = lean_unsigned_to_nat(0u);
v___x_4413_ = l_Array_extract___redArg(v_a_4408_, v___x_4412_, v_maxSuggestions_4405_);
lean_dec(v_a_4408_);
if (v_isShared_4411_ == 0)
{
lean_ctor_set(v___x_4410_, 0, v___x_4413_);
v___x_4415_ = v___x_4410_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v___x_4413_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
else
{
lean_dec(v_maxSuggestions_4405_);
return v___x_4407_;
}
}
else
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4425_; 
lean_dec(v_a_4401_);
lean_dec_ref(v_a_4400_);
lean_dec(v_a_4399_);
lean_dec_ref(v_a_4398_);
lean_dec_ref(v_config_4397_);
v_a_4418_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4420_ = v___x_4403_;
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4403_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4423_; 
if (v_isShared_4421_ == 0)
{
v___x_4423_ = v___x_4420_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_sineQuaNonSelector___boxed(lean_object* v_depthFactor_4426_, lean_object* v_g_4427_, lean_object* v_config_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_){
_start:
{
double v_depthFactor_boxed_4434_; lean_object* v_res_4435_; 
v_depthFactor_boxed_4434_ = lean_unbox_float(v_depthFactor_4426_);
lean_dec_ref(v_depthFactor_4426_);
v_res_4435_ = l_Lean_LibrarySuggestions_sineQuaNonSelector(v_depthFactor_boxed_4434_, v_g_4427_, v_config_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_);
return v_res_4435_;
}
}
lean_object* runtime_initialize_Lean_LibrarySuggestions_SymbolFrequency(uint8_t builtin);
lean_object* runtime_initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LibrarySuggestions_SineQuaNon(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LibrarySuggestions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_830398421____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerDenyListExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerDenyListExt);
lean_dec_ref(res);
l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols___closed__0___boxed__const__1 = _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols___closed__0___boxed__const__1);
l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___boxed__const__1 = _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___boxed__const__1();
lean_mark_persistent(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___boxed__const__1);
res = l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt);
lean_dec_ref(res);
res = l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_228879371____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersRef);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_LibrarySuggestions_SineQuaNon(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3 = _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3();
lean_mark_persistent(l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___auto__3);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_LibrarySuggestions_SymbolFrequency(uint8_t builtin);
lean_object* initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LibrarySuggestions_SineQuaNon(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LibrarySuggestions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LibrarySuggestions_SineQuaNon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_LibrarySuggestions_SineQuaNon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_LibrarySuggestions_SineQuaNon(builtin);
}
#ifdef __cplusplus
}
#endif
