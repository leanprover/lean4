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
static const lean_array_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "sine qua non premise selection extension"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "sineQueNon"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(67, 84, 59, 241, 113, 198, 42, 47)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_array_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2__value)}};
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
double v___y_2993__boxed_353_; double v_maxTolerance_boxed_354_; size_t v_i_boxed_355_; size_t v_stop_boxed_356_; lean_object* v_res_357_; 
v___y_2993__boxed_353_ = lean_unbox_float(v___y_347_);
lean_dec_ref(v___y_347_);
v_maxTolerance_boxed_354_ = lean_unbox_float(v_maxTolerance_348_);
lean_dec_ref(v_maxTolerance_348_);
v_i_boxed_355_ = lean_unbox_usize(v_i_350_);
lean_dec(v_i_350_);
v_stop_boxed_356_ = lean_unbox_usize(v_stop_351_);
lean_dec(v_stop_351_);
v_res_357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1_spec__2(v___y_2993__boxed_353_, v_maxTolerance_boxed_354_, v_as_349_, v_i_boxed_355_, v_stop_boxed_356_, v_b_352_);
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
double v___y_3046__boxed_381_; double v_maxTolerance_boxed_382_; lean_object* v_res_383_; 
v___y_3046__boxed_381_ = lean_unbox_float(v___y_376_);
lean_dec_ref(v___y_376_);
v_maxTolerance_boxed_382_ = lean_unbox_float(v_maxTolerance_377_);
lean_dec_ref(v_maxTolerance_377_);
v_res_383_ = l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1(v___y_3046__boxed_381_, v_maxTolerance_boxed_382_, v_as_378_, v_start_379_, v_stop_380_);
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
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
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
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
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
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
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
lean_object* v_fileName_1027_; lean_object* v_fileMap_1028_; lean_object* v_options_1029_; lean_object* v_currRecDepth_1030_; lean_object* v_maxRecDepth_1031_; lean_object* v_ref_1032_; lean_object* v_currNamespace_1033_; lean_object* v_openDecls_1034_; lean_object* v_initHeartbeats_1035_; lean_object* v_maxHeartbeats_1036_; lean_object* v_quotContext_1037_; lean_object* v_currMacroScope_1038_; uint8_t v_diag_1039_; lean_object* v_cancelTk_x3f_1040_; uint8_t v_suppressElabErrors_1041_; lean_object* v_inheritedTraceOptions_1042_; lean_object* v_ref_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
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
v_ref_1043_ = l_Lean_replaceRef(v_ref_1020_, v_ref_1032_);
lean_inc_ref(v_inheritedTraceOptions_1042_);
lean_inc(v_cancelTk_x3f_1040_);
lean_inc(v_currMacroScope_1038_);
lean_inc(v_quotContext_1037_);
lean_inc(v_maxHeartbeats_1036_);
lean_inc(v_initHeartbeats_1035_);
lean_inc(v_openDecls_1034_);
lean_inc(v_currNamespace_1033_);
lean_inc(v_maxRecDepth_1031_);
lean_inc(v_currRecDepth_1030_);
lean_inc_ref(v_options_1029_);
lean_inc_ref(v_fileMap_1028_);
lean_inc_ref(v_fileName_1027_);
v___x_1044_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1044_, 0, v_fileName_1027_);
lean_ctor_set(v___x_1044_, 1, v_fileMap_1028_);
lean_ctor_set(v___x_1044_, 2, v_options_1029_);
lean_ctor_set(v___x_1044_, 3, v_currRecDepth_1030_);
lean_ctor_set(v___x_1044_, 4, v_maxRecDepth_1031_);
lean_ctor_set(v___x_1044_, 5, v_ref_1043_);
lean_ctor_set(v___x_1044_, 6, v_currNamespace_1033_);
lean_ctor_set(v___x_1044_, 7, v_openDecls_1034_);
lean_ctor_set(v___x_1044_, 8, v_initHeartbeats_1035_);
lean_ctor_set(v___x_1044_, 9, v_maxHeartbeats_1036_);
lean_ctor_set(v___x_1044_, 10, v_quotContext_1037_);
lean_ctor_set(v___x_1044_, 11, v_currMacroScope_1038_);
lean_ctor_set(v___x_1044_, 12, v_cancelTk_x3f_1040_);
lean_ctor_set(v___x_1044_, 13, v_inheritedTraceOptions_1042_);
lean_ctor_set_uint8(v___x_1044_, sizeof(void*)*14, v_diag_1039_);
lean_ctor_set_uint8(v___x_1044_, sizeof(void*)*14 + 1, v_suppressElabErrors_1041_);
v___x_1045_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(v_msg_1021_, v___y_1022_, v___y_1023_, v___x_1044_, v___y_1025_);
lean_dec_ref(v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1046_, lean_object* v_msg_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_1046_, v_msg_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v_ref_1046_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_ref_1054_, lean_object* v_msg_1055_, lean_object* v_declHint_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; lean_object* v_a_1063_; lean_object* v___x_1064_; 
v___x_1062_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6(v_msg_1055_, v_declHint_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref(v___x_1062_);
v___x_1064_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_1054_, v_a_1063_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_ref_1065_, lean_object* v_msg_1066_, lean_object* v_declHint_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_1065_, v_msg_1066_, v_declHint_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v_ref_1065_);
return v_res_1073_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1076_ = l_Lean_stringToMessageData(v___x_1075_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1079_ = l_Lean_stringToMessageData(v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1080_, lean_object* v_constName_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1087_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1088_ = 0;
lean_inc(v_constName_1081_);
v___x_1089_ = l_Lean_MessageData_ofConstName(v_constName_1081_, v___x_1088_);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1087_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_1080_, v___x_1092_, v_constName_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1094_, lean_object* v_constName_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg(v_ref_1094_, v_constName_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v_ref_1094_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0___redArg(lean_object* v_constName_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_ref_1108_; lean_object* v___x_1109_; 
v_ref_1108_ = lean_ctor_get(v___y_1105_, 5);
v___x_1109_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg(v_ref_1108_, v_constName_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0___redArg(v_constName_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0(lean_object* v_constName_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v___x_1123_; lean_object* v_env_1124_; uint8_t v___x_1125_; lean_object* v___x_1126_; 
v___x_1123_ = lean_st_ref_get(v___y_1121_);
v_env_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc_ref(v_env_1124_);
lean_dec(v___x_1123_);
v___x_1125_ = 0;
lean_inc(v_constName_1117_);
v___x_1126_ = l_Lean_Environment_find_x3f(v_env_1124_, v_constName_1117_, v___x_1125_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0___redArg(v_constName_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
return v___x_1127_;
}
else
{
lean_object* v_val_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec(v_constName_1117_);
v_val_1128_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1126_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_val_1128_);
lean_dec(v___x_1126_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 0);
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_val_1128_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0___boxed(lean_object* v_constName_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0(v_constName_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__2(double v_maxTolerance_1143_, lean_object* v_as_1144_, size_t v_sz_1145_, size_t v_i_1146_, lean_object* v_b_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
uint8_t v___x_1153_; 
v___x_1153_ = lean_usize_dec_lt(v_i_1146_, v_sz_1145_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v_b_1147_);
return v___x_1154_;
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1156_; 
v_a_1155_ = lean_array_uget_borrowed(v_as_1144_, v_i_1146_);
lean_inc(v_a_1155_);
v___x_1156_ = l_Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0(v_a_1155_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1158_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref(v___x_1156_);
v___x_1158_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols(v_a_1157_, v_maxTolerance_1143_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v_a_1157_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; size_t v_sz_1160_; size_t v___x_1161_; lean_object* v___x_1162_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref(v___x_1158_);
v_sz_1160_ = lean_array_size(v_a_1159_);
v___x_1161_ = ((size_t)0ULL);
lean_inc(v_a_1155_);
v___x_1162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__1___redArg(v_a_1155_, v_a_1159_, v_sz_1160_, v___x_1161_, v_b_1147_);
lean_dec(v_a_1159_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; size_t v___x_1164_; size_t v___x_1165_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref(v___x_1162_);
v___x_1164_ = ((size_t)1ULL);
v___x_1165_ = lean_usize_add(v_i_1146_, v___x_1164_);
v_i_1146_ = v___x_1165_;
v_b_1147_ = v_a_1163_;
goto _start;
}
else
{
return v___x_1162_;
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v_b_1147_);
v_a_1167_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1158_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1158_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec(v_b_1147_);
v_a_1175_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1156_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1156_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__2___boxed(lean_object* v_maxTolerance_1183_, lean_object* v_as_1184_, lean_object* v_sz_1185_, lean_object* v_i_1186_, lean_object* v_b_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
double v_maxTolerance_boxed_1193_; size_t v_sz_boxed_1194_; size_t v_i_boxed_1195_; lean_object* v_res_1196_; 
v_maxTolerance_boxed_1193_ = lean_unbox_float(v_maxTolerance_1183_);
lean_dec_ref(v_maxTolerance_1183_);
v_sz_boxed_1194_ = lean_unbox_usize(v_sz_1185_);
lean_dec(v_sz_1185_);
v_i_boxed_1195_ = lean_unbox_usize(v_i_1186_);
lean_dec(v_i_1186_);
v_res_1196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__2(v_maxTolerance_boxed_1193_, v_as_1184_, v_sz_boxed_1194_, v_i_boxed_1195_, v_b_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec_ref(v_as_1184_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers(lean_object* v_names_1199_, double v_maxTolerance_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v___x_1206_; lean_object* v_map_1207_; lean_object* v___y_1209_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1206_ = lean_st_ref_get(v_a_1204_);
v_map_1207_ = lean_box(1);
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = lean_array_get_size(v_names_1199_);
v___x_1215_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers___closed__0));
v___x_1216_ = lean_nat_dec_lt(v___x_1213_, v___x_1214_);
if (v___x_1216_ == 0)
{
lean_dec(v___x_1206_);
v___y_1209_ = v___x_1215_;
goto v___jp_1208_;
}
else
{
lean_object* v_env_1217_; uint8_t v___x_1218_; 
v_env_1217_ = lean_ctor_get(v___x_1206_, 0);
lean_inc_ref(v_env_1217_);
lean_dec(v___x_1206_);
v___x_1218_ = lean_nat_dec_le(v___x_1214_, v___x_1214_);
if (v___x_1218_ == 0)
{
if (v___x_1216_ == 0)
{
lean_dec_ref(v_env_1217_);
v___y_1209_ = v___x_1215_;
goto v___jp_1208_;
}
else
{
size_t v___x_1219_; size_t v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = ((size_t)0ULL);
v___x_1220_ = lean_usize_of_nat(v___x_1214_);
v___x_1221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__3(v_env_1217_, v_names_1199_, v___x_1219_, v___x_1220_, v___x_1215_);
v___y_1209_ = v___x_1221_;
goto v___jp_1208_;
}
}
else
{
size_t v___x_1222_; size_t v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = ((size_t)0ULL);
v___x_1223_ = lean_usize_of_nat(v___x_1214_);
v___x_1224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__3(v_env_1217_, v_names_1199_, v___x_1222_, v___x_1223_, v___x_1215_);
v___y_1209_ = v___x_1224_;
goto v___jp_1208_;
}
}
v___jp_1208_:
{
size_t v_sz_1210_; size_t v___x_1211_; lean_object* v___x_1212_; 
v_sz_1210_ = lean_array_size(v___y_1209_);
v___x_1211_ = ((size_t)0ULL);
v___x_1212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__2(v_maxTolerance_1200_, v___y_1209_, v_sz_1210_, v___x_1211_, v_map_1207_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
lean_dec_ref(v___y_1209_);
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers___boxed(lean_object* v_names_1225_, lean_object* v_maxTolerance_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
double v_maxTolerance_boxed_1232_; lean_object* v_res_1233_; 
v_maxTolerance_boxed_1232_ = lean_unbox_float(v_maxTolerance_1226_);
lean_dec_ref(v_maxTolerance_1226_);
v_res_1233_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers(v_names_1225_, v_maxTolerance_boxed_1232_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec_ref(v_names_1225_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__1(lean_object* v_a_1234_, lean_object* v_as_1235_, size_t v_sz_1236_, size_t v_i_1237_, lean_object* v_b_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__1___redArg(v_a_1234_, v_as_1235_, v_sz_1236_, v_i_1237_, v_b_1238_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__1___boxed(lean_object* v_a_1245_, lean_object* v_as_1246_, lean_object* v_sz_1247_, lean_object* v_i_1248_, lean_object* v_b_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
size_t v_sz_boxed_1255_; size_t v_i_boxed_1256_; lean_object* v_res_1257_; 
v_sz_boxed_1255_ = lean_unbox_usize(v_sz_1247_);
lean_dec(v_sz_1247_);
v_i_boxed_1256_ = lean_unbox_usize(v_i_1248_);
lean_dec(v_i_1248_);
v_res_1257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__1(v_a_1245_, v_as_1246_, v_sz_boxed_1255_, v_i_boxed_1256_, v_b_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec_ref(v_as_1246_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0(lean_object* v_00_u03b1_1258_, lean_object* v_constName_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0___redArg(v_constName_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1266_, lean_object* v_constName_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0(v_00_u03b1_1266_, v_constName_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1274_, lean_object* v_ref_1275_, lean_object* v_constName_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___redArg(v_ref_1275_, v_constName_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1283_, lean_object* v_ref_1284_, lean_object* v_constName_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1(v_00_u03b1_1283_, v_ref_1284_, v_constName_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v_ref_1284_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b1_1292_, lean_object* v_ref_1293_, lean_object* v_msg_1294_, lean_object* v_declHint_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_1293_, v_msg_1294_, v_declHint_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b1_1302_, lean_object* v_ref_1303_, lean_object* v_msg_1304_, lean_object* v_declHint_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5(v_00_u03b1_1302_, v_ref_1303_, v_msg_1304_, v_declHint_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v_ref_1303_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7(lean_object* v_msg_1312_, lean_object* v_declHint_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___redArg(v_msg_1312_, v_declHint_1313_, v___y_1317_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_1320_, lean_object* v_declHint_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__6_spec__7(v_msg_1320_, v_declHint_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_1328_, lean_object* v_ref_1329_, lean_object* v_msg_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_1329_, v_msg_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1337_, lean_object* v_ref_1338_, lean_object* v_msg_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7(v_00_u03b1_1337_, v_ref_1338_, v_msg_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v_ref_1338_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_1346_, lean_object* v_msg_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(v_msg_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1354_, lean_object* v_msg_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9(v_00_u03b1_1354_, v_msg_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers_spec__0(lean_object* v_x_1362_, lean_object* v_x_1363_){
_start:
{
if (lean_obj_tag(v_x_1363_) == 0)
{
return v_x_1362_;
}
else
{
lean_object* v_head_1364_; lean_object* v_tail_1365_; lean_object* v___f_1366_; lean_object* v___x_1367_; 
v_head_1364_ = lean_ctor_get(v_x_1363_, 0);
lean_inc(v_head_1364_);
v_tail_1365_ = lean_ctor_get(v_x_1363_, 1);
lean_inc(v_tail_1365_);
lean_dec_ref(v_x_1363_);
v___f_1366_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_insertTrigger___closed__0));
v___x_1367_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__List_orderedInsert___redArg(v___f_1366_, v_head_1364_, v_x_1362_);
v_x_1362_ = v___x_1367_;
v_x_1363_ = v_tail_1365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers_spec__1(lean_object* v_map_u2081_1369_, lean_object* v_init_1370_, lean_object* v_x_1371_){
_start:
{
if (lean_obj_tag(v_x_1371_) == 0)
{
lean_object* v_k_1372_; lean_object* v_v_1373_; lean_object* v_l_1374_; lean_object* v_r_1375_; lean_object* v___x_1376_; lean_object* v_a_1377_; lean_object* v___x_1378_; 
v_k_1372_ = lean_ctor_get(v_x_1371_, 1);
lean_inc(v_k_1372_);
v_v_1373_ = lean_ctor_get(v_x_1371_, 2);
lean_inc(v_v_1373_);
v_l_1374_ = lean_ctor_get(v_x_1371_, 3);
lean_inc(v_l_1374_);
v_r_1375_ = lean_ctor_get(v_x_1371_, 4);
lean_inc(v_r_1375_);
lean_dec_ref(v_x_1371_);
v___x_1376_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers_spec__1(v_map_u2081_1369_, v_init_1370_, v_l_1374_);
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref(v___x_1376_);
v___x_1378_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_u2081_1369_, v_k_1372_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1372_, v_v_1373_, v_a_1377_);
v_init_1370_ = v___x_1379_;
v_x_1371_ = v_r_1375_;
goto _start;
}
else
{
lean_object* v_val_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_val_1381_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_val_1381_);
lean_dec_ref(v___x_1378_);
v___x_1382_ = l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers_spec__0(v_val_1381_, v_v_1373_);
v___x_1383_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1372_, v___x_1382_, v_a_1377_);
v_init_1370_ = v___x_1383_;
v_x_1371_ = v_r_1375_;
goto _start;
}
}
else
{
lean_object* v___x_1385_; 
v___x_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1385_, 0, v_init_1370_);
return v___x_1385_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers_spec__1___boxed(lean_object* v_map_u2081_1386_, lean_object* v_init_1387_, lean_object* v_x_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers_spec__1(v_map_u2081_1386_, v_init_1387_, v_x_1388_);
lean_dec(v_map_u2081_1386_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers(lean_object* v_map_u2081_1390_, lean_object* v_map_u2082_1391_){
_start:
{
lean_object* v___x_1392_; lean_object* v_a_1393_; 
lean_inc(v_map_u2081_1390_);
v___x_1392_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers_spec__1(v_map_u2081_1390_, v_map_u2081_1390_, v_map_u2082_1391_);
lean_dec(v_map_u2081_1390_);
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref(v___x_1392_);
return v_a_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___lam__0(lean_object* v___x_1394_, double v___x_1395_, lean_object* v___x_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers(v___x_1394_, v___x_1395_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1412_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1412_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1412_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1407_ = lean_mk_empty_array_with_capacity(v___x_1396_);
v___x_1408_ = lean_array_push(v___x_1407_, v_a_1403_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1408_);
v___x_1410_ = v___x_1405_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
v_a_1413_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1402_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1402_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___lam__0___boxed(lean_object* v___x_1421_, lean_object* v___x_1422_, lean_object* v___x_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
double v___x_852__boxed_1429_; lean_object* v_res_1430_; 
v___x_852__boxed_1429_ = lean_unbox_float(v___x_1422_);
lean_dec_ref(v___x_1422_);
v_res_1430_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___lam__0(v___x_1421_, v___x_852__boxed_1429_, v___x_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___x_1423_);
lean_dec_ref(v___x_1421_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__1(size_t v_sz_1431_, size_t v_i_1432_, lean_object* v_bs_1433_){
_start:
{
uint8_t v___x_1434_; 
v___x_1434_ = lean_usize_dec_lt(v_i_1432_, v_sz_1431_);
if (v___x_1434_ == 0)
{
return v_bs_1433_;
}
else
{
lean_object* v_v_1435_; lean_object* v_fst_1436_; lean_object* v___x_1437_; lean_object* v_bs_x27_1438_; size_t v___x_1439_; size_t v___x_1440_; lean_object* v___x_1441_; 
v_v_1435_ = lean_array_uget_borrowed(v_bs_1433_, v_i_1432_);
v_fst_1436_ = lean_ctor_get(v_v_1435_, 0);
lean_inc(v_fst_1436_);
v___x_1437_ = lean_unsigned_to_nat(0u);
v_bs_x27_1438_ = lean_array_uset(v_bs_1433_, v_i_1432_, v___x_1437_);
v___x_1439_ = ((size_t)1ULL);
v___x_1440_ = lean_usize_add(v_i_1432_, v___x_1439_);
v___x_1441_ = lean_array_uset(v_bs_x27_1438_, v_i_1432_, v_fst_1436_);
v_i_1432_ = v___x_1440_;
v_bs_1433_ = v___x_1441_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__1___boxed(lean_object* v_sz_1443_, lean_object* v_i_1444_, lean_object* v_bs_1445_){
_start:
{
size_t v_sz_boxed_1446_; size_t v_i_boxed_1447_; lean_object* v_res_1448_; 
v_sz_boxed_1446_ = lean_unbox_usize(v_sz_1443_);
lean_dec(v_sz_1443_);
v_i_boxed_1447_ = lean_unbox_usize(v_i_1444_);
lean_dec(v_i_1444_);
v_res_1448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__1(v_sz_boxed_1446_, v_i_boxed_1447_, v_bs_1445_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg___lam__0(lean_object* v_f_1449_, lean_object* v_x1_1450_, lean_object* v_x2_1451_, lean_object* v_x3_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_apply_3(v_f_1449_, v_x1_1450_, v_x2_1451_, v_x3_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_f_1454_, lean_object* v_keys_1455_, lean_object* v_vals_1456_, lean_object* v_i_1457_, lean_object* v_acc_1458_){
_start:
{
lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1459_ = lean_array_get_size(v_keys_1455_);
v___x_1460_ = lean_nat_dec_lt(v_i_1457_, v___x_1459_);
if (v___x_1460_ == 0)
{
lean_dec(v_i_1457_);
lean_dec(v_f_1454_);
return v_acc_1458_;
}
else
{
lean_object* v_k_1461_; lean_object* v_v_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_k_1461_ = lean_array_fget_borrowed(v_keys_1455_, v_i_1457_);
v_v_1462_ = lean_array_fget_borrowed(v_vals_1456_, v_i_1457_);
lean_inc(v_f_1454_);
lean_inc(v_v_1462_);
lean_inc(v_k_1461_);
v___x_1463_ = lean_apply_3(v_f_1454_, v_acc_1458_, v_k_1461_, v_v_1462_);
v___x_1464_ = lean_unsigned_to_nat(1u);
v___x_1465_ = lean_nat_add(v_i_1457_, v___x_1464_);
lean_dec(v_i_1457_);
v_i_1457_ = v___x_1465_;
v_acc_1458_ = v___x_1463_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_f_1467_, lean_object* v_keys_1468_, lean_object* v_vals_1469_, lean_object* v_i_1470_, lean_object* v_acc_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_1467_, v_keys_1468_, v_vals_1469_, v_i_1470_, v_acc_1471_);
lean_dec_ref(v_vals_1469_);
lean_dec_ref(v_keys_1468_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_1473_, lean_object* v_x_1474_, lean_object* v_x_1475_){
_start:
{
if (lean_obj_tag(v_x_1474_) == 0)
{
lean_object* v_es_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v_es_1476_ = lean_ctor_get(v_x_1474_, 0);
v___x_1477_ = lean_unsigned_to_nat(0u);
v___x_1478_ = lean_array_get_size(v_es_1476_);
v___x_1479_ = lean_nat_dec_lt(v___x_1477_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_dec(v_f_1473_);
return v_x_1475_;
}
else
{
uint8_t v___x_1480_; 
v___x_1480_ = lean_nat_dec_le(v___x_1478_, v___x_1478_);
if (v___x_1480_ == 0)
{
if (v___x_1479_ == 0)
{
lean_dec(v_f_1473_);
return v_x_1475_;
}
else
{
size_t v___x_1481_; size_t v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = ((size_t)0ULL);
v___x_1482_ = lean_usize_of_nat(v___x_1478_);
v___x_1483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_f_1473_, v_es_1476_, v___x_1481_, v___x_1482_, v_x_1475_);
return v___x_1483_;
}
}
else
{
size_t v___x_1484_; size_t v___x_1485_; lean_object* v___x_1486_; 
v___x_1484_ = ((size_t)0ULL);
v___x_1485_ = lean_usize_of_nat(v___x_1478_);
v___x_1486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_f_1473_, v_es_1476_, v___x_1484_, v___x_1485_, v_x_1475_);
return v___x_1486_;
}
}
}
else
{
lean_object* v_ks_1487_; lean_object* v_vs_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v_ks_1487_ = lean_ctor_get(v_x_1474_, 0);
v_vs_1488_ = lean_ctor_get(v_x_1474_, 1);
v___x_1489_ = lean_unsigned_to_nat(0u);
v___x_1490_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_1473_, v_ks_1487_, v_vs_1488_, v___x_1489_, v_x_1475_);
return v___x_1490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_f_1491_, lean_object* v_as_1492_, size_t v_i_1493_, size_t v_stop_1494_, lean_object* v_b_1495_){
_start:
{
lean_object* v___y_1497_; uint8_t v___x_1501_; 
v___x_1501_ = lean_usize_dec_eq(v_i_1493_, v_stop_1494_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_array_uget_borrowed(v_as_1492_, v_i_1493_);
switch(lean_obj_tag(v___x_1502_))
{
case 0:
{
lean_object* v_key_1503_; lean_object* v_val_1504_; lean_object* v___x_1505_; 
v_key_1503_ = lean_ctor_get(v___x_1502_, 0);
v_val_1504_ = lean_ctor_get(v___x_1502_, 1);
lean_inc(v_f_1491_);
lean_inc(v_val_1504_);
lean_inc(v_key_1503_);
v___x_1505_ = lean_apply_3(v_f_1491_, v_b_1495_, v_key_1503_, v_val_1504_);
v___y_1497_ = v___x_1505_;
goto v___jp_1496_;
}
case 1:
{
lean_object* v_node_1506_; lean_object* v___x_1507_; 
v_node_1506_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_f_1491_);
v___x_1507_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1491_, v_node_1506_, v_b_1495_);
v___y_1497_ = v___x_1507_;
goto v___jp_1496_;
}
default: 
{
v___y_1497_ = v_b_1495_;
goto v___jp_1496_;
}
}
}
else
{
lean_dec(v_f_1491_);
return v_b_1495_;
}
v___jp_1496_:
{
size_t v___x_1498_; size_t v___x_1499_; 
v___x_1498_ = ((size_t)1ULL);
v___x_1499_ = lean_usize_add(v_i_1493_, v___x_1498_);
v_i_1493_ = v___x_1499_;
v_b_1495_ = v___y_1497_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_f_1508_, lean_object* v_as_1509_, lean_object* v_i_1510_, lean_object* v_stop_1511_, lean_object* v_b_1512_){
_start:
{
size_t v_i_boxed_1513_; size_t v_stop_boxed_1514_; lean_object* v_res_1515_; 
v_i_boxed_1513_ = lean_unbox_usize(v_i_1510_);
lean_dec(v_i_1510_);
v_stop_boxed_1514_ = lean_unbox_usize(v_stop_1511_);
lean_dec(v_stop_1511_);
v_res_1515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_f_1508_, v_as_1509_, v_i_boxed_1513_, v_stop_boxed_1514_, v_b_1512_);
lean_dec_ref(v_as_1509_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_1516_, lean_object* v_x_1517_, lean_object* v_x_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1516_, v_x_1517_, v_x_1518_);
lean_dec_ref(v_x_1517_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg(lean_object* v_map_1520_, lean_object* v_f_1521_, lean_object* v_init_1522_){
_start:
{
lean_object* v___f_1523_; lean_object* v___x_1524_; 
v___f_1523_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1523_, 0, v_f_1521_);
v___x_1524_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(v___f_1523_, v_map_1520_, v_init_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg___boxed(lean_object* v_map_1525_, lean_object* v_f_1526_, lean_object* v_init_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg(v_map_1525_, v_f_1526_, v_init_1527_);
lean_dec_ref(v_map_1525_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg___lam__0(lean_object* v_ps_1529_, lean_object* v_k_1530_, lean_object* v_v_1531_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v_k_1530_);
lean_ctor_set(v___x_1532_, 1, v_v_1531_);
v___x_1533_ = lean_array_push(v_ps_1529_, v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg(lean_object* v_m_1537_){
_start:
{
lean_object* v___f_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___f_1538_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg___closed__0));
v___x_1539_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg___closed__1));
v___x_1540_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg(v_m_1537_, v___f_1538_, v___x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg___boxed(lean_object* v_m_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg(v_m_1541_);
lean_dec_ref(v_m_1541_);
return v_res_1542_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__0(void){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Array_instInhabited(lean_box(0));
return v___x_1543_;
}
}
static double _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__1(void){
_start:
{
lean_object* v___x_1544_; uint8_t v___x_1545_; lean_object* v___x_1546_; double v___x_1547_; 
v___x_1544_ = lean_unsigned_to_nat(1u);
v___x_1545_ = 1;
v___x_1546_ = lean_unsigned_to_nat(30u);
v___x_1547_ = l_Float_ofScientific(v___x_1546_, v___x_1545_, v___x_1544_);
return v___x_1547_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___boxed__const__1(void){
_start:
{
double v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_float_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__1, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__1_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__1);
v___x_1549_ = lean_box_float(v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3(lean_object* v_env_1550_){
_start:
{
lean_object* v___x_1551_; lean_object* v_map_u2082_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; size_t v_sz_1555_; size_t v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___f_1560_; lean_object* v___x_1561_; 
lean_inc_ref(v_env_1550_);
v___x_1551_ = l_Lean_Environment_constants(v_env_1550_);
v_map_u2082_1552_ = lean_ctor_get(v___x_1551_, 1);
lean_inc_ref(v_map_u2082_1552_);
lean_dec_ref(v___x_1551_);
v___x_1553_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__0, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__0_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___closed__0);
v___x_1554_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg(v_map_u2082_1552_);
lean_dec_ref(v_map_u2082_1552_);
v_sz_1555_ = lean_array_size(v___x_1554_);
v___x_1556_ = ((size_t)0ULL);
v___x_1557_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__1(v_sz_1555_, v___x_1556_, v___x_1554_);
v___x_1558_ = lean_unsigned_to_nat(1u);
v___x_1559_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___boxed__const__1;
v___f_1560_ = lean_alloc_closure((void*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1560_, 0, v___x_1557_);
lean_closure_set(v___f_1560_, 1, v___x_1559_);
lean_closure_set(v___f_1560_, 2, v___x_1558_);
v___x_1561_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v___x_1553_, v_env_1550_, v___f_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0(lean_object* v_00_u03b2_1562_, lean_object* v_m_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg(v_m_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___boxed(lean_object* v_00_u03b2_1565_, lean_object* v_m_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0(v_00_u03b2_1565_, v_m_1566_);
lean_dec_ref(v_m_1566_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0(lean_object* v_00_u03c3_1568_, lean_object* v_00_u03b2_1569_, lean_object* v_map_1570_, lean_object* v_f_1571_, lean_object* v_init_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg(v_map_1570_, v_f_1571_, v_init_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___boxed(lean_object* v_00_u03c3_1574_, lean_object* v_00_u03b2_1575_, lean_object* v_map_1576_, lean_object* v_f_1577_, lean_object* v_init_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0(v_00_u03c3_1574_, v_00_u03b2_1575_, v_map_1576_, v_f_1577_, v_init_1578_);
lean_dec_ref(v_map_1576_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1___redArg(lean_object* v_map_1580_, lean_object* v_f_1581_, lean_object* v_init_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1581_, v_map_1580_, v_init_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_1584_, lean_object* v_f_1585_, lean_object* v_init_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1___redArg(v_map_1584_, v_f_1585_, v_init_1586_);
lean_dec_ref(v_map_1584_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_1588_, lean_object* v_00_u03b2_1589_, lean_object* v_map_1590_, lean_object* v_f_1591_, lean_object* v_init_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1591_, v_map_1590_, v_init_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1594_, lean_object* v_00_u03b2_1595_, lean_object* v_map_1596_, lean_object* v_f_1597_, lean_object* v_init_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1(v_00_u03c3_1594_, v_00_u03b2_1595_, v_map_1596_, v_f_1597_, v_init_1598_);
lean_dec_ref(v_map_1596_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_1600_, lean_object* v_00_u03b1_1601_, lean_object* v_00_u03b2_1602_, lean_object* v_f_1603_, lean_object* v_x_1604_, lean_object* v_x_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1603_, v_x_1604_, v_x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_1607_, lean_object* v_00_u03b1_1608_, lean_object* v_00_u03b2_1609_, lean_object* v_f_1610_, lean_object* v_x_1611_, lean_object* v_x_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_1607_, v_00_u03b1_1608_, v_00_u03b2_1609_, v_f_1610_, v_x_1611_, v_x_1612_);
lean_dec_ref(v_x_1611_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b1_1614_, lean_object* v_00_u03b2_1615_, lean_object* v_00_u03c3_1616_, lean_object* v_f_1617_, lean_object* v_as_1618_, size_t v_i_1619_, size_t v_stop_1620_, lean_object* v_b_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_f_1617_, v_as_1618_, v_i_1619_, v_stop_1620_, v_b_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1623_, lean_object* v_00_u03b2_1624_, lean_object* v_00_u03c3_1625_, lean_object* v_f_1626_, lean_object* v_as_1627_, lean_object* v_i_1628_, lean_object* v_stop_1629_, lean_object* v_b_1630_){
_start:
{
size_t v_i_boxed_1631_; size_t v_stop_boxed_1632_; lean_object* v_res_1633_; 
v_i_boxed_1631_ = lean_unbox_usize(v_i_1628_);
lean_dec(v_i_1628_);
v_stop_boxed_1632_ = lean_unbox_usize(v_stop_1629_);
lean_dec(v_stop_1629_);
v_res_1633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4(v_00_u03b1_1623_, v_00_u03b2_1624_, v_00_u03c3_1625_, v_f_1626_, v_as_1627_, v_i_boxed_1631_, v_stop_boxed_1632_, v_b_1630_);
lean_dec_ref(v_as_1627_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03c3_1634_, lean_object* v_00_u03b1_1635_, lean_object* v_00_u03b2_1636_, lean_object* v_f_1637_, lean_object* v_keys_1638_, lean_object* v_vals_1639_, lean_object* v_heq_1640_, lean_object* v_i_1641_, lean_object* v_acc_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_1637_, v_keys_1638_, v_vals_1639_, v_i_1641_, v_acc_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03c3_1644_, lean_object* v_00_u03b1_1645_, lean_object* v_00_u03b2_1646_, lean_object* v_f_1647_, lean_object* v_keys_1648_, lean_object* v_vals_1649_, lean_object* v_heq_1650_, lean_object* v_i_1651_, lean_object* v_acc_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03c3_1644_, v_00_u03b1_1645_, v_00_u03b2_1646_, v_f_1647_, v_keys_1648_, v_vals_1649_, v_heq_1650_, v_i_1651_, v_acc_1652_);
lean_dec_ref(v_vals_1649_);
lean_dec_ref(v_keys_1648_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object* v_x_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = ((lean_object*)(l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_));
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object* v_x_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(v_x_1658_);
lean_dec_ref(v_x_1658_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object* v_x_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = ((lean_object*)(l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_));
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object* v_x_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(v_x_1665_);
lean_dec_ref(v_x_1665_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object* v_env_1667_, lean_object* v_x_1668_, uint8_t v_x_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3(v_env_1667_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object* v_env_1671_, lean_object* v_x_1672_, lean_object* v_x_1673_){
_start:
{
uint8_t v_x_107__boxed_1674_; lean_object* v_res_1675_; 
v_x_107__boxed_1674_ = lean_unbox(v_x_1673_);
v_res_1675_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(v_env_1671_, v_x_1672_, v_x_107__boxed_1674_);
lean_dec_ref(v_x_1672_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object* v_a_1676_, uint8_t v_a_1677_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
uint8_t v_a_115__boxed_1680_; lean_object* v_res_1681_; 
v_a_115__boxed_1680_ = lean_unbox(v_a_1679_);
v_res_1681_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(v_a_1678_, v_a_115__boxed_1680_);
lean_dec_ref(v_a_1678_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object* v_mapss_1682_, lean_object* v_x_1683_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1685_, 0, v_mapss_1682_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object* v_mapss_1686_, lean_object* v_x_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(v_mapss_1686_, v_x_1687_);
lean_dec_ref(v_x_1687_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(lean_object* v___x_1690_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object* v___x_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(v___x_1693_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = ((lean_object*)(l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_));
v___x_1722_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2____boxed(lean_object* v_a_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_1146880649____hygCtx___hyg_2_();
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_228879371____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = lean_box(0);
v___x_1727_ = lean_st_mk_ref(v___x_1726_);
v___x_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_228879371____hygCtx___hyg_2____boxed(lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_228879371____hygCtx___hyg_2_();
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__0(lean_object* v_as_1731_, size_t v_i_1732_, size_t v_stop_1733_, lean_object* v_b_1734_){
_start:
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_usize_dec_eq(v_i_1732_, v_stop_1733_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; size_t v___x_1738_; size_t v___x_1739_; 
v___x_1736_ = lean_array_uget_borrowed(v_as_1731_, v_i_1732_);
lean_inc(v___x_1736_);
v___x_1737_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers(v_b_1734_, v___x_1736_);
v___x_1738_ = ((size_t)1ULL);
v___x_1739_ = lean_usize_add(v_i_1732_, v___x_1738_);
v_i_1732_ = v___x_1739_;
v_b_1734_ = v___x_1737_;
goto _start;
}
else
{
return v_b_1734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__0___boxed(lean_object* v_as_1741_, lean_object* v_i_1742_, lean_object* v_stop_1743_, lean_object* v_b_1744_){
_start:
{
size_t v_i_boxed_1745_; size_t v_stop_boxed_1746_; lean_object* v_res_1747_; 
v_i_boxed_1745_ = lean_unbox_usize(v_i_1742_);
lean_dec(v_i_1742_);
v_stop_boxed_1746_ = lean_unbox_usize(v_stop_1743_);
lean_dec(v_stop_1743_);
v_res_1747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__0(v_as_1741_, v_i_boxed_1745_, v_stop_boxed_1746_, v_b_1744_);
lean_dec_ref(v_as_1741_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__1(lean_object* v_as_1748_, size_t v_i_1749_, size_t v_stop_1750_, lean_object* v_b_1751_){
_start:
{
lean_object* v___y_1753_; uint8_t v___x_1757_; 
v___x_1757_ = lean_usize_dec_eq(v_i_1749_, v_stop_1750_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1758_ = lean_array_uget_borrowed(v_as_1748_, v_i_1749_);
v___x_1759_ = lean_unsigned_to_nat(0u);
v___x_1760_ = lean_array_get_size(v___x_1758_);
v___x_1761_ = lean_nat_dec_lt(v___x_1759_, v___x_1760_);
if (v___x_1761_ == 0)
{
v___y_1753_ = v_b_1751_;
goto v___jp_1752_;
}
else
{
uint8_t v___x_1762_; 
v___x_1762_ = lean_nat_dec_le(v___x_1760_, v___x_1760_);
if (v___x_1762_ == 0)
{
if (v___x_1761_ == 0)
{
v___y_1753_ = v_b_1751_;
goto v___jp_1752_;
}
else
{
size_t v___x_1763_; size_t v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = ((size_t)0ULL);
v___x_1764_ = lean_usize_of_nat(v___x_1760_);
v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__0(v___x_1758_, v___x_1763_, v___x_1764_, v_b_1751_);
v___y_1753_ = v___x_1765_;
goto v___jp_1752_;
}
}
else
{
size_t v___x_1766_; size_t v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = ((size_t)0ULL);
v___x_1767_ = lean_usize_of_nat(v___x_1760_);
v___x_1768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__0(v___x_1758_, v___x_1766_, v___x_1767_, v_b_1751_);
v___y_1753_ = v___x_1768_;
goto v___jp_1752_;
}
}
}
else
{
return v_b_1751_;
}
v___jp_1752_:
{
size_t v___x_1754_; size_t v___x_1755_; 
v___x_1754_ = ((size_t)1ULL);
v___x_1755_ = lean_usize_add(v_i_1749_, v___x_1754_);
v_i_1749_ = v___x_1755_;
v_b_1751_ = v___y_1753_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__1___boxed(lean_object* v_as_1769_, lean_object* v_i_1770_, lean_object* v_stop_1771_, lean_object* v_b_1772_){
_start:
{
size_t v_i_boxed_1773_; size_t v_stop_boxed_1774_; lean_object* v_res_1775_; 
v_i_boxed_1773_ = lean_unbox_usize(v_i_1770_);
lean_dec(v_i_1770_);
v_stop_boxed_1774_ = lean_unbox_usize(v_stop_1771_);
lean_dec(v_stop_1771_);
v_res_1775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__1(v_as_1769_, v_i_boxed_1773_, v_stop_boxed_1774_, v_b_1772_);
lean_dec_ref(v_as_1769_);
return v_res_1775_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___closed__0(void){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Array_instInhabited(lean_box(0));
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg(lean_object* v_a_1777_){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersRef;
v___x_1780_ = lean_st_ref_get(v___x_1779_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v___x_1781_; lean_object* v___y_1783_; lean_object* v_env_1787_; lean_object* v___x_1788_; lean_object* v_toEnvExtension_1789_; lean_object* v_asyncMode_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1781_ = lean_st_ref_get(v_a_1777_);
v_env_1787_ = lean_ctor_get(v___x_1781_, 0);
lean_inc_ref(v_env_1787_);
lean_dec(v___x_1781_);
v___x_1788_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt;
v_toEnvExtension_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc_ref(v_toEnvExtension_1789_);
v_asyncMode_1790_ = lean_ctor_get(v_toEnvExtension_1789_, 2);
lean_inc(v_asyncMode_1790_);
lean_dec_ref(v_toEnvExtension_1789_);
v___x_1791_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___closed__0, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___closed__0_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___closed__0);
v___x_1792_ = lean_box(0);
v___x_1793_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1791_, v___x_1788_, v_env_1787_, v_asyncMode_1790_, v___x_1792_);
lean_dec(v_asyncMode_1790_);
v___x_1794_ = lean_box(1);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = lean_array_get_size(v___x_1793_);
v___x_1797_ = lean_nat_dec_lt(v___x_1795_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_dec(v___x_1793_);
v___y_1783_ = v___x_1794_;
goto v___jp_1782_;
}
else
{
uint8_t v___x_1798_; 
v___x_1798_ = lean_nat_dec_le(v___x_1796_, v___x_1796_);
if (v___x_1798_ == 0)
{
if (v___x_1797_ == 0)
{
lean_dec(v___x_1793_);
v___y_1783_ = v___x_1794_;
goto v___jp_1782_;
}
else
{
size_t v___x_1799_; size_t v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = ((size_t)0ULL);
v___x_1800_ = lean_usize_of_nat(v___x_1796_);
v___x_1801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__1(v___x_1793_, v___x_1799_, v___x_1800_, v___x_1794_);
lean_dec(v___x_1793_);
v___y_1783_ = v___x_1801_;
goto v___jp_1782_;
}
}
else
{
size_t v___x_1802_; size_t v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = ((size_t)0ULL);
v___x_1803_ = lean_usize_of_nat(v___x_1796_);
v___x_1804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__1(v___x_1793_, v___x_1802_, v___x_1803_, v___x_1794_);
lean_dec(v___x_1793_);
v___y_1783_ = v___x_1804_;
goto v___jp_1782_;
}
}
v___jp_1782_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
lean_inc(v___y_1783_);
v___x_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___y_1783_);
v___x_1785_ = lean_st_ref_set(v___x_1779_, v___x_1784_);
v___x_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1786_, 0, v___y_1783_);
return v___x_1786_;
}
}
else
{
lean_object* v_val_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
v_val_1805_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1780_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_val_1805_);
lean_dec(v___x_1780_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set_tag(v___x_1807_, 0);
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_val_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___boxed(lean_object* v_a_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg(v_a_1813_);
lean_dec(v_a_1813_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap(lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg(v_a_1817_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___boxed(lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap(v_a_1820_, v_a_1821_);
lean_dec(v_a_1821_);
lean_dec_ref(v_a_1820_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___redArg(lean_object* v_trigger_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v___x_1827_; lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1837_; 
v___x_1827_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg(v_a_1825_);
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1837_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1837_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1832_ = lean_box(0);
v___x_1833_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_a_1828_, v_trigger_1824_, v___x_1832_);
lean_dec(v_a_1828_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1833_);
v___x_1835_ = v___x_1830_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___redArg___boxed(lean_object* v_trigger_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___redArg(v_trigger_1838_, v_a_1839_);
lean_dec(v_a_1839_);
lean_dec(v_trigger_1838_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems(lean_object* v_trigger_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___redArg(v_trigger_1842_, v_a_1844_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___boxed(lean_object* v_trigger_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems(v_trigger_1847_, v_a_1848_, v_a_1849_);
lean_dec(v_a_1849_);
lean_dec_ref(v_a_1848_);
lean_dec(v_trigger_1847_);
return v_res_1851_;
}
}
LEAN_EXPORT uint8_t l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1___lam__0(lean_object* v_decl_1852_, lean_object* v_x_1853_){
_start:
{
lean_object* v_fst_1854_; uint8_t v___x_1855_; 
v_fst_1854_ = lean_ctor_get(v_x_1853_, 0);
v___x_1855_ = lean_name_eq(v_fst_1854_, v_decl_1852_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1___lam__0___boxed(lean_object* v_decl_1856_, lean_object* v_x_1857_){
_start:
{
uint8_t v_res_1858_; lean_object* v_r_1859_; 
v_res_1858_ = l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1___lam__0(v_decl_1856_, v_x_1857_);
lean_dec_ref(v_x_1857_);
lean_dec(v_decl_1856_);
v_r_1859_ = lean_box(v_res_1858_);
return v_r_1859_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1(lean_object* v_decl_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
if (lean_obj_tag(v_a_1861_) == 0)
{
lean_object* v___x_1863_; 
lean_dec(v_decl_1860_);
v___x_1863_ = lean_array_to_list(v_a_1862_);
return v___x_1863_;
}
else
{
lean_object* v_head_1864_; lean_object* v_tail_1865_; lean_object* v_val_1867_; lean_object* v_fst_1870_; lean_object* v_snd_1871_; lean_object* v___f_1872_; lean_object* v___x_1873_; 
v_head_1864_ = lean_ctor_get(v_a_1861_, 0);
lean_inc(v_head_1864_);
v_tail_1865_ = lean_ctor_get(v_a_1861_, 1);
lean_inc(v_tail_1865_);
lean_dec_ref(v_a_1861_);
v_fst_1870_ = lean_ctor_get(v_head_1864_, 0);
lean_inc(v_fst_1870_);
v_snd_1871_ = lean_ctor_get(v_head_1864_, 1);
lean_inc(v_snd_1871_);
lean_dec(v_head_1864_);
lean_inc(v_decl_1860_);
v___f_1872_ = lean_alloc_closure((void*)(l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1872_, 0, v_decl_1860_);
v___x_1873_ = l_List_find_x3f___redArg(v___f_1872_, v_snd_1871_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_dec(v_fst_1870_);
if (lean_obj_tag(v___x_1873_) == 0)
{
v_a_1861_ = v_tail_1865_;
goto _start;
}
else
{
lean_object* v_val_1875_; 
v_val_1875_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_val_1875_);
lean_dec_ref(v___x_1873_);
v_val_1867_ = v_val_1875_;
goto v___jp_1866_;
}
}
else
{
lean_object* v_val_1876_; lean_object* v_snd_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
v_val_1876_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_val_1876_);
lean_dec_ref(v___x_1873_);
v_snd_1877_ = lean_ctor_get(v_val_1876_, 1);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_val_1876_);
if (v_isSharedCheck_1884_ == 0)
{
lean_object* v_unused_1885_; 
v_unused_1885_ = lean_ctor_get(v_val_1876_, 0);
lean_dec(v_unused_1885_);
v___x_1879_ = v_val_1876_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_snd_1877_);
lean_dec(v_val_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v_fst_1870_);
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_fst_1870_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_snd_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
v_val_1867_ = v___x_1882_;
goto v___jp_1866_;
}
}
}
v___jp_1866_:
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_array_push(v_a_1862_, v_val_1867_);
v_a_1861_ = v_tail_1865_;
v_a_1862_ = v___x_1868_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__0(lean_object* v_init_1886_, lean_object* v_x_1887_){
_start:
{
if (lean_obj_tag(v_x_1887_) == 0)
{
lean_object* v_k_1888_; lean_object* v_v_1889_; lean_object* v_l_1890_; lean_object* v_r_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v_k_1888_ = lean_ctor_get(v_x_1887_, 1);
v_v_1889_ = lean_ctor_get(v_x_1887_, 2);
v_l_1890_ = lean_ctor_get(v_x_1887_, 3);
v_r_1891_ = lean_ctor_get(v_x_1887_, 4);
v___x_1892_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__0(v_init_1886_, v_r_1891_);
lean_inc(v_v_1889_);
lean_inc(v_k_1888_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v_k_1888_);
lean_ctor_set(v___x_1893_, 1, v_v_1889_);
v___x_1894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
lean_ctor_set(v___x_1894_, 1, v___x_1892_);
v_init_1886_ = v___x_1894_;
v_x_1887_ = v_l_1890_;
goto _start;
}
else
{
return v_init_1886_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__0___boxed(lean_object* v_init_1896_, lean_object* v_x_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__0(v_init_1896_, v_x_1897_);
lean_dec(v_x_1897_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___redArg(lean_object* v_decl_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v___x_1902_; lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1914_; 
v___x_1902_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg(v_a_1900_);
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1905_ = v___x_1902_;
v_isShared_1906_ = v_isSharedCheck_1914_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1902_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1914_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1907_ = lean_box(0);
v___x_1908_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__0(v___x_1907_, v_a_1903_);
lean_dec(v_a_1903_);
v___x_1909_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1___closed__0));
v___x_1910_ = l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1(v_decl_1899_, v___x_1908_, v___x_1909_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v___x_1910_);
v___x_1912_ = v___x_1905_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___redArg___boxed(lean_object* v_decl_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___redArg(v_decl_1915_, v_a_1916_);
lean_dec(v_a_1916_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor(lean_object* v_decl_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___redArg(v_decl_1919_, v_a_1921_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___boxed(lean_object* v_decl_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor(v_decl_1924_, v_a_1925_, v_a_1926_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
return v_res_1928_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___lam__0(lean_object* v_x_1929_, lean_object* v_y_1930_){
_start:
{
lean_object* v_fst_1931_; lean_object* v_snd_1932_; lean_object* v_fst_1933_; lean_object* v_snd_1934_; double v___x_1935_; double v___x_1936_; uint8_t v___x_1937_; 
v_fst_1931_ = lean_ctor_get(v_x_1929_, 0);
v_snd_1932_ = lean_ctor_get(v_x_1929_, 1);
v_fst_1933_ = lean_ctor_get(v_y_1930_, 0);
v_snd_1934_ = lean_ctor_get(v_y_1930_, 1);
v___x_1935_ = lean_unbox_float(v_fst_1931_);
v___x_1936_ = lean_unbox_float(v_fst_1933_);
v___x_1937_ = lean_float_decLt(v___x_1935_, v___x_1936_);
if (v___x_1937_ == 0)
{
double v___x_1938_; double v___x_1939_; uint8_t v___x_1940_; 
v___x_1938_ = lean_unbox_float(v_fst_1933_);
v___x_1939_ = lean_unbox_float(v_fst_1931_);
v___x_1940_ = lean_float_decLt(v___x_1938_, v___x_1939_);
if (v___x_1940_ == 0)
{
uint8_t v___x_1941_; 
v___x_1941_ = l_Lean_Name_cmp(v_snd_1932_, v_snd_1934_);
return v___x_1941_;
}
else
{
uint8_t v___x_1942_; 
v___x_1942_ = 2;
return v___x_1942_;
}
}
else
{
uint8_t v___x_1943_; 
v___x_1943_ = 0;
return v___x_1943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___lam__0___boxed(lean_object* v_x_1944_, lean_object* v_y_1945_){
_start:
{
uint8_t v_res_1946_; lean_object* v_r_1947_; 
v_res_1946_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___lam__0(v_x_1944_, v_y_1945_);
lean_dec_ref(v_y_1945_);
lean_dec_ref(v_x_1944_);
v_r_1947_ = lean_box(v_res_1946_);
return v_r_1947_;
}
}
static double _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___closed__0(void){
_start:
{
lean_object* v___x_1950_; uint8_t v___x_1951_; lean_object* v___x_1952_; double v___x_1953_; 
v___x_1950_ = lean_unsigned_to_nat(1u);
v___x_1951_ = 1;
v___x_1952_ = lean_unsigned_to_nat(10u);
v___x_1953_ = l_Float_ofScientific(v___x_1952_, v___x_1951_, v___x_1950_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg(lean_object* v_n_1954_, double v_frequencyWeight_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_LibrarySuggestions_symbolFrequency___redArg(v_n_1954_, v_a_1956_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1974_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1974_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1974_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; double v___x_1964_; lean_object* v___x_1965_; double v___x_1966_; double v___x_1967_; double v___x_1968_; double v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1963_ = lean_unsigned_to_nat(1u);
v___x_1964_ = lean_float_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___closed__0, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___closed__0_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___closed__0);
v___x_1965_ = lean_nat_add(v_a_1959_, v___x_1963_);
lean_dec(v_a_1959_);
v___x_1966_ = lean_float_of_nat(v___x_1965_);
v___x_1967_ = log2(v___x_1966_);
v___x_1968_ = lean_float_mul(v_frequencyWeight_1955_, v___x_1967_);
v___x_1969_ = lean_float_add(v___x_1964_, v___x_1968_);
v___x_1970_ = lean_box_float(v___x_1969_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1970_);
v___x_1972_ = v___x_1961_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
v_a_1975_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1958_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1958_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___boxed(lean_object* v_n_1983_, lean_object* v_frequencyWeight_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
double v_frequencyWeight_boxed_1987_; lean_object* v_res_1988_; 
v_frequencyWeight_boxed_1987_ = lean_unbox_float(v_frequencyWeight_1984_);
lean_dec_ref(v_frequencyWeight_1984_);
v_res_1988_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg(v_n_1983_, v_frequencyWeight_boxed_1987_, v_a_1985_);
lean_dec(v_a_1985_);
lean_dec(v_n_1983_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore(lean_object* v_n_1989_, double v_frequencyWeight_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg(v_n_1989_, v_frequencyWeight_1990_, v_a_1994_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___boxed(lean_object* v_n_1997_, lean_object* v_frequencyWeight_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
double v_frequencyWeight_boxed_2004_; lean_object* v_res_2005_; 
v_frequencyWeight_boxed_2004_ = lean_unbox_float(v_frequencyWeight_1998_);
lean_dec_ref(v_frequencyWeight_1998_);
v_res_2005_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore(v_n_1997_, v_frequencyWeight_boxed_2004_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_n_1997_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg(lean_object* v_cls_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_options_2012_; uint8_t v_hasTrace_2013_; 
v_options_2012_ = lean_ctor_get(v___y_2010_, 2);
v_hasTrace_2013_ = lean_ctor_get_uint8(v_options_2012_, sizeof(void*)*1);
if (v_hasTrace_2013_ == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_dec(v_cls_2009_);
v___x_2014_ = lean_box(v_hasTrace_2013_);
v___x_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
return v___x_2015_;
}
else
{
lean_object* v_inheritedTraceOptions_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v_inheritedTraceOptions_2016_ = lean_ctor_get(v___y_2010_, 13);
v___x_2017_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg___closed__1));
v___x_2018_ = l_Lean_Name_append(v___x_2017_, v_cls_2009_);
v___x_2019_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2016_, v_options_2012_, v___x_2018_);
lean_dec(v___x_2018_);
v___x_2020_ = lean_box(v___x_2019_);
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
return v___x_2021_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg___boxed(lean_object* v_cls_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg(v_cls_2022_, v___y_2023_);
lean_dec_ref(v___y_2023_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5(lean_object* v_cls_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v___x_2032_; 
v___x_2032_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg(v_cls_2026_, v___y_2029_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___boxed(lean_object* v_cls_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5(v_cls_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(lean_object* v_k_2040_, lean_object* v_t_2041_){
_start:
{
lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; 
if (lean_obj_tag(v_t_2041_) == 0)
{
lean_object* v_k_2056_; lean_object* v_v_2057_; lean_object* v_l_2058_; lean_object* v_r_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2702_; 
v_k_2056_ = lean_ctor_get(v_t_2041_, 1);
v_v_2057_ = lean_ctor_get(v_t_2041_, 2);
v_l_2058_ = lean_ctor_get(v_t_2041_, 3);
v_r_2059_ = lean_ctor_get(v_t_2041_, 4);
v_isSharedCheck_2702_ = !lean_is_exclusive(v_t_2041_);
if (v_isSharedCheck_2702_ == 0)
{
lean_object* v_unused_2703_; 
v_unused_2703_ = lean_ctor_get(v_t_2041_, 0);
lean_dec(v_unused_2703_);
v___x_2061_ = v_t_2041_;
v_isShared_2062_ = v_isSharedCheck_2702_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_r_2059_);
lean_inc(v_l_2058_);
lean_inc(v_v_2057_);
lean_inc(v_k_2056_);
lean_dec(v_t_2041_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2702_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v_fst_2380_; lean_object* v_snd_2381_; lean_object* v_fst_2382_; lean_object* v_snd_2383_; double v___x_2384_; double v___x_2385_; uint8_t v___x_2386_; 
v_fst_2380_ = lean_ctor_get(v_k_2040_, 0);
v_snd_2381_ = lean_ctor_get(v_k_2040_, 1);
v_fst_2382_ = lean_ctor_get(v_k_2056_, 0);
v_snd_2383_ = lean_ctor_get(v_k_2056_, 1);
v___x_2384_ = lean_unbox_float(v_fst_2380_);
v___x_2385_ = lean_unbox_float(v_fst_2382_);
v___x_2386_ = lean_float_decLt(v___x_2384_, v___x_2385_);
if (v___x_2386_ == 0)
{
double v___x_2387_; double v___x_2388_; uint8_t v___x_2389_; 
v___x_2387_ = lean_unbox_float(v_fst_2382_);
v___x_2388_ = lean_unbox_float(v_fst_2380_);
v___x_2389_ = lean_float_decLt(v___x_2387_, v___x_2388_);
if (v___x_2389_ == 0)
{
uint8_t v___x_2390_; 
v___x_2390_ = l_Lean_Name_cmp(v_snd_2381_, v_snd_2383_);
switch(v___x_2390_)
{
case 0:
{
lean_del_object(v___x_2061_);
goto v___jp_2248_;
}
case 1:
{
lean_del_object(v___x_2061_);
lean_dec(v_v_2057_);
lean_dec(v_k_2056_);
if (lean_obj_tag(v_l_2058_) == 0)
{
if (lean_obj_tag(v_r_2059_) == 0)
{
lean_object* v_size_2391_; lean_object* v_k_2392_; lean_object* v_v_2393_; lean_object* v_l_2394_; lean_object* v_r_2395_; lean_object* v_size_2396_; lean_object* v_k_2397_; lean_object* v_v_2398_; lean_object* v_l_2399_; lean_object* v_r_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; 
v_size_2391_ = lean_ctor_get(v_l_2058_, 0);
v_k_2392_ = lean_ctor_get(v_l_2058_, 1);
v_v_2393_ = lean_ctor_get(v_l_2058_, 2);
v_l_2394_ = lean_ctor_get(v_l_2058_, 3);
v_r_2395_ = lean_ctor_get(v_l_2058_, 4);
lean_inc(v_r_2395_);
v_size_2396_ = lean_ctor_get(v_r_2059_, 0);
v_k_2397_ = lean_ctor_get(v_r_2059_, 1);
v_v_2398_ = lean_ctor_get(v_r_2059_, 2);
v_l_2399_ = lean_ctor_get(v_r_2059_, 3);
lean_inc(v_l_2399_);
v_r_2400_ = lean_ctor_get(v_r_2059_, 4);
v___x_2401_ = lean_unsigned_to_nat(1u);
v___x_2402_ = lean_nat_dec_lt(v_size_2391_, v_size_2396_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2538_; 
lean_inc(v_l_2394_);
lean_inc(v_v_2393_);
lean_inc(v_k_2392_);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_l_2058_);
if (v_isSharedCheck_2538_ == 0)
{
lean_object* v_unused_2539_; lean_object* v_unused_2540_; lean_object* v_unused_2541_; lean_object* v_unused_2542_; lean_object* v_unused_2543_; 
v_unused_2539_ = lean_ctor_get(v_l_2058_, 4);
lean_dec(v_unused_2539_);
v_unused_2540_ = lean_ctor_get(v_l_2058_, 3);
lean_dec(v_unused_2540_);
v_unused_2541_ = lean_ctor_get(v_l_2058_, 2);
lean_dec(v_unused_2541_);
v_unused_2542_ = lean_ctor_get(v_l_2058_, 1);
lean_dec(v_unused_2542_);
v_unused_2543_ = lean_ctor_get(v_l_2058_, 0);
lean_dec(v_unused_2543_);
v___x_2404_ = v_l_2058_;
v_isShared_2405_ = v_isSharedCheck_2538_;
goto v_resetjp_2403_;
}
else
{
lean_dec(v_l_2058_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2538_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2406_; lean_object* v_tree_2407_; 
v___x_2406_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2392_, v_v_2393_, v_l_2394_, v_r_2395_);
v_tree_2407_ = lean_ctor_get(v___x_2406_, 2);
lean_inc(v_tree_2407_);
if (lean_obj_tag(v_tree_2407_) == 0)
{
lean_object* v_k_2408_; lean_object* v_v_2409_; lean_object* v_size_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; 
v_k_2408_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_k_2408_);
v_v_2409_ = lean_ctor_get(v___x_2406_, 1);
lean_inc(v_v_2409_);
lean_dec_ref(v___x_2406_);
v_size_2410_ = lean_ctor_get(v_tree_2407_, 0);
v___x_2411_ = lean_unsigned_to_nat(3u);
v___x_2412_ = lean_nat_mul(v___x_2411_, v_size_2410_);
v___x_2413_ = lean_nat_dec_lt(v___x_2412_, v_size_2396_);
lean_dec(v___x_2412_);
if (v___x_2413_ == 0)
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2417_; 
lean_dec(v_l_2399_);
v___x_2414_ = lean_nat_add(v___x_2401_, v_size_2410_);
v___x_2415_ = lean_nat_add(v___x_2414_, v_size_2396_);
lean_dec(v___x_2414_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 4, v_r_2059_);
lean_ctor_set(v___x_2404_, 3, v_tree_2407_);
lean_ctor_set(v___x_2404_, 2, v_v_2409_);
lean_ctor_set(v___x_2404_, 1, v_k_2408_);
lean_ctor_set(v___x_2404_, 0, v___x_2415_);
v___x_2417_ = v___x_2404_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_k_2408_);
lean_ctor_set(v_reuseFailAlloc_2418_, 2, v_v_2409_);
lean_ctor_set(v_reuseFailAlloc_2418_, 3, v_tree_2407_);
lean_ctor_set(v_reuseFailAlloc_2418_, 4, v_r_2059_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
else
{
lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2473_; 
lean_inc(v_r_2400_);
lean_inc(v_v_2398_);
lean_inc(v_k_2397_);
lean_inc(v_size_2396_);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_r_2059_);
if (v_isSharedCheck_2473_ == 0)
{
lean_object* v_unused_2474_; lean_object* v_unused_2475_; lean_object* v_unused_2476_; lean_object* v_unused_2477_; lean_object* v_unused_2478_; 
v_unused_2474_ = lean_ctor_get(v_r_2059_, 4);
lean_dec(v_unused_2474_);
v_unused_2475_ = lean_ctor_get(v_r_2059_, 3);
lean_dec(v_unused_2475_);
v_unused_2476_ = lean_ctor_get(v_r_2059_, 2);
lean_dec(v_unused_2476_);
v_unused_2477_ = lean_ctor_get(v_r_2059_, 1);
lean_dec(v_unused_2477_);
v_unused_2478_ = lean_ctor_get(v_r_2059_, 0);
lean_dec(v_unused_2478_);
v___x_2420_ = v_r_2059_;
v_isShared_2421_ = v_isSharedCheck_2473_;
goto v_resetjp_2419_;
}
else
{
lean_dec(v_r_2059_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2473_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v_size_2422_; lean_object* v_k_2423_; lean_object* v_v_2424_; lean_object* v_l_2425_; lean_object* v_r_2426_; lean_object* v_size_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; uint8_t v___x_2430_; 
v_size_2422_ = lean_ctor_get(v_l_2399_, 0);
v_k_2423_ = lean_ctor_get(v_l_2399_, 1);
v_v_2424_ = lean_ctor_get(v_l_2399_, 2);
v_l_2425_ = lean_ctor_get(v_l_2399_, 3);
v_r_2426_ = lean_ctor_get(v_l_2399_, 4);
v_size_2427_ = lean_ctor_get(v_r_2400_, 0);
v___x_2428_ = lean_unsigned_to_nat(2u);
v___x_2429_ = lean_nat_mul(v___x_2428_, v_size_2427_);
v___x_2430_ = lean_nat_dec_lt(v_size_2422_, v___x_2429_);
lean_dec(v___x_2429_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2458_; 
lean_inc(v_r_2426_);
lean_inc(v_l_2425_);
lean_inc(v_v_2424_);
lean_inc(v_k_2423_);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_l_2399_);
if (v_isSharedCheck_2458_ == 0)
{
lean_object* v_unused_2459_; lean_object* v_unused_2460_; lean_object* v_unused_2461_; lean_object* v_unused_2462_; lean_object* v_unused_2463_; 
v_unused_2459_ = lean_ctor_get(v_l_2399_, 4);
lean_dec(v_unused_2459_);
v_unused_2460_ = lean_ctor_get(v_l_2399_, 3);
lean_dec(v_unused_2460_);
v_unused_2461_ = lean_ctor_get(v_l_2399_, 2);
lean_dec(v_unused_2461_);
v_unused_2462_ = lean_ctor_get(v_l_2399_, 1);
lean_dec(v_unused_2462_);
v_unused_2463_ = lean_ctor_get(v_l_2399_, 0);
lean_dec(v_unused_2463_);
v___x_2432_ = v_l_2399_;
v_isShared_2433_ = v_isSharedCheck_2458_;
goto v_resetjp_2431_;
}
else
{
lean_dec(v_l_2399_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2458_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2448_; 
v___x_2434_ = lean_nat_add(v___x_2401_, v_size_2410_);
v___x_2435_ = lean_nat_add(v___x_2434_, v_size_2396_);
lean_dec(v_size_2396_);
if (lean_obj_tag(v_l_2425_) == 0)
{
lean_object* v_size_2456_; 
v_size_2456_ = lean_ctor_get(v_l_2425_, 0);
lean_inc(v_size_2456_);
v___y_2448_ = v_size_2456_;
goto v___jp_2447_;
}
else
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_unsigned_to_nat(0u);
v___y_2448_ = v___x_2457_;
goto v___jp_2447_;
}
v___jp_2436_:
{
lean_object* v___x_2440_; lean_object* v___x_2442_; 
v___x_2440_ = lean_nat_add(v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec(v___y_2438_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 4, v_r_2400_);
lean_ctor_set(v___x_2432_, 3, v_r_2426_);
lean_ctor_set(v___x_2432_, 2, v_v_2398_);
lean_ctor_set(v___x_2432_, 1, v_k_2397_);
lean_ctor_set(v___x_2432_, 0, v___x_2440_);
v___x_2442_ = v___x_2432_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2440_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_k_2397_);
lean_ctor_set(v_reuseFailAlloc_2446_, 2, v_v_2398_);
lean_ctor_set(v_reuseFailAlloc_2446_, 3, v_r_2426_);
lean_ctor_set(v_reuseFailAlloc_2446_, 4, v_r_2400_);
v___x_2442_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2444_; 
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 4, v___x_2442_);
lean_ctor_set(v___x_2420_, 3, v___y_2437_);
lean_ctor_set(v___x_2420_, 2, v_v_2424_);
lean_ctor_set(v___x_2420_, 1, v_k_2423_);
lean_ctor_set(v___x_2420_, 0, v___x_2435_);
v___x_2444_ = v___x_2420_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v_k_2423_);
lean_ctor_set(v_reuseFailAlloc_2445_, 2, v_v_2424_);
lean_ctor_set(v_reuseFailAlloc_2445_, 3, v___y_2437_);
lean_ctor_set(v_reuseFailAlloc_2445_, 4, v___x_2442_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
v___jp_2447_:
{
lean_object* v___x_2449_; lean_object* v___x_2451_; 
v___x_2449_ = lean_nat_add(v___x_2434_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec(v___x_2434_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 4, v_l_2425_);
lean_ctor_set(v___x_2404_, 3, v_tree_2407_);
lean_ctor_set(v___x_2404_, 2, v_v_2409_);
lean_ctor_set(v___x_2404_, 1, v_k_2408_);
lean_ctor_set(v___x_2404_, 0, v___x_2449_);
v___x_2451_ = v___x_2404_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_k_2408_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v_v_2409_);
lean_ctor_set(v_reuseFailAlloc_2455_, 3, v_tree_2407_);
lean_ctor_set(v_reuseFailAlloc_2455_, 4, v_l_2425_);
v___x_2451_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
lean_object* v___x_2452_; 
v___x_2452_ = lean_nat_add(v___x_2401_, v_size_2427_);
if (lean_obj_tag(v_r_2426_) == 0)
{
lean_object* v_size_2453_; 
v_size_2453_ = lean_ctor_get(v_r_2426_, 0);
lean_inc(v_size_2453_);
v___y_2437_ = v___x_2451_;
v___y_2438_ = v___x_2452_;
v___y_2439_ = v_size_2453_;
goto v___jp_2436_;
}
else
{
lean_object* v___x_2454_; 
v___x_2454_ = lean_unsigned_to_nat(0u);
v___y_2437_ = v___x_2451_;
v___y_2438_ = v___x_2452_;
v___y_2439_ = v___x_2454_;
goto v___jp_2436_;
}
}
}
}
}
else
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2468_; 
v___x_2464_ = lean_nat_add(v___x_2401_, v_size_2410_);
v___x_2465_ = lean_nat_add(v___x_2464_, v_size_2396_);
lean_dec(v_size_2396_);
v___x_2466_ = lean_nat_add(v___x_2464_, v_size_2422_);
lean_dec(v___x_2464_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 4, v_l_2399_);
lean_ctor_set(v___x_2420_, 3, v_tree_2407_);
lean_ctor_set(v___x_2420_, 2, v_v_2409_);
lean_ctor_set(v___x_2420_, 1, v_k_2408_);
lean_ctor_set(v___x_2420_, 0, v___x_2466_);
v___x_2468_ = v___x_2420_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_k_2408_);
lean_ctor_set(v_reuseFailAlloc_2472_, 2, v_v_2409_);
lean_ctor_set(v_reuseFailAlloc_2472_, 3, v_tree_2407_);
lean_ctor_set(v_reuseFailAlloc_2472_, 4, v_l_2399_);
v___x_2468_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
lean_object* v___x_2470_; 
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 4, v_r_2400_);
lean_ctor_set(v___x_2404_, 3, v___x_2468_);
lean_ctor_set(v___x_2404_, 2, v_v_2398_);
lean_ctor_set(v___x_2404_, 1, v_k_2397_);
lean_ctor_set(v___x_2404_, 0, v___x_2465_);
v___x_2470_ = v___x_2404_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2465_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v_k_2397_);
lean_ctor_set(v_reuseFailAlloc_2471_, 2, v_v_2398_);
lean_ctor_set(v_reuseFailAlloc_2471_, 3, v___x_2468_);
lean_ctor_set(v_reuseFailAlloc_2471_, 4, v_r_2400_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
}
else
{
lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2532_; 
lean_inc(v_r_2400_);
lean_inc(v_v_2398_);
lean_inc(v_k_2397_);
lean_inc(v_size_2396_);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_r_2059_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; lean_object* v_unused_2534_; lean_object* v_unused_2535_; lean_object* v_unused_2536_; lean_object* v_unused_2537_; 
v_unused_2533_ = lean_ctor_get(v_r_2059_, 4);
lean_dec(v_unused_2533_);
v_unused_2534_ = lean_ctor_get(v_r_2059_, 3);
lean_dec(v_unused_2534_);
v_unused_2535_ = lean_ctor_get(v_r_2059_, 2);
lean_dec(v_unused_2535_);
v_unused_2536_ = lean_ctor_get(v_r_2059_, 1);
lean_dec(v_unused_2536_);
v_unused_2537_ = lean_ctor_get(v_r_2059_, 0);
lean_dec(v_unused_2537_);
v___x_2480_ = v_r_2059_;
v_isShared_2481_ = v_isSharedCheck_2532_;
goto v_resetjp_2479_;
}
else
{
lean_dec(v_r_2059_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2532_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
if (lean_obj_tag(v_l_2399_) == 0)
{
if (lean_obj_tag(v_r_2400_) == 0)
{
lean_object* v_k_2482_; lean_object* v_v_2483_; lean_object* v_size_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2488_; 
v_k_2482_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_k_2482_);
v_v_2483_ = lean_ctor_get(v___x_2406_, 1);
lean_inc(v_v_2483_);
lean_dec_ref(v___x_2406_);
v_size_2484_ = lean_ctor_get(v_l_2399_, 0);
v___x_2485_ = lean_nat_add(v___x_2401_, v_size_2396_);
lean_dec(v_size_2396_);
v___x_2486_ = lean_nat_add(v___x_2401_, v_size_2484_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 4, v_l_2399_);
lean_ctor_set(v___x_2480_, 3, v_tree_2407_);
lean_ctor_set(v___x_2480_, 2, v_v_2483_);
lean_ctor_set(v___x_2480_, 1, v_k_2482_);
lean_ctor_set(v___x_2480_, 0, v___x_2486_);
v___x_2488_ = v___x_2480_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2486_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_k_2482_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_v_2483_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v_tree_2407_);
lean_ctor_set(v_reuseFailAlloc_2492_, 4, v_l_2399_);
v___x_2488_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2490_; 
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 4, v_r_2400_);
lean_ctor_set(v___x_2404_, 3, v___x_2488_);
lean_ctor_set(v___x_2404_, 2, v_v_2398_);
lean_ctor_set(v___x_2404_, 1, v_k_2397_);
lean_ctor_set(v___x_2404_, 0, v___x_2485_);
v___x_2490_ = v___x_2404_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_k_2397_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_v_2398_);
lean_ctor_set(v_reuseFailAlloc_2491_, 3, v___x_2488_);
lean_ctor_set(v_reuseFailAlloc_2491_, 4, v_r_2400_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
else
{
lean_object* v_k_2493_; lean_object* v_v_2494_; lean_object* v_k_2495_; lean_object* v_v_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2510_; 
lean_dec(v_size_2396_);
v_k_2493_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_k_2493_);
v_v_2494_ = lean_ctor_get(v___x_2406_, 1);
lean_inc(v_v_2494_);
lean_dec_ref(v___x_2406_);
v_k_2495_ = lean_ctor_get(v_l_2399_, 1);
v_v_2496_ = lean_ctor_get(v_l_2399_, 2);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_l_2399_);
if (v_isSharedCheck_2510_ == 0)
{
lean_object* v_unused_2511_; lean_object* v_unused_2512_; lean_object* v_unused_2513_; 
v_unused_2511_ = lean_ctor_get(v_l_2399_, 4);
lean_dec(v_unused_2511_);
v_unused_2512_ = lean_ctor_get(v_l_2399_, 3);
lean_dec(v_unused_2512_);
v_unused_2513_ = lean_ctor_get(v_l_2399_, 0);
lean_dec(v_unused_2513_);
v___x_2498_ = v_l_2399_;
v_isShared_2499_ = v_isSharedCheck_2510_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_v_2496_);
lean_inc(v_k_2495_);
lean_dec(v_l_2399_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2510_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2500_ = lean_unsigned_to_nat(3u);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 4, v_r_2400_);
lean_ctor_set(v___x_2498_, 3, v_r_2400_);
lean_ctor_set(v___x_2498_, 2, v_v_2494_);
lean_ctor_set(v___x_2498_, 1, v_k_2493_);
lean_ctor_set(v___x_2498_, 0, v___x_2401_);
v___x_2502_ = v___x_2498_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_k_2493_);
lean_ctor_set(v_reuseFailAlloc_2509_, 2, v_v_2494_);
lean_ctor_set(v_reuseFailAlloc_2509_, 3, v_r_2400_);
lean_ctor_set(v_reuseFailAlloc_2509_, 4, v_r_2400_);
v___x_2502_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v___x_2504_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 3, v_r_2400_);
lean_ctor_set(v___x_2480_, 0, v___x_2401_);
v___x_2504_ = v___x_2480_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v_k_2397_);
lean_ctor_set(v_reuseFailAlloc_2508_, 2, v_v_2398_);
lean_ctor_set(v_reuseFailAlloc_2508_, 3, v_r_2400_);
lean_ctor_set(v_reuseFailAlloc_2508_, 4, v_r_2400_);
v___x_2504_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2506_; 
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 4, v___x_2504_);
lean_ctor_set(v___x_2404_, 3, v___x_2502_);
lean_ctor_set(v___x_2404_, 2, v_v_2496_);
lean_ctor_set(v___x_2404_, 1, v_k_2495_);
lean_ctor_set(v___x_2404_, 0, v___x_2500_);
v___x_2506_ = v___x_2404_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2500_);
lean_ctor_set(v_reuseFailAlloc_2507_, 1, v_k_2495_);
lean_ctor_set(v_reuseFailAlloc_2507_, 2, v_v_2496_);
lean_ctor_set(v_reuseFailAlloc_2507_, 3, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2507_, 4, v___x_2504_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2400_) == 0)
{
lean_object* v_k_2514_; lean_object* v_v_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
lean_dec(v_size_2396_);
v_k_2514_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_k_2514_);
v_v_2515_ = lean_ctor_get(v___x_2406_, 1);
lean_inc(v_v_2515_);
lean_dec_ref(v___x_2406_);
v___x_2516_ = lean_unsigned_to_nat(3u);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 4, v_l_2399_);
lean_ctor_set(v___x_2480_, 2, v_v_2515_);
lean_ctor_set(v___x_2480_, 1, v_k_2514_);
lean_ctor_set(v___x_2480_, 0, v___x_2401_);
v___x_2518_ = v___x_2480_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_k_2514_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_v_2515_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v_l_2399_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v_l_2399_);
v___x_2518_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2520_; 
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 4, v_r_2400_);
lean_ctor_set(v___x_2404_, 3, v___x_2518_);
lean_ctor_set(v___x_2404_, 2, v_v_2398_);
lean_ctor_set(v___x_2404_, 1, v_k_2397_);
lean_ctor_set(v___x_2404_, 0, v___x_2516_);
v___x_2520_ = v___x_2404_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_k_2397_);
lean_ctor_set(v_reuseFailAlloc_2521_, 2, v_v_2398_);
lean_ctor_set(v_reuseFailAlloc_2521_, 3, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2521_, 4, v_r_2400_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
else
{
lean_object* v_k_2523_; lean_object* v_v_2524_; lean_object* v___x_2526_; 
v_k_2523_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_k_2523_);
v_v_2524_ = lean_ctor_get(v___x_2406_, 1);
lean_inc(v_v_2524_);
lean_dec_ref(v___x_2406_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 3, v_r_2400_);
v___x_2526_ = v___x_2480_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_size_2396_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_k_2397_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v_v_2398_);
lean_ctor_set(v_reuseFailAlloc_2531_, 3, v_r_2400_);
lean_ctor_set(v_reuseFailAlloc_2531_, 4, v_r_2400_);
v___x_2526_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2527_ = lean_unsigned_to_nat(2u);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 4, v___x_2526_);
lean_ctor_set(v___x_2404_, 3, v_r_2400_);
lean_ctor_set(v___x_2404_, 2, v_v_2524_);
lean_ctor_set(v___x_2404_, 1, v_k_2523_);
lean_ctor_set(v___x_2404_, 0, v___x_2527_);
v___x_2529_ = v___x_2404_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_k_2523_);
lean_ctor_set(v_reuseFailAlloc_2530_, 2, v_v_2524_);
lean_ctor_set(v_reuseFailAlloc_2530_, 3, v_r_2400_);
lean_ctor_set(v_reuseFailAlloc_2530_, 4, v___x_2526_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
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
lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2696_; 
lean_inc(v_r_2400_);
lean_inc(v_v_2398_);
lean_inc(v_k_2397_);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_r_2059_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; lean_object* v_unused_2698_; lean_object* v_unused_2699_; lean_object* v_unused_2700_; lean_object* v_unused_2701_; 
v_unused_2697_ = lean_ctor_get(v_r_2059_, 4);
lean_dec(v_unused_2697_);
v_unused_2698_ = lean_ctor_get(v_r_2059_, 3);
lean_dec(v_unused_2698_);
v_unused_2699_ = lean_ctor_get(v_r_2059_, 2);
lean_dec(v_unused_2699_);
v_unused_2700_ = lean_ctor_get(v_r_2059_, 1);
lean_dec(v_unused_2700_);
v_unused_2701_ = lean_ctor_get(v_r_2059_, 0);
lean_dec(v_unused_2701_);
v___x_2545_ = v_r_2059_;
v_isShared_2546_ = v_isSharedCheck_2696_;
goto v_resetjp_2544_;
}
else
{
lean_dec(v_r_2059_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2696_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; lean_object* v_tree_2548_; 
v___x_2547_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2397_, v_v_2398_, v_l_2399_, v_r_2400_);
v_tree_2548_ = lean_ctor_get(v___x_2547_, 2);
lean_inc(v_tree_2548_);
if (lean_obj_tag(v_tree_2548_) == 0)
{
lean_object* v_k_2549_; lean_object* v_v_2550_; lean_object* v_size_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v_k_2549_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_k_2549_);
v_v_2550_ = lean_ctor_get(v___x_2547_, 1);
lean_inc(v_v_2550_);
lean_dec_ref(v___x_2547_);
v_size_2551_ = lean_ctor_get(v_tree_2548_, 0);
v___x_2552_ = lean_unsigned_to_nat(3u);
v___x_2553_ = lean_nat_mul(v___x_2552_, v_size_2551_);
v___x_2554_ = lean_nat_dec_lt(v___x_2553_, v_size_2391_);
lean_dec(v___x_2553_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2558_; 
lean_dec(v_r_2395_);
v___x_2555_ = lean_nat_add(v___x_2401_, v_size_2391_);
v___x_2556_ = lean_nat_add(v___x_2555_, v_size_2551_);
lean_dec(v___x_2555_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 4, v_tree_2548_);
lean_ctor_set(v___x_2545_, 3, v_l_2058_);
lean_ctor_set(v___x_2545_, 2, v_v_2550_);
lean_ctor_set(v___x_2545_, 1, v_k_2549_);
lean_ctor_set(v___x_2545_, 0, v___x_2556_);
v___x_2558_ = v___x_2545_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2556_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_k_2549_);
lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_v_2550_);
lean_ctor_set(v_reuseFailAlloc_2559_, 3, v_l_2058_);
lean_ctor_set(v_reuseFailAlloc_2559_, 4, v_tree_2548_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
else
{
lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2625_; 
lean_inc(v_l_2394_);
lean_inc(v_v_2393_);
lean_inc(v_k_2392_);
lean_inc(v_size_2391_);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_l_2058_);
if (v_isSharedCheck_2625_ == 0)
{
lean_object* v_unused_2626_; lean_object* v_unused_2627_; lean_object* v_unused_2628_; lean_object* v_unused_2629_; lean_object* v_unused_2630_; 
v_unused_2626_ = lean_ctor_get(v_l_2058_, 4);
lean_dec(v_unused_2626_);
v_unused_2627_ = lean_ctor_get(v_l_2058_, 3);
lean_dec(v_unused_2627_);
v_unused_2628_ = lean_ctor_get(v_l_2058_, 2);
lean_dec(v_unused_2628_);
v_unused_2629_ = lean_ctor_get(v_l_2058_, 1);
lean_dec(v_unused_2629_);
v_unused_2630_ = lean_ctor_get(v_l_2058_, 0);
lean_dec(v_unused_2630_);
v___x_2561_ = v_l_2058_;
v_isShared_2562_ = v_isSharedCheck_2625_;
goto v_resetjp_2560_;
}
else
{
lean_dec(v_l_2058_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2625_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v_size_2563_; lean_object* v_size_2564_; lean_object* v_k_2565_; lean_object* v_v_2566_; lean_object* v_l_2567_; lean_object* v_r_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v_size_2563_ = lean_ctor_get(v_l_2394_, 0);
v_size_2564_ = lean_ctor_get(v_r_2395_, 0);
v_k_2565_ = lean_ctor_get(v_r_2395_, 1);
v_v_2566_ = lean_ctor_get(v_r_2395_, 2);
v_l_2567_ = lean_ctor_get(v_r_2395_, 3);
v_r_2568_ = lean_ctor_get(v_r_2395_, 4);
v___x_2569_ = lean_unsigned_to_nat(2u);
v___x_2570_ = lean_nat_mul(v___x_2569_, v_size_2563_);
v___x_2571_ = lean_nat_dec_lt(v_size_2564_, v___x_2570_);
lean_dec(v___x_2570_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2609_; 
lean_inc(v_r_2568_);
lean_inc(v_l_2567_);
lean_inc(v_v_2566_);
lean_inc(v_k_2565_);
lean_del_object(v___x_2561_);
v_isSharedCheck_2609_ = !lean_is_exclusive(v_r_2395_);
if (v_isSharedCheck_2609_ == 0)
{
lean_object* v_unused_2610_; lean_object* v_unused_2611_; lean_object* v_unused_2612_; lean_object* v_unused_2613_; lean_object* v_unused_2614_; 
v_unused_2610_ = lean_ctor_get(v_r_2395_, 4);
lean_dec(v_unused_2610_);
v_unused_2611_ = lean_ctor_get(v_r_2395_, 3);
lean_dec(v_unused_2611_);
v_unused_2612_ = lean_ctor_get(v_r_2395_, 2);
lean_dec(v_unused_2612_);
v_unused_2613_ = lean_ctor_get(v_r_2395_, 1);
lean_dec(v_unused_2613_);
v_unused_2614_ = lean_ctor_get(v_r_2395_, 0);
lean_dec(v_unused_2614_);
v___x_2573_ = v_r_2395_;
v_isShared_2574_ = v_isSharedCheck_2609_;
goto v_resetjp_2572_;
}
else
{
lean_dec(v_r_2395_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2609_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___x_2597_; lean_object* v___y_2599_; 
v___x_2575_ = lean_nat_add(v___x_2401_, v_size_2391_);
lean_dec(v_size_2391_);
v___x_2576_ = lean_nat_add(v___x_2575_, v_size_2551_);
lean_dec(v___x_2575_);
v___x_2597_ = lean_nat_add(v___x_2401_, v_size_2563_);
if (lean_obj_tag(v_l_2567_) == 0)
{
lean_object* v_size_2607_; 
v_size_2607_ = lean_ctor_get(v_l_2567_, 0);
lean_inc(v_size_2607_);
v___y_2599_ = v_size_2607_;
goto v___jp_2598_;
}
else
{
lean_object* v___x_2608_; 
v___x_2608_ = lean_unsigned_to_nat(0u);
v___y_2599_ = v___x_2608_;
goto v___jp_2598_;
}
v___jp_2577_:
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2581_ = lean_nat_add(v___y_2579_, v___y_2580_);
lean_dec(v___y_2580_);
lean_dec(v___y_2579_);
lean_inc_ref(v_tree_2548_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 4, v_tree_2548_);
lean_ctor_set(v___x_2573_, 3, v_r_2568_);
lean_ctor_set(v___x_2573_, 2, v_v_2550_);
lean_ctor_set(v___x_2573_, 1, v_k_2549_);
lean_ctor_set(v___x_2573_, 0, v___x_2581_);
v___x_2583_ = v___x_2573_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2581_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_k_2549_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v_v_2550_);
lean_ctor_set(v_reuseFailAlloc_2596_, 3, v_r_2568_);
lean_ctor_set(v_reuseFailAlloc_2596_, 4, v_tree_2548_);
v___x_2583_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
v_isSharedCheck_2590_ = !lean_is_exclusive(v_tree_2548_);
if (v_isSharedCheck_2590_ == 0)
{
lean_object* v_unused_2591_; lean_object* v_unused_2592_; lean_object* v_unused_2593_; lean_object* v_unused_2594_; lean_object* v_unused_2595_; 
v_unused_2591_ = lean_ctor_get(v_tree_2548_, 4);
lean_dec(v_unused_2591_);
v_unused_2592_ = lean_ctor_get(v_tree_2548_, 3);
lean_dec(v_unused_2592_);
v_unused_2593_ = lean_ctor_get(v_tree_2548_, 2);
lean_dec(v_unused_2593_);
v_unused_2594_ = lean_ctor_get(v_tree_2548_, 1);
lean_dec(v_unused_2594_);
v_unused_2595_ = lean_ctor_get(v_tree_2548_, 0);
lean_dec(v_unused_2595_);
v___x_2585_ = v_tree_2548_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_dec(v_tree_2548_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 4, v___x_2583_);
lean_ctor_set(v___x_2585_, 3, v___y_2578_);
lean_ctor_set(v___x_2585_, 2, v_v_2566_);
lean_ctor_set(v___x_2585_, 1, v_k_2565_);
lean_ctor_set(v___x_2585_, 0, v___x_2576_);
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2576_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_k_2565_);
lean_ctor_set(v_reuseFailAlloc_2589_, 2, v_v_2566_);
lean_ctor_set(v_reuseFailAlloc_2589_, 3, v___y_2578_);
lean_ctor_set(v_reuseFailAlloc_2589_, 4, v___x_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
v___jp_2598_:
{
lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2600_ = lean_nat_add(v___x_2597_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec(v___x_2597_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 4, v_l_2567_);
lean_ctor_set(v___x_2545_, 3, v_l_2394_);
lean_ctor_set(v___x_2545_, 2, v_v_2393_);
lean_ctor_set(v___x_2545_, 1, v_k_2392_);
lean_ctor_set(v___x_2545_, 0, v___x_2600_);
v___x_2602_ = v___x_2545_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_k_2392_);
lean_ctor_set(v_reuseFailAlloc_2606_, 2, v_v_2393_);
lean_ctor_set(v_reuseFailAlloc_2606_, 3, v_l_2394_);
lean_ctor_set(v_reuseFailAlloc_2606_, 4, v_l_2567_);
v___x_2602_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2603_; 
v___x_2603_ = lean_nat_add(v___x_2401_, v_size_2551_);
if (lean_obj_tag(v_r_2568_) == 0)
{
lean_object* v_size_2604_; 
v_size_2604_ = lean_ctor_get(v_r_2568_, 0);
lean_inc(v_size_2604_);
v___y_2578_ = v___x_2602_;
v___y_2579_ = v___x_2603_;
v___y_2580_ = v_size_2604_;
goto v___jp_2577_;
}
else
{
lean_object* v___x_2605_; 
v___x_2605_ = lean_unsigned_to_nat(0u);
v___y_2578_ = v___x_2602_;
v___y_2579_ = v___x_2603_;
v___y_2580_ = v___x_2605_;
goto v___jp_2577_;
}
}
}
}
}
else
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2620_; 
v___x_2615_ = lean_nat_add(v___x_2401_, v_size_2391_);
lean_dec(v_size_2391_);
v___x_2616_ = lean_nat_add(v___x_2615_, v_size_2551_);
lean_dec(v___x_2615_);
v___x_2617_ = lean_nat_add(v___x_2401_, v_size_2551_);
v___x_2618_ = lean_nat_add(v___x_2617_, v_size_2564_);
lean_dec(v___x_2617_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 4, v_tree_2548_);
lean_ctor_set(v___x_2545_, 3, v_r_2395_);
lean_ctor_set(v___x_2545_, 2, v_v_2550_);
lean_ctor_set(v___x_2545_, 1, v_k_2549_);
lean_ctor_set(v___x_2545_, 0, v___x_2618_);
v___x_2620_ = v___x_2545_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_k_2549_);
lean_ctor_set(v_reuseFailAlloc_2624_, 2, v_v_2550_);
lean_ctor_set(v_reuseFailAlloc_2624_, 3, v_r_2395_);
lean_ctor_set(v_reuseFailAlloc_2624_, 4, v_tree_2548_);
v___x_2620_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
lean_object* v___x_2622_; 
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 4, v___x_2620_);
lean_ctor_set(v___x_2561_, 0, v___x_2616_);
v___x_2622_ = v___x_2561_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2616_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_k_2392_);
lean_ctor_set(v_reuseFailAlloc_2623_, 2, v_v_2393_);
lean_ctor_set(v_reuseFailAlloc_2623_, 3, v_l_2394_);
lean_ctor_set(v_reuseFailAlloc_2623_, 4, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2394_) == 0)
{
lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2654_; 
lean_inc_ref(v_l_2394_);
lean_inc(v_v_2393_);
lean_inc(v_k_2392_);
lean_inc(v_size_2391_);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_l_2058_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; lean_object* v_unused_2656_; lean_object* v_unused_2657_; lean_object* v_unused_2658_; lean_object* v_unused_2659_; 
v_unused_2655_ = lean_ctor_get(v_l_2058_, 4);
lean_dec(v_unused_2655_);
v_unused_2656_ = lean_ctor_get(v_l_2058_, 3);
lean_dec(v_unused_2656_);
v_unused_2657_ = lean_ctor_get(v_l_2058_, 2);
lean_dec(v_unused_2657_);
v_unused_2658_ = lean_ctor_get(v_l_2058_, 1);
lean_dec(v_unused_2658_);
v_unused_2659_ = lean_ctor_get(v_l_2058_, 0);
lean_dec(v_unused_2659_);
v___x_2632_ = v_l_2058_;
v_isShared_2633_ = v_isSharedCheck_2654_;
goto v_resetjp_2631_;
}
else
{
lean_dec(v_l_2058_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2654_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
if (lean_obj_tag(v_r_2395_) == 0)
{
lean_object* v_k_2634_; lean_object* v_v_2635_; lean_object* v_size_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2640_; 
v_k_2634_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_k_2634_);
v_v_2635_ = lean_ctor_get(v___x_2547_, 1);
lean_inc(v_v_2635_);
lean_dec_ref(v___x_2547_);
v_size_2636_ = lean_ctor_get(v_r_2395_, 0);
v___x_2637_ = lean_nat_add(v___x_2401_, v_size_2391_);
lean_dec(v_size_2391_);
v___x_2638_ = lean_nat_add(v___x_2401_, v_size_2636_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 4, v_tree_2548_);
lean_ctor_set(v___x_2545_, 3, v_r_2395_);
lean_ctor_set(v___x_2545_, 2, v_v_2635_);
lean_ctor_set(v___x_2545_, 1, v_k_2634_);
lean_ctor_set(v___x_2545_, 0, v___x_2638_);
v___x_2640_ = v___x_2545_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2638_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_k_2634_);
lean_ctor_set(v_reuseFailAlloc_2644_, 2, v_v_2635_);
lean_ctor_set(v_reuseFailAlloc_2644_, 3, v_r_2395_);
lean_ctor_set(v_reuseFailAlloc_2644_, 4, v_tree_2548_);
v___x_2640_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
lean_object* v___x_2642_; 
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 4, v___x_2640_);
lean_ctor_set(v___x_2632_, 0, v___x_2637_);
v___x_2642_ = v___x_2632_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_k_2392_);
lean_ctor_set(v_reuseFailAlloc_2643_, 2, v_v_2393_);
lean_ctor_set(v_reuseFailAlloc_2643_, 3, v_l_2394_);
lean_ctor_set(v_reuseFailAlloc_2643_, 4, v___x_2640_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
else
{
lean_object* v_k_2645_; lean_object* v_v_2646_; lean_object* v___x_2647_; lean_object* v___x_2649_; 
lean_dec(v_size_2391_);
v_k_2645_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_k_2645_);
v_v_2646_ = lean_ctor_get(v___x_2547_, 1);
lean_inc(v_v_2646_);
lean_dec_ref(v___x_2547_);
v___x_2647_ = lean_unsigned_to_nat(3u);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 4, v_r_2395_);
lean_ctor_set(v___x_2545_, 3, v_r_2395_);
lean_ctor_set(v___x_2545_, 2, v_v_2646_);
lean_ctor_set(v___x_2545_, 1, v_k_2645_);
lean_ctor_set(v___x_2545_, 0, v___x_2401_);
v___x_2649_ = v___x_2545_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_k_2645_);
lean_ctor_set(v_reuseFailAlloc_2653_, 2, v_v_2646_);
lean_ctor_set(v_reuseFailAlloc_2653_, 3, v_r_2395_);
lean_ctor_set(v_reuseFailAlloc_2653_, 4, v_r_2395_);
v___x_2649_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2651_; 
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 4, v___x_2649_);
lean_ctor_set(v___x_2632_, 0, v___x_2647_);
v___x_2651_ = v___x_2632_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2647_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v_k_2392_);
lean_ctor_set(v_reuseFailAlloc_2652_, 2, v_v_2393_);
lean_ctor_set(v_reuseFailAlloc_2652_, 3, v_l_2394_);
lean_ctor_set(v_reuseFailAlloc_2652_, 4, v___x_2649_);
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
else
{
if (lean_obj_tag(v_r_2395_) == 0)
{
lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2684_; 
lean_inc(v_l_2394_);
lean_inc(v_v_2393_);
lean_inc(v_k_2392_);
v_isSharedCheck_2684_ = !lean_is_exclusive(v_l_2058_);
if (v_isSharedCheck_2684_ == 0)
{
lean_object* v_unused_2685_; lean_object* v_unused_2686_; lean_object* v_unused_2687_; lean_object* v_unused_2688_; lean_object* v_unused_2689_; 
v_unused_2685_ = lean_ctor_get(v_l_2058_, 4);
lean_dec(v_unused_2685_);
v_unused_2686_ = lean_ctor_get(v_l_2058_, 3);
lean_dec(v_unused_2686_);
v_unused_2687_ = lean_ctor_get(v_l_2058_, 2);
lean_dec(v_unused_2687_);
v_unused_2688_ = lean_ctor_get(v_l_2058_, 1);
lean_dec(v_unused_2688_);
v_unused_2689_ = lean_ctor_get(v_l_2058_, 0);
lean_dec(v_unused_2689_);
v___x_2661_ = v_l_2058_;
v_isShared_2662_ = v_isSharedCheck_2684_;
goto v_resetjp_2660_;
}
else
{
lean_dec(v_l_2058_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2684_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v_k_2663_; lean_object* v_v_2664_; lean_object* v_k_2665_; lean_object* v_v_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2680_; 
v_k_2663_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_k_2663_);
v_v_2664_ = lean_ctor_get(v___x_2547_, 1);
lean_inc(v_v_2664_);
lean_dec_ref(v___x_2547_);
v_k_2665_ = lean_ctor_get(v_r_2395_, 1);
v_v_2666_ = lean_ctor_get(v_r_2395_, 2);
v_isSharedCheck_2680_ = !lean_is_exclusive(v_r_2395_);
if (v_isSharedCheck_2680_ == 0)
{
lean_object* v_unused_2681_; lean_object* v_unused_2682_; lean_object* v_unused_2683_; 
v_unused_2681_ = lean_ctor_get(v_r_2395_, 4);
lean_dec(v_unused_2681_);
v_unused_2682_ = lean_ctor_get(v_r_2395_, 3);
lean_dec(v_unused_2682_);
v_unused_2683_ = lean_ctor_get(v_r_2395_, 0);
lean_dec(v_unused_2683_);
v___x_2668_ = v_r_2395_;
v_isShared_2669_ = v_isSharedCheck_2680_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_v_2666_);
lean_inc(v_k_2665_);
lean_dec(v_r_2395_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2680_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2670_ = lean_unsigned_to_nat(3u);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 4, v_l_2394_);
lean_ctor_set(v___x_2668_, 3, v_l_2394_);
lean_ctor_set(v___x_2668_, 2, v_v_2393_);
lean_ctor_set(v___x_2668_, 1, v_k_2392_);
lean_ctor_set(v___x_2668_, 0, v___x_2401_);
v___x_2672_ = v___x_2668_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_k_2392_);
lean_ctor_set(v_reuseFailAlloc_2679_, 2, v_v_2393_);
lean_ctor_set(v_reuseFailAlloc_2679_, 3, v_l_2394_);
lean_ctor_set(v_reuseFailAlloc_2679_, 4, v_l_2394_);
v___x_2672_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2674_; 
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 4, v_l_2394_);
lean_ctor_set(v___x_2545_, 3, v_l_2394_);
lean_ctor_set(v___x_2545_, 2, v_v_2664_);
lean_ctor_set(v___x_2545_, 1, v_k_2663_);
lean_ctor_set(v___x_2545_, 0, v___x_2401_);
v___x_2674_ = v___x_2545_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_k_2663_);
lean_ctor_set(v_reuseFailAlloc_2678_, 2, v_v_2664_);
lean_ctor_set(v_reuseFailAlloc_2678_, 3, v_l_2394_);
lean_ctor_set(v_reuseFailAlloc_2678_, 4, v_l_2394_);
v___x_2674_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2676_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 4, v___x_2674_);
lean_ctor_set(v___x_2661_, 3, v___x_2672_);
lean_ctor_set(v___x_2661_, 2, v_v_2666_);
lean_ctor_set(v___x_2661_, 1, v_k_2665_);
lean_ctor_set(v___x_2661_, 0, v___x_2670_);
v___x_2676_ = v___x_2661_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_k_2665_);
lean_ctor_set(v_reuseFailAlloc_2677_, 2, v_v_2666_);
lean_ctor_set(v_reuseFailAlloc_2677_, 3, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2677_, 4, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
}
}
else
{
lean_object* v_k_2690_; lean_object* v_v_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
v_k_2690_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_k_2690_);
v_v_2691_ = lean_ctor_get(v___x_2547_, 1);
lean_inc(v_v_2691_);
lean_dec_ref(v___x_2547_);
v___x_2692_ = lean_unsigned_to_nat(2u);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 4, v_r_2395_);
lean_ctor_set(v___x_2545_, 3, v_l_2058_);
lean_ctor_set(v___x_2545_, 2, v_v_2691_);
lean_ctor_set(v___x_2545_, 1, v_k_2690_);
lean_ctor_set(v___x_2545_, 0, v___x_2692_);
v___x_2694_ = v___x_2545_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v_k_2690_);
lean_ctor_set(v_reuseFailAlloc_2695_, 2, v_v_2691_);
lean_ctor_set(v_reuseFailAlloc_2695_, 3, v_l_2058_);
lean_ctor_set(v_reuseFailAlloc_2695_, 4, v_r_2395_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
}
}
else
{
return v_l_2058_;
}
}
else
{
return v_r_2059_;
}
}
default: 
{
goto v___jp_2096_;
}
}
}
else
{
goto v___jp_2096_;
}
}
else
{
lean_del_object(v___x_2061_);
goto v___jp_2248_;
}
v___jp_2063_:
{
lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2072_ = lean_nat_add(v___y_2069_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec(v___y_2069_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 4, v___y_2065_);
lean_ctor_set(v___x_2061_, 3, v___y_2068_);
lean_ctor_set(v___x_2061_, 0, v___x_2072_);
v___x_2074_ = v___x_2061_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_k_2056_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_v_2057_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v___y_2068_);
lean_ctor_set(v_reuseFailAlloc_2076_, 4, v___y_2065_);
v___x_2074_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2075_, 0, v___y_2067_);
lean_ctor_set(v___x_2075_, 1, v___y_2064_);
lean_ctor_set(v___x_2075_, 2, v___y_2070_);
lean_ctor_set(v___x_2075_, 3, v___y_2066_);
lean_ctor_set(v___x_2075_, 4, v___x_2074_);
return v___x_2075_;
}
}
v___jp_2077_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_nat_add(v___y_2081_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec(v___y_2081_);
v___x_2092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v___y_2083_);
lean_ctor_set(v___x_2092_, 2, v___y_2084_);
lean_ctor_set(v___x_2092_, 3, v___y_2088_);
lean_ctor_set(v___x_2092_, 4, v___y_2087_);
v___x_2093_ = lean_nat_add(v___y_2080_, v___y_2086_);
lean_dec(v___y_2086_);
if (lean_obj_tag(v___y_2085_) == 0)
{
lean_object* v_size_2094_; 
v_size_2094_ = lean_ctor_get(v___y_2085_, 0);
lean_inc(v_size_2094_);
v___y_2064_ = v___y_2079_;
v___y_2065_ = v___y_2078_;
v___y_2066_ = v___x_2092_;
v___y_2067_ = v___y_2082_;
v___y_2068_ = v___y_2085_;
v___y_2069_ = v___x_2093_;
v___y_2070_ = v___y_2089_;
v___y_2071_ = v_size_2094_;
goto v___jp_2063_;
}
else
{
lean_object* v___x_2095_; 
v___x_2095_ = lean_unsigned_to_nat(0u);
v___y_2064_ = v___y_2079_;
v___y_2065_ = v___y_2078_;
v___y_2066_ = v___x_2092_;
v___y_2067_ = v___y_2082_;
v___y_2068_ = v___y_2085_;
v___y_2069_ = v___x_2093_;
v___y_2070_ = v___y_2089_;
v___y_2071_ = v___x_2095_;
goto v___jp_2063_;
}
}
v___jp_2096_:
{
lean_object* v_impl_2097_; lean_object* v___x_2098_; 
v_impl_2097_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v_k_2040_, v_r_2059_);
v___x_2098_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2097_) == 0)
{
if (lean_obj_tag(v_l_2058_) == 0)
{
lean_object* v_size_2099_; lean_object* v_size_2100_; lean_object* v_k_2101_; lean_object* v_v_2102_; lean_object* v_l_2103_; lean_object* v_r_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v_size_2099_ = lean_ctor_get(v_impl_2097_, 0);
lean_inc(v_size_2099_);
v_size_2100_ = lean_ctor_get(v_l_2058_, 0);
v_k_2101_ = lean_ctor_get(v_l_2058_, 1);
v_v_2102_ = lean_ctor_get(v_l_2058_, 2);
v_l_2103_ = lean_ctor_get(v_l_2058_, 3);
v_r_2104_ = lean_ctor_get(v_l_2058_, 4);
v___x_2105_ = lean_unsigned_to_nat(3u);
v___x_2106_ = lean_nat_mul(v___x_2105_, v_size_2099_);
v___x_2107_ = lean_nat_dec_lt(v___x_2106_, v_size_2100_);
lean_dec(v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_del_object(v___x_2061_);
v___x_2108_ = lean_nat_add(v___x_2098_, v_size_2100_);
v___x_2109_ = lean_nat_add(v___x_2108_, v_size_2099_);
lean_dec(v_size_2099_);
lean_dec(v___x_2108_);
v___x_2110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
lean_ctor_set(v___x_2110_, 1, v_k_2056_);
lean_ctor_set(v___x_2110_, 2, v_v_2057_);
lean_ctor_set(v___x_2110_, 3, v_l_2058_);
lean_ctor_set(v___x_2110_, 4, v_impl_2097_);
return v___x_2110_;
}
else
{
lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2147_; 
lean_inc(v_r_2104_);
lean_inc(v_l_2103_);
lean_inc(v_v_2102_);
lean_inc(v_k_2101_);
lean_inc(v_size_2100_);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_l_2058_);
if (v_isSharedCheck_2147_ == 0)
{
lean_object* v_unused_2148_; lean_object* v_unused_2149_; lean_object* v_unused_2150_; lean_object* v_unused_2151_; lean_object* v_unused_2152_; 
v_unused_2148_ = lean_ctor_get(v_l_2058_, 4);
lean_dec(v_unused_2148_);
v_unused_2149_ = lean_ctor_get(v_l_2058_, 3);
lean_dec(v_unused_2149_);
v_unused_2150_ = lean_ctor_get(v_l_2058_, 2);
lean_dec(v_unused_2150_);
v_unused_2151_ = lean_ctor_get(v_l_2058_, 1);
lean_dec(v_unused_2151_);
v_unused_2152_ = lean_ctor_get(v_l_2058_, 0);
lean_dec(v_unused_2152_);
v___x_2112_ = v_l_2058_;
v_isShared_2113_ = v_isSharedCheck_2147_;
goto v_resetjp_2111_;
}
else
{
lean_dec(v_l_2058_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2147_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v_size_2114_; lean_object* v_size_2115_; lean_object* v_k_2116_; lean_object* v_v_2117_; lean_object* v_l_2118_; lean_object* v_r_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v_size_2114_ = lean_ctor_get(v_l_2103_, 0);
v_size_2115_ = lean_ctor_get(v_r_2104_, 0);
v_k_2116_ = lean_ctor_get(v_r_2104_, 1);
v_v_2117_ = lean_ctor_get(v_r_2104_, 2);
v_l_2118_ = lean_ctor_get(v_r_2104_, 3);
v_r_2119_ = lean_ctor_get(v_r_2104_, 4);
v___x_2120_ = lean_unsigned_to_nat(2u);
v___x_2121_ = lean_nat_mul(v___x_2120_, v_size_2114_);
v___x_2122_ = lean_nat_dec_lt(v_size_2115_, v___x_2121_);
lean_dec(v___x_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_inc(v_r_2119_);
lean_inc(v_l_2118_);
lean_inc(v_v_2117_);
lean_inc(v_k_2116_);
lean_del_object(v___x_2112_);
lean_dec(v_r_2104_);
v___x_2123_ = lean_nat_add(v___x_2098_, v_size_2100_);
lean_dec(v_size_2100_);
v___x_2124_ = lean_nat_add(v___x_2123_, v_size_2099_);
lean_dec(v___x_2123_);
v___x_2125_ = lean_nat_add(v___x_2098_, v_size_2114_);
if (lean_obj_tag(v_l_2118_) == 0)
{
lean_object* v_size_2126_; 
v_size_2126_ = lean_ctor_get(v_l_2118_, 0);
lean_inc(v_size_2126_);
v___y_2078_ = v_impl_2097_;
v___y_2079_ = v_k_2116_;
v___y_2080_ = v___x_2098_;
v___y_2081_ = v___x_2125_;
v___y_2082_ = v___x_2124_;
v___y_2083_ = v_k_2101_;
v___y_2084_ = v_v_2102_;
v___y_2085_ = v_r_2119_;
v___y_2086_ = v_size_2099_;
v___y_2087_ = v_l_2118_;
v___y_2088_ = v_l_2103_;
v___y_2089_ = v_v_2117_;
v___y_2090_ = v_size_2126_;
goto v___jp_2077_;
}
else
{
lean_object* v___x_2127_; 
v___x_2127_ = lean_unsigned_to_nat(0u);
v___y_2078_ = v_impl_2097_;
v___y_2079_ = v_k_2116_;
v___y_2080_ = v___x_2098_;
v___y_2081_ = v___x_2125_;
v___y_2082_ = v___x_2124_;
v___y_2083_ = v_k_2101_;
v___y_2084_ = v_v_2102_;
v___y_2085_ = v_r_2119_;
v___y_2086_ = v_size_2099_;
v___y_2087_ = v_l_2118_;
v___y_2088_ = v_l_2103_;
v___y_2089_ = v_v_2117_;
v___y_2090_ = v___x_2127_;
goto v___jp_2077_;
}
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2133_; 
lean_del_object(v___x_2061_);
v___x_2128_ = lean_nat_add(v___x_2098_, v_size_2100_);
lean_dec(v_size_2100_);
v___x_2129_ = lean_nat_add(v___x_2128_, v_size_2099_);
lean_dec(v___x_2128_);
v___x_2130_ = lean_nat_add(v___x_2098_, v_size_2099_);
lean_dec(v_size_2099_);
v___x_2131_ = lean_nat_add(v___x_2130_, v_size_2115_);
lean_dec(v___x_2130_);
lean_inc_ref(v_impl_2097_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 4, v_impl_2097_);
lean_ctor_set(v___x_2112_, 3, v_r_2104_);
lean_ctor_set(v___x_2112_, 2, v_v_2057_);
lean_ctor_set(v___x_2112_, 1, v_k_2056_);
lean_ctor_set(v___x_2112_, 0, v___x_2131_);
v___x_2133_ = v___x_2112_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_k_2056_);
lean_ctor_set(v_reuseFailAlloc_2146_, 2, v_v_2057_);
lean_ctor_set(v_reuseFailAlloc_2146_, 3, v_r_2104_);
lean_ctor_set(v_reuseFailAlloc_2146_, 4, v_impl_2097_);
v___x_2133_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
v_isSharedCheck_2140_ = !lean_is_exclusive(v_impl_2097_);
if (v_isSharedCheck_2140_ == 0)
{
lean_object* v_unused_2141_; lean_object* v_unused_2142_; lean_object* v_unused_2143_; lean_object* v_unused_2144_; lean_object* v_unused_2145_; 
v_unused_2141_ = lean_ctor_get(v_impl_2097_, 4);
lean_dec(v_unused_2141_);
v_unused_2142_ = lean_ctor_get(v_impl_2097_, 3);
lean_dec(v_unused_2142_);
v_unused_2143_ = lean_ctor_get(v_impl_2097_, 2);
lean_dec(v_unused_2143_);
v_unused_2144_ = lean_ctor_get(v_impl_2097_, 1);
lean_dec(v_unused_2144_);
v_unused_2145_ = lean_ctor_get(v_impl_2097_, 0);
lean_dec(v_unused_2145_);
v___x_2135_ = v_impl_2097_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_dec(v_impl_2097_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 4, v___x_2133_);
lean_ctor_set(v___x_2135_, 3, v_l_2103_);
lean_ctor_set(v___x_2135_, 2, v_v_2102_);
lean_ctor_set(v___x_2135_, 1, v_k_2101_);
lean_ctor_set(v___x_2135_, 0, v___x_2129_);
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2129_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_k_2101_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v_v_2102_);
lean_ctor_set(v_reuseFailAlloc_2139_, 3, v_l_2103_);
lean_ctor_set(v_reuseFailAlloc_2139_, 4, v___x_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_del_object(v___x_2061_);
v_size_2153_ = lean_ctor_get(v_impl_2097_, 0);
lean_inc(v_size_2153_);
v___x_2154_ = lean_nat_add(v___x_2098_, v_size_2153_);
lean_dec(v_size_2153_);
v___x_2155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
lean_ctor_set(v___x_2155_, 1, v_k_2056_);
lean_ctor_set(v___x_2155_, 2, v_v_2057_);
lean_ctor_set(v___x_2155_, 3, v_l_2058_);
lean_ctor_set(v___x_2155_, 4, v_impl_2097_);
return v___x_2155_;
}
}
else
{
lean_del_object(v___x_2061_);
if (lean_obj_tag(v_l_2058_) == 0)
{
lean_object* v_l_2156_; 
v_l_2156_ = lean_ctor_get(v_l_2058_, 3);
if (lean_obj_tag(v_l_2156_) == 0)
{
lean_object* v_r_2157_; 
lean_inc_ref(v_l_2156_);
v_r_2157_ = lean_ctor_get(v_l_2058_, 4);
lean_inc(v_r_2157_);
if (lean_obj_tag(v_r_2157_) == 0)
{
lean_object* v_size_2158_; lean_object* v_k_2159_; lean_object* v_v_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2182_; 
v_size_2158_ = lean_ctor_get(v_l_2058_, 0);
v_k_2159_ = lean_ctor_get(v_l_2058_, 1);
v_v_2160_ = lean_ctor_get(v_l_2058_, 2);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_l_2058_);
if (v_isSharedCheck_2182_ == 0)
{
lean_object* v_unused_2183_; lean_object* v_unused_2184_; 
v_unused_2183_ = lean_ctor_get(v_l_2058_, 4);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_l_2058_, 3);
lean_dec(v_unused_2184_);
v___x_2162_ = v_l_2058_;
v_isShared_2163_ = v_isSharedCheck_2182_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_v_2160_);
lean_inc(v_k_2159_);
lean_inc(v_size_2158_);
lean_dec(v_l_2058_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2182_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v_size_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
v_size_2164_ = lean_ctor_get(v_r_2157_, 0);
v___x_2165_ = lean_nat_add(v___x_2098_, v_size_2158_);
lean_dec(v_size_2158_);
v___x_2166_ = lean_nat_add(v___x_2098_, v_size_2164_);
lean_inc_ref(v_r_2157_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 4, v_impl_2097_);
lean_ctor_set(v___x_2162_, 3, v_r_2157_);
lean_ctor_set(v___x_2162_, 2, v_v_2057_);
lean_ctor_set(v___x_2162_, 1, v_k_2056_);
lean_ctor_set(v___x_2162_, 0, v___x_2166_);
v___x_2168_ = v___x_2162_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_k_2056_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v_v_2057_);
lean_ctor_set(v_reuseFailAlloc_2181_, 3, v_r_2157_);
lean_ctor_set(v_reuseFailAlloc_2181_, 4, v_impl_2097_);
v___x_2168_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
v_isSharedCheck_2175_ = !lean_is_exclusive(v_r_2157_);
if (v_isSharedCheck_2175_ == 0)
{
lean_object* v_unused_2176_; lean_object* v_unused_2177_; lean_object* v_unused_2178_; lean_object* v_unused_2179_; lean_object* v_unused_2180_; 
v_unused_2176_ = lean_ctor_get(v_r_2157_, 4);
lean_dec(v_unused_2176_);
v_unused_2177_ = lean_ctor_get(v_r_2157_, 3);
lean_dec(v_unused_2177_);
v_unused_2178_ = lean_ctor_get(v_r_2157_, 2);
lean_dec(v_unused_2178_);
v_unused_2179_ = lean_ctor_get(v_r_2157_, 1);
lean_dec(v_unused_2179_);
v_unused_2180_ = lean_ctor_get(v_r_2157_, 0);
lean_dec(v_unused_2180_);
v___x_2170_ = v_r_2157_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_dec(v_r_2157_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 4, v___x_2168_);
lean_ctor_set(v___x_2170_, 3, v_l_2156_);
lean_ctor_set(v___x_2170_, 2, v_v_2160_);
lean_ctor_set(v___x_2170_, 1, v_k_2159_);
lean_ctor_set(v___x_2170_, 0, v___x_2165_);
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_k_2159_);
lean_ctor_set(v_reuseFailAlloc_2174_, 2, v_v_2160_);
lean_ctor_set(v_reuseFailAlloc_2174_, 3, v_l_2156_);
lean_ctor_set(v_reuseFailAlloc_2174_, 4, v___x_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
else
{
lean_object* v_k_2185_; lean_object* v_v_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2195_; 
v_k_2185_ = lean_ctor_get(v_l_2058_, 1);
v_v_2186_ = lean_ctor_get(v_l_2058_, 2);
v_isSharedCheck_2195_ = !lean_is_exclusive(v_l_2058_);
if (v_isSharedCheck_2195_ == 0)
{
lean_object* v_unused_2196_; lean_object* v_unused_2197_; lean_object* v_unused_2198_; 
v_unused_2196_ = lean_ctor_get(v_l_2058_, 4);
lean_dec(v_unused_2196_);
v_unused_2197_ = lean_ctor_get(v_l_2058_, 3);
lean_dec(v_unused_2197_);
v_unused_2198_ = lean_ctor_get(v_l_2058_, 0);
lean_dec(v_unused_2198_);
v___x_2188_ = v_l_2058_;
v_isShared_2189_ = v_isSharedCheck_2195_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_v_2186_);
lean_inc(v_k_2185_);
lean_dec(v_l_2058_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2195_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2190_ = lean_unsigned_to_nat(3u);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 3, v_r_2157_);
lean_ctor_set(v___x_2188_, 2, v_v_2057_);
lean_ctor_set(v___x_2188_, 1, v_k_2056_);
lean_ctor_set(v___x_2188_, 0, v___x_2098_);
v___x_2192_ = v___x_2188_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_k_2056_);
lean_ctor_set(v_reuseFailAlloc_2194_, 2, v_v_2057_);
lean_ctor_set(v_reuseFailAlloc_2194_, 3, v_r_2157_);
lean_ctor_set(v_reuseFailAlloc_2194_, 4, v_r_2157_);
v___x_2192_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2193_; 
v___x_2193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2190_);
lean_ctor_set(v___x_2193_, 1, v_k_2185_);
lean_ctor_set(v___x_2193_, 2, v_v_2186_);
lean_ctor_set(v___x_2193_, 3, v_l_2156_);
lean_ctor_set(v___x_2193_, 4, v___x_2192_);
return v___x_2193_;
}
}
}
}
else
{
lean_object* v_r_2199_; 
v_r_2199_ = lean_ctor_get(v_l_2058_, 4);
lean_inc(v_r_2199_);
if (lean_obj_tag(v_r_2199_) == 0)
{
lean_object* v_k_2200_; lean_object* v_v_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2222_; 
lean_inc(v_l_2156_);
v_k_2200_ = lean_ctor_get(v_l_2058_, 1);
v_v_2201_ = lean_ctor_get(v_l_2058_, 2);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_l_2058_);
if (v_isSharedCheck_2222_ == 0)
{
lean_object* v_unused_2223_; lean_object* v_unused_2224_; lean_object* v_unused_2225_; 
v_unused_2223_ = lean_ctor_get(v_l_2058_, 4);
lean_dec(v_unused_2223_);
v_unused_2224_ = lean_ctor_get(v_l_2058_, 3);
lean_dec(v_unused_2224_);
v_unused_2225_ = lean_ctor_get(v_l_2058_, 0);
lean_dec(v_unused_2225_);
v___x_2203_ = v_l_2058_;
v_isShared_2204_ = v_isSharedCheck_2222_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_v_2201_);
lean_inc(v_k_2200_);
lean_dec(v_l_2058_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2222_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v_k_2205_; lean_object* v_v_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2218_; 
v_k_2205_ = lean_ctor_get(v_r_2199_, 1);
v_v_2206_ = lean_ctor_get(v_r_2199_, 2);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_r_2199_);
if (v_isSharedCheck_2218_ == 0)
{
lean_object* v_unused_2219_; lean_object* v_unused_2220_; lean_object* v_unused_2221_; 
v_unused_2219_ = lean_ctor_get(v_r_2199_, 4);
lean_dec(v_unused_2219_);
v_unused_2220_ = lean_ctor_get(v_r_2199_, 3);
lean_dec(v_unused_2220_);
v_unused_2221_ = lean_ctor_get(v_r_2199_, 0);
lean_dec(v_unused_2221_);
v___x_2208_ = v_r_2199_;
v_isShared_2209_ = v_isSharedCheck_2218_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_v_2206_);
lean_inc(v_k_2205_);
lean_dec(v_r_2199_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2218_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2210_ = lean_unsigned_to_nat(3u);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 4, v_l_2156_);
lean_ctor_set(v___x_2208_, 3, v_l_2156_);
lean_ctor_set(v___x_2208_, 2, v_v_2201_);
lean_ctor_set(v___x_2208_, 1, v_k_2200_);
lean_ctor_set(v___x_2208_, 0, v___x_2098_);
v___x_2212_ = v___x_2208_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v_k_2200_);
lean_ctor_set(v_reuseFailAlloc_2217_, 2, v_v_2201_);
lean_ctor_set(v_reuseFailAlloc_2217_, 3, v_l_2156_);
lean_ctor_set(v_reuseFailAlloc_2217_, 4, v_l_2156_);
v___x_2212_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
lean_object* v___x_2214_; 
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 4, v_l_2156_);
lean_ctor_set(v___x_2203_, 2, v_v_2057_);
lean_ctor_set(v___x_2203_, 1, v_k_2056_);
lean_ctor_set(v___x_2203_, 0, v___x_2098_);
v___x_2214_ = v___x_2203_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_k_2056_);
lean_ctor_set(v_reuseFailAlloc_2216_, 2, v_v_2057_);
lean_ctor_set(v_reuseFailAlloc_2216_, 3, v_l_2156_);
lean_ctor_set(v_reuseFailAlloc_2216_, 4, v_l_2156_);
v___x_2214_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; 
v___x_2215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2210_);
lean_ctor_set(v___x_2215_, 1, v_k_2205_);
lean_ctor_set(v___x_2215_, 2, v_v_2206_);
lean_ctor_set(v___x_2215_, 3, v___x_2212_);
lean_ctor_set(v___x_2215_, 4, v___x_2214_);
return v___x_2215_;
}
}
}
}
}
else
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_unsigned_to_nat(2u);
v___x_2227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set(v___x_2227_, 1, v_k_2056_);
lean_ctor_set(v___x_2227_, 2, v_v_2057_);
lean_ctor_set(v___x_2227_, 3, v_l_2058_);
lean_ctor_set(v___x_2227_, 4, v_r_2199_);
return v___x_2227_;
}
}
}
else
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2098_);
lean_ctor_set(v___x_2228_, 1, v_k_2056_);
lean_ctor_set(v___x_2228_, 2, v_v_2057_);
lean_ctor_set(v___x_2228_, 3, v_l_2058_);
lean_ctor_set(v___x_2228_, 4, v_l_2058_);
return v___x_2228_;
}
}
}
v___jp_2229_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = lean_nat_add(v___y_2239_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec(v___y_2239_);
v___x_2244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
lean_ctor_set(v___x_2244_, 1, v_k_2056_);
lean_ctor_set(v___x_2244_, 2, v_v_2057_);
lean_ctor_set(v___x_2244_, 3, v___y_2238_);
lean_ctor_set(v___x_2244_, 4, v___y_2237_);
v___x_2245_ = lean_nat_add(v___y_2231_, v___y_2240_);
lean_dec(v___y_2240_);
if (lean_obj_tag(v___y_2235_) == 0)
{
lean_object* v_size_2246_; 
v_size_2246_ = lean_ctor_get(v___y_2235_, 0);
lean_inc(v_size_2246_);
v___y_2043_ = v___y_2230_;
v___y_2044_ = v___x_2245_;
v___y_2045_ = v___y_2234_;
v___y_2046_ = v___y_2233_;
v___y_2047_ = v___y_2232_;
v___y_2048_ = v___y_2235_;
v___y_2049_ = v___x_2244_;
v___y_2050_ = v___y_2236_;
v___y_2051_ = v___y_2241_;
v___y_2052_ = v_size_2246_;
goto v___jp_2042_;
}
else
{
lean_object* v___x_2247_; 
v___x_2247_ = lean_unsigned_to_nat(0u);
v___y_2043_ = v___y_2230_;
v___y_2044_ = v___x_2245_;
v___y_2045_ = v___y_2234_;
v___y_2046_ = v___y_2233_;
v___y_2047_ = v___y_2232_;
v___y_2048_ = v___y_2235_;
v___y_2049_ = v___x_2244_;
v___y_2050_ = v___y_2236_;
v___y_2051_ = v___y_2241_;
v___y_2052_ = v___x_2247_;
goto v___jp_2042_;
}
}
v___jp_2248_:
{
lean_object* v_impl_2249_; lean_object* v___x_2250_; 
v_impl_2249_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v_k_2040_, v_l_2058_);
v___x_2250_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2249_) == 0)
{
if (lean_obj_tag(v_r_2059_) == 0)
{
lean_object* v_size_2251_; lean_object* v_size_2252_; lean_object* v_k_2253_; lean_object* v_v_2254_; lean_object* v_l_2255_; lean_object* v_r_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; 
v_size_2251_ = lean_ctor_get(v_impl_2249_, 0);
lean_inc(v_size_2251_);
v_size_2252_ = lean_ctor_get(v_r_2059_, 0);
v_k_2253_ = lean_ctor_get(v_r_2059_, 1);
v_v_2254_ = lean_ctor_get(v_r_2059_, 2);
v_l_2255_ = lean_ctor_get(v_r_2059_, 3);
v_r_2256_ = lean_ctor_get(v_r_2059_, 4);
v___x_2257_ = lean_unsigned_to_nat(3u);
v___x_2258_ = lean_nat_mul(v___x_2257_, v_size_2251_);
v___x_2259_ = lean_nat_dec_lt(v___x_2258_, v_size_2252_);
lean_dec(v___x_2258_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = lean_nat_add(v___x_2250_, v_size_2251_);
lean_dec(v_size_2251_);
v___x_2261_ = lean_nat_add(v___x_2260_, v_size_2252_);
lean_dec(v___x_2260_);
v___x_2262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
lean_ctor_set(v___x_2262_, 1, v_k_2056_);
lean_ctor_set(v___x_2262_, 2, v_v_2057_);
lean_ctor_set(v___x_2262_, 3, v_impl_2249_);
lean_ctor_set(v___x_2262_, 4, v_r_2059_);
return v___x_2262_;
}
else
{
lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2297_; 
lean_inc(v_r_2256_);
lean_inc(v_l_2255_);
lean_inc(v_v_2254_);
lean_inc(v_k_2253_);
lean_inc(v_size_2252_);
v_isSharedCheck_2297_ = !lean_is_exclusive(v_r_2059_);
if (v_isSharedCheck_2297_ == 0)
{
lean_object* v_unused_2298_; lean_object* v_unused_2299_; lean_object* v_unused_2300_; lean_object* v_unused_2301_; lean_object* v_unused_2302_; 
v_unused_2298_ = lean_ctor_get(v_r_2059_, 4);
lean_dec(v_unused_2298_);
v_unused_2299_ = lean_ctor_get(v_r_2059_, 3);
lean_dec(v_unused_2299_);
v_unused_2300_ = lean_ctor_get(v_r_2059_, 2);
lean_dec(v_unused_2300_);
v_unused_2301_ = lean_ctor_get(v_r_2059_, 1);
lean_dec(v_unused_2301_);
v_unused_2302_ = lean_ctor_get(v_r_2059_, 0);
lean_dec(v_unused_2302_);
v___x_2264_ = v_r_2059_;
v_isShared_2265_ = v_isSharedCheck_2297_;
goto v_resetjp_2263_;
}
else
{
lean_dec(v_r_2059_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2297_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v_size_2266_; lean_object* v_k_2267_; lean_object* v_v_2268_; lean_object* v_l_2269_; lean_object* v_r_2270_; lean_object* v_size_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v_size_2266_ = lean_ctor_get(v_l_2255_, 0);
v_k_2267_ = lean_ctor_get(v_l_2255_, 1);
v_v_2268_ = lean_ctor_get(v_l_2255_, 2);
v_l_2269_ = lean_ctor_get(v_l_2255_, 3);
v_r_2270_ = lean_ctor_get(v_l_2255_, 4);
v_size_2271_ = lean_ctor_get(v_r_2256_, 0);
v___x_2272_ = lean_unsigned_to_nat(2u);
v___x_2273_ = lean_nat_mul(v___x_2272_, v_size_2271_);
v___x_2274_ = lean_nat_dec_lt(v_size_2266_, v___x_2273_);
lean_dec(v___x_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
lean_inc(v_size_2271_);
lean_inc(v_r_2270_);
lean_inc(v_l_2269_);
lean_inc(v_v_2268_);
lean_inc(v_k_2267_);
lean_del_object(v___x_2264_);
lean_dec(v_l_2255_);
v___x_2275_ = lean_nat_add(v___x_2250_, v_size_2251_);
lean_dec(v_size_2251_);
v___x_2276_ = lean_nat_add(v___x_2275_, v_size_2252_);
lean_dec(v_size_2252_);
if (lean_obj_tag(v_l_2269_) == 0)
{
lean_object* v_size_2277_; 
v_size_2277_ = lean_ctor_get(v_l_2269_, 0);
lean_inc(v_size_2277_);
v___y_2230_ = v_v_2268_;
v___y_2231_ = v___x_2250_;
v___y_2232_ = v_k_2253_;
v___y_2233_ = v_r_2256_;
v___y_2234_ = v___x_2276_;
v___y_2235_ = v_r_2270_;
v___y_2236_ = v_k_2267_;
v___y_2237_ = v_l_2269_;
v___y_2238_ = v_impl_2249_;
v___y_2239_ = v___x_2275_;
v___y_2240_ = v_size_2271_;
v___y_2241_ = v_v_2254_;
v___y_2242_ = v_size_2277_;
goto v___jp_2229_;
}
else
{
lean_object* v___x_2278_; 
v___x_2278_ = lean_unsigned_to_nat(0u);
v___y_2230_ = v_v_2268_;
v___y_2231_ = v___x_2250_;
v___y_2232_ = v_k_2253_;
v___y_2233_ = v_r_2256_;
v___y_2234_ = v___x_2276_;
v___y_2235_ = v_r_2270_;
v___y_2236_ = v_k_2267_;
v___y_2237_ = v_l_2269_;
v___y_2238_ = v_impl_2249_;
v___y_2239_ = v___x_2275_;
v___y_2240_ = v_size_2271_;
v___y_2241_ = v_v_2254_;
v___y_2242_ = v___x_2278_;
goto v___jp_2229_;
}
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2279_ = lean_nat_add(v___x_2250_, v_size_2251_);
lean_dec(v_size_2251_);
v___x_2280_ = lean_nat_add(v___x_2279_, v_size_2252_);
lean_dec(v_size_2252_);
v___x_2281_ = lean_nat_add(v___x_2279_, v_size_2266_);
lean_dec(v___x_2279_);
lean_inc_ref(v_impl_2249_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 4, v_l_2255_);
lean_ctor_set(v___x_2264_, 3, v_impl_2249_);
lean_ctor_set(v___x_2264_, 2, v_v_2057_);
lean_ctor_set(v___x_2264_, 1, v_k_2056_);
lean_ctor_set(v___x_2264_, 0, v___x_2281_);
v___x_2283_ = v___x_2264_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2281_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v_k_2056_);
lean_ctor_set(v_reuseFailAlloc_2296_, 2, v_v_2057_);
lean_ctor_set(v_reuseFailAlloc_2296_, 3, v_impl_2249_);
lean_ctor_set(v_reuseFailAlloc_2296_, 4, v_l_2255_);
v___x_2283_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
v_isSharedCheck_2290_ = !lean_is_exclusive(v_impl_2249_);
if (v_isSharedCheck_2290_ == 0)
{
lean_object* v_unused_2291_; lean_object* v_unused_2292_; lean_object* v_unused_2293_; lean_object* v_unused_2294_; lean_object* v_unused_2295_; 
v_unused_2291_ = lean_ctor_get(v_impl_2249_, 4);
lean_dec(v_unused_2291_);
v_unused_2292_ = lean_ctor_get(v_impl_2249_, 3);
lean_dec(v_unused_2292_);
v_unused_2293_ = lean_ctor_get(v_impl_2249_, 2);
lean_dec(v_unused_2293_);
v_unused_2294_ = lean_ctor_get(v_impl_2249_, 1);
lean_dec(v_unused_2294_);
v_unused_2295_ = lean_ctor_get(v_impl_2249_, 0);
lean_dec(v_unused_2295_);
v___x_2285_ = v_impl_2249_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_dec(v_impl_2249_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 4, v_r_2256_);
lean_ctor_set(v___x_2285_, 3, v___x_2283_);
lean_ctor_set(v___x_2285_, 2, v_v_2254_);
lean_ctor_set(v___x_2285_, 1, v_k_2253_);
lean_ctor_set(v___x_2285_, 0, v___x_2280_);
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v_k_2253_);
lean_ctor_set(v_reuseFailAlloc_2289_, 2, v_v_2254_);
lean_ctor_set(v_reuseFailAlloc_2289_, 3, v___x_2283_);
lean_ctor_set(v_reuseFailAlloc_2289_, 4, v_r_2256_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_size_2303_ = lean_ctor_get(v_impl_2249_, 0);
lean_inc(v_size_2303_);
v___x_2304_ = lean_nat_add(v___x_2250_, v_size_2303_);
lean_dec(v_size_2303_);
v___x_2305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
lean_ctor_set(v___x_2305_, 1, v_k_2056_);
lean_ctor_set(v___x_2305_, 2, v_v_2057_);
lean_ctor_set(v___x_2305_, 3, v_impl_2249_);
lean_ctor_set(v___x_2305_, 4, v_r_2059_);
return v___x_2305_;
}
}
else
{
if (lean_obj_tag(v_r_2059_) == 0)
{
lean_object* v_l_2306_; 
v_l_2306_ = lean_ctor_get(v_r_2059_, 3);
lean_inc(v_l_2306_);
if (lean_obj_tag(v_l_2306_) == 0)
{
lean_object* v_r_2307_; 
v_r_2307_ = lean_ctor_get(v_r_2059_, 4);
lean_inc(v_r_2307_);
if (lean_obj_tag(v_r_2307_) == 0)
{
lean_object* v_size_2308_; lean_object* v_k_2309_; lean_object* v_v_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2321_; 
v_size_2308_ = lean_ctor_get(v_r_2059_, 0);
v_k_2309_ = lean_ctor_get(v_r_2059_, 1);
v_v_2310_ = lean_ctor_get(v_r_2059_, 2);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_r_2059_);
if (v_isSharedCheck_2321_ == 0)
{
lean_object* v_unused_2322_; lean_object* v_unused_2323_; 
v_unused_2322_ = lean_ctor_get(v_r_2059_, 4);
lean_dec(v_unused_2322_);
v_unused_2323_ = lean_ctor_get(v_r_2059_, 3);
lean_dec(v_unused_2323_);
v___x_2312_ = v_r_2059_;
v_isShared_2313_ = v_isSharedCheck_2321_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_v_2310_);
lean_inc(v_k_2309_);
lean_inc(v_size_2308_);
lean_dec(v_r_2059_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2321_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v_size_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
v_size_2314_ = lean_ctor_get(v_l_2306_, 0);
v___x_2315_ = lean_nat_add(v___x_2250_, v_size_2308_);
lean_dec(v_size_2308_);
v___x_2316_ = lean_nat_add(v___x_2250_, v_size_2314_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 4, v_l_2306_);
lean_ctor_set(v___x_2312_, 3, v_impl_2249_);
lean_ctor_set(v___x_2312_, 2, v_v_2057_);
lean_ctor_set(v___x_2312_, 1, v_k_2056_);
lean_ctor_set(v___x_2312_, 0, v___x_2316_);
v___x_2318_ = v___x_2312_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2316_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_k_2056_);
lean_ctor_set(v_reuseFailAlloc_2320_, 2, v_v_2057_);
lean_ctor_set(v_reuseFailAlloc_2320_, 3, v_impl_2249_);
lean_ctor_set(v_reuseFailAlloc_2320_, 4, v_l_2306_);
v___x_2318_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2319_; 
v___x_2319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2315_);
lean_ctor_set(v___x_2319_, 1, v_k_2309_);
lean_ctor_set(v___x_2319_, 2, v_v_2310_);
lean_ctor_set(v___x_2319_, 3, v___x_2318_);
lean_ctor_set(v___x_2319_, 4, v_r_2307_);
return v___x_2319_;
}
}
}
else
{
lean_object* v_k_2324_; lean_object* v_v_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2346_; 
v_k_2324_ = lean_ctor_get(v_r_2059_, 1);
v_v_2325_ = lean_ctor_get(v_r_2059_, 2);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_r_2059_);
if (v_isSharedCheck_2346_ == 0)
{
lean_object* v_unused_2347_; lean_object* v_unused_2348_; lean_object* v_unused_2349_; 
v_unused_2347_ = lean_ctor_get(v_r_2059_, 4);
lean_dec(v_unused_2347_);
v_unused_2348_ = lean_ctor_get(v_r_2059_, 3);
lean_dec(v_unused_2348_);
v_unused_2349_ = lean_ctor_get(v_r_2059_, 0);
lean_dec(v_unused_2349_);
v___x_2327_ = v_r_2059_;
v_isShared_2328_ = v_isSharedCheck_2346_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_v_2325_);
lean_inc(v_k_2324_);
lean_dec(v_r_2059_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2346_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v_k_2329_; lean_object* v_v_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2342_; 
v_k_2329_ = lean_ctor_get(v_l_2306_, 1);
v_v_2330_ = lean_ctor_get(v_l_2306_, 2);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_l_2306_);
if (v_isSharedCheck_2342_ == 0)
{
lean_object* v_unused_2343_; lean_object* v_unused_2344_; lean_object* v_unused_2345_; 
v_unused_2343_ = lean_ctor_get(v_l_2306_, 4);
lean_dec(v_unused_2343_);
v_unused_2344_ = lean_ctor_get(v_l_2306_, 3);
lean_dec(v_unused_2344_);
v_unused_2345_ = lean_ctor_get(v_l_2306_, 0);
lean_dec(v_unused_2345_);
v___x_2332_ = v_l_2306_;
v_isShared_2333_ = v_isSharedCheck_2342_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_v_2330_);
lean_inc(v_k_2329_);
lean_dec(v_l_2306_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2342_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2334_ = lean_unsigned_to_nat(3u);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 4, v_r_2307_);
lean_ctor_set(v___x_2332_, 3, v_r_2307_);
lean_ctor_set(v___x_2332_, 2, v_v_2057_);
lean_ctor_set(v___x_2332_, 1, v_k_2056_);
lean_ctor_set(v___x_2332_, 0, v___x_2250_);
v___x_2336_ = v___x_2332_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2250_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_k_2056_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v_v_2057_);
lean_ctor_set(v_reuseFailAlloc_2341_, 3, v_r_2307_);
lean_ctor_set(v_reuseFailAlloc_2341_, 4, v_r_2307_);
v___x_2336_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2338_; 
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 3, v_r_2307_);
lean_ctor_set(v___x_2327_, 0, v___x_2250_);
v___x_2338_ = v___x_2327_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2250_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_k_2324_);
lean_ctor_set(v_reuseFailAlloc_2340_, 2, v_v_2325_);
lean_ctor_set(v_reuseFailAlloc_2340_, 3, v_r_2307_);
lean_ctor_set(v_reuseFailAlloc_2340_, 4, v_r_2307_);
v___x_2338_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
lean_object* v___x_2339_; 
v___x_2339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2334_);
lean_ctor_set(v___x_2339_, 1, v_k_2329_);
lean_ctor_set(v___x_2339_, 2, v_v_2330_);
lean_ctor_set(v___x_2339_, 3, v___x_2336_);
lean_ctor_set(v___x_2339_, 4, v___x_2338_);
return v___x_2339_;
}
}
}
}
}
}
else
{
lean_object* v_r_2350_; 
v_r_2350_ = lean_ctor_get(v_r_2059_, 4);
lean_inc(v_r_2350_);
if (lean_obj_tag(v_r_2350_) == 0)
{
lean_object* v_k_2351_; lean_object* v_v_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2361_; 
v_k_2351_ = lean_ctor_get(v_r_2059_, 1);
v_v_2352_ = lean_ctor_get(v_r_2059_, 2);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_r_2059_);
if (v_isSharedCheck_2361_ == 0)
{
lean_object* v_unused_2362_; lean_object* v_unused_2363_; lean_object* v_unused_2364_; 
v_unused_2362_ = lean_ctor_get(v_r_2059_, 4);
lean_dec(v_unused_2362_);
v_unused_2363_ = lean_ctor_get(v_r_2059_, 3);
lean_dec(v_unused_2363_);
v_unused_2364_ = lean_ctor_get(v_r_2059_, 0);
lean_dec(v_unused_2364_);
v___x_2354_ = v_r_2059_;
v_isShared_2355_ = v_isSharedCheck_2361_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_v_2352_);
lean_inc(v_k_2351_);
lean_dec(v_r_2059_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2361_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2358_; 
v___x_2356_ = lean_unsigned_to_nat(3u);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 4, v_l_2306_);
lean_ctor_set(v___x_2354_, 2, v_v_2057_);
lean_ctor_set(v___x_2354_, 1, v_k_2056_);
lean_ctor_set(v___x_2354_, 0, v___x_2250_);
v___x_2358_ = v___x_2354_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2250_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_k_2056_);
lean_ctor_set(v_reuseFailAlloc_2360_, 2, v_v_2057_);
lean_ctor_set(v_reuseFailAlloc_2360_, 3, v_l_2306_);
lean_ctor_set(v_reuseFailAlloc_2360_, 4, v_l_2306_);
v___x_2358_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2359_; 
v___x_2359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2356_);
lean_ctor_set(v___x_2359_, 1, v_k_2351_);
lean_ctor_set(v___x_2359_, 2, v_v_2352_);
lean_ctor_set(v___x_2359_, 3, v___x_2358_);
lean_ctor_set(v___x_2359_, 4, v_r_2350_);
return v___x_2359_;
}
}
}
else
{
lean_object* v_size_2365_; lean_object* v_k_2366_; lean_object* v_v_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2376_; 
v_size_2365_ = lean_ctor_get(v_r_2059_, 0);
v_k_2366_ = lean_ctor_get(v_r_2059_, 1);
v_v_2367_ = lean_ctor_get(v_r_2059_, 2);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_r_2059_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; lean_object* v_unused_2378_; 
v_unused_2377_ = lean_ctor_get(v_r_2059_, 4);
lean_dec(v_unused_2377_);
v_unused_2378_ = lean_ctor_get(v_r_2059_, 3);
lean_dec(v_unused_2378_);
v___x_2369_ = v_r_2059_;
v_isShared_2370_ = v_isSharedCheck_2376_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_v_2367_);
lean_inc(v_k_2366_);
lean_inc(v_size_2365_);
lean_dec(v_r_2059_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2376_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 3, v_r_2350_);
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_size_2365_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v_k_2366_);
lean_ctor_set(v_reuseFailAlloc_2375_, 2, v_v_2367_);
lean_ctor_set(v_reuseFailAlloc_2375_, 3, v_r_2350_);
lean_ctor_set(v_reuseFailAlloc_2375_, 4, v_r_2350_);
v___x_2372_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_unsigned_to_nat(2u);
v___x_2374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
lean_ctor_set(v___x_2374_, 1, v_k_2056_);
lean_ctor_set(v___x_2374_, 2, v_v_2057_);
lean_ctor_set(v___x_2374_, 3, v_r_2350_);
lean_ctor_set(v___x_2374_, 4, v___x_2372_);
return v___x_2374_;
}
}
}
}
}
else
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2250_);
lean_ctor_set(v___x_2379_, 1, v_k_2056_);
lean_ctor_set(v___x_2379_, 2, v_v_2057_);
lean_ctor_set(v___x_2379_, 3, v_r_2059_);
lean_ctor_set(v___x_2379_, 4, v_r_2059_);
return v___x_2379_;
}
}
}
}
}
else
{
return v_t_2041_;
}
v___jp_2042_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = lean_nat_add(v___y_2044_, v___y_2052_);
lean_dec(v___y_2052_);
lean_dec(v___y_2044_);
v___x_2054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
lean_ctor_set(v___x_2054_, 1, v___y_2047_);
lean_ctor_set(v___x_2054_, 2, v___y_2051_);
lean_ctor_set(v___x_2054_, 3, v___y_2048_);
lean_ctor_set(v___x_2054_, 4, v___y_2046_);
v___x_2055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2055_, 0, v___y_2045_);
lean_ctor_set(v___x_2055_, 1, v___y_2050_);
lean_ctor_set(v___x_2055_, 2, v___y_2043_);
lean_ctor_set(v___x_2055_, 3, v___y_2049_);
lean_ctor_set(v___x_2055_, 4, v___x_2054_);
return v___x_2055_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg___boxed(lean_object* v_k_2704_, lean_object* v_t_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v_k_2704_, v_t_2705_);
lean_dec_ref(v_k_2704_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(lean_object* v_k_2707_, lean_object* v_v_2708_, lean_object* v_t_2709_){
_start:
{
lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; 
if (lean_obj_tag(v_t_2709_) == 0)
{
lean_object* v_size_2724_; lean_object* v_k_2725_; lean_object* v_v_2726_; lean_object* v_l_2727_; lean_object* v_r_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2993_; 
v_size_2724_ = lean_ctor_get(v_t_2709_, 0);
v_k_2725_ = lean_ctor_get(v_t_2709_, 1);
v_v_2726_ = lean_ctor_get(v_t_2709_, 2);
v_l_2727_ = lean_ctor_get(v_t_2709_, 3);
v_r_2728_ = lean_ctor_get(v_t_2709_, 4);
v_isSharedCheck_2993_ = !lean_is_exclusive(v_t_2709_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2730_ = v_t_2709_;
v_isShared_2731_ = v_isSharedCheck_2993_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_r_2728_);
lean_inc(v_l_2727_);
lean_inc(v_v_2726_);
lean_inc(v_k_2725_);
lean_inc(v_size_2724_);
lean_dec(v_t_2709_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2993_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v_fst_2981_; lean_object* v_snd_2982_; lean_object* v_fst_2983_; lean_object* v_snd_2984_; double v___x_2985_; double v___x_2986_; uint8_t v___x_2987_; 
v_fst_2981_ = lean_ctor_get(v_k_2707_, 0);
v_snd_2982_ = lean_ctor_get(v_k_2707_, 1);
v_fst_2983_ = lean_ctor_get(v_k_2725_, 0);
v_snd_2984_ = lean_ctor_get(v_k_2725_, 1);
v___x_2985_ = lean_unbox_float(v_fst_2981_);
v___x_2986_ = lean_unbox_float(v_fst_2983_);
v___x_2987_ = lean_float_decLt(v___x_2985_, v___x_2986_);
if (v___x_2987_ == 0)
{
double v___x_2988_; double v___x_2989_; uint8_t v___x_2990_; 
v___x_2988_ = lean_unbox_float(v_fst_2983_);
v___x_2989_ = lean_unbox_float(v_fst_2981_);
v___x_2990_ = lean_float_decLt(v___x_2988_, v___x_2989_);
if (v___x_2990_ == 0)
{
uint8_t v___x_2991_; 
v___x_2991_ = l_Lean_Name_cmp(v_snd_2982_, v_snd_2984_);
switch(v___x_2991_)
{
case 0:
{
lean_del_object(v___x_2730_);
lean_dec(v_size_2724_);
goto v___jp_2880_;
}
case 1:
{
lean_object* v___x_2992_; 
lean_del_object(v___x_2730_);
lean_dec(v_v_2726_);
lean_dec(v_k_2725_);
v___x_2992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2992_, 0, v_size_2724_);
lean_ctor_set(v___x_2992_, 1, v_k_2707_);
lean_ctor_set(v___x_2992_, 2, v_v_2708_);
lean_ctor_set(v___x_2992_, 3, v_l_2727_);
lean_ctor_set(v___x_2992_, 4, v_r_2728_);
return v___x_2992_;
}
default: 
{
lean_dec(v_size_2724_);
goto v___jp_2752_;
}
}
}
else
{
lean_dec(v_size_2724_);
goto v___jp_2752_;
}
}
else
{
lean_del_object(v___x_2730_);
lean_dec(v_size_2724_);
goto v___jp_2880_;
}
v___jp_2732_:
{
lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2745_ = lean_nat_add(v___y_2734_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec(v___y_2734_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 4, v___y_2736_);
lean_ctor_set(v___x_2730_, 0, v___x_2745_);
v___x_2747_ = v___x_2730_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2745_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_k_2725_);
lean_ctor_set(v_reuseFailAlloc_2751_, 2, v_v_2726_);
lean_ctor_set(v_reuseFailAlloc_2751_, 3, v_l_2727_);
lean_ctor_set(v_reuseFailAlloc_2751_, 4, v___y_2736_);
v___x_2747_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
lean_object* v___x_2748_; 
v___x_2748_ = lean_nat_add(v___y_2740_, v___y_2733_);
lean_dec(v___y_2733_);
if (lean_obj_tag(v___y_2739_) == 0)
{
lean_object* v_size_2749_; 
v_size_2749_ = lean_ctor_get(v___y_2739_, 0);
lean_inc(v_size_2749_);
v___y_2711_ = v___x_2747_;
v___y_2712_ = v___y_2735_;
v___y_2713_ = v___y_2738_;
v___y_2714_ = v___y_2737_;
v___y_2715_ = v___y_2739_;
v___y_2716_ = v___x_2748_;
v___y_2717_ = v___y_2741_;
v___y_2718_ = v___y_2742_;
v___y_2719_ = v___y_2743_;
v___y_2720_ = v_size_2749_;
goto v___jp_2710_;
}
else
{
lean_object* v___x_2750_; 
v___x_2750_ = lean_unsigned_to_nat(0u);
v___y_2711_ = v___x_2747_;
v___y_2712_ = v___y_2735_;
v___y_2713_ = v___y_2738_;
v___y_2714_ = v___y_2737_;
v___y_2715_ = v___y_2739_;
v___y_2716_ = v___x_2748_;
v___y_2717_ = v___y_2741_;
v___y_2718_ = v___y_2742_;
v___y_2719_ = v___y_2743_;
v___y_2720_ = v___x_2750_;
goto v___jp_2710_;
}
}
}
v___jp_2752_:
{
lean_object* v_impl_2753_; lean_object* v___x_2754_; 
v_impl_2753_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(v_k_2707_, v_v_2708_, v_r_2728_);
v___x_2754_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2727_) == 0)
{
lean_object* v_size_2755_; lean_object* v_size_2756_; lean_object* v_k_2757_; lean_object* v_v_2758_; lean_object* v_l_2759_; lean_object* v_r_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; uint8_t v___x_2763_; 
v_size_2755_ = lean_ctor_get(v_l_2727_, 0);
v_size_2756_ = lean_ctor_get(v_impl_2753_, 0);
lean_inc(v_size_2756_);
v_k_2757_ = lean_ctor_get(v_impl_2753_, 1);
lean_inc(v_k_2757_);
v_v_2758_ = lean_ctor_get(v_impl_2753_, 2);
lean_inc(v_v_2758_);
v_l_2759_ = lean_ctor_get(v_impl_2753_, 3);
lean_inc(v_l_2759_);
v_r_2760_ = lean_ctor_get(v_impl_2753_, 4);
lean_inc(v_r_2760_);
v___x_2761_ = lean_unsigned_to_nat(3u);
v___x_2762_ = lean_nat_mul(v___x_2761_, v_size_2755_);
v___x_2763_ = lean_nat_dec_lt(v___x_2762_, v_size_2756_);
lean_dec(v___x_2762_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
lean_dec(v_r_2760_);
lean_dec(v_l_2759_);
lean_dec(v_v_2758_);
lean_dec(v_k_2757_);
lean_del_object(v___x_2730_);
v___x_2764_ = lean_nat_add(v___x_2754_, v_size_2755_);
v___x_2765_ = lean_nat_add(v___x_2764_, v_size_2756_);
lean_dec(v_size_2756_);
lean_dec(v___x_2764_);
v___x_2766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
lean_ctor_set(v___x_2766_, 1, v_k_2725_);
lean_ctor_set(v___x_2766_, 2, v_v_2726_);
lean_ctor_set(v___x_2766_, 3, v_l_2727_);
lean_ctor_set(v___x_2766_, 4, v_impl_2753_);
return v___x_2766_;
}
else
{
lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2801_; 
v_isSharedCheck_2801_ = !lean_is_exclusive(v_impl_2753_);
if (v_isSharedCheck_2801_ == 0)
{
lean_object* v_unused_2802_; lean_object* v_unused_2803_; lean_object* v_unused_2804_; lean_object* v_unused_2805_; lean_object* v_unused_2806_; 
v_unused_2802_ = lean_ctor_get(v_impl_2753_, 4);
lean_dec(v_unused_2802_);
v_unused_2803_ = lean_ctor_get(v_impl_2753_, 3);
lean_dec(v_unused_2803_);
v_unused_2804_ = lean_ctor_get(v_impl_2753_, 2);
lean_dec(v_unused_2804_);
v_unused_2805_ = lean_ctor_get(v_impl_2753_, 1);
lean_dec(v_unused_2805_);
v_unused_2806_ = lean_ctor_get(v_impl_2753_, 0);
lean_dec(v_unused_2806_);
v___x_2768_ = v_impl_2753_;
v_isShared_2769_ = v_isSharedCheck_2801_;
goto v_resetjp_2767_;
}
else
{
lean_dec(v_impl_2753_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2801_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v_size_2770_; lean_object* v_k_2771_; lean_object* v_v_2772_; lean_object* v_l_2773_; lean_object* v_r_2774_; lean_object* v_size_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; 
v_size_2770_ = lean_ctor_get(v_l_2759_, 0);
v_k_2771_ = lean_ctor_get(v_l_2759_, 1);
v_v_2772_ = lean_ctor_get(v_l_2759_, 2);
v_l_2773_ = lean_ctor_get(v_l_2759_, 3);
v_r_2774_ = lean_ctor_get(v_l_2759_, 4);
v_size_2775_ = lean_ctor_get(v_r_2760_, 0);
v___x_2776_ = lean_unsigned_to_nat(2u);
v___x_2777_ = lean_nat_mul(v___x_2776_, v_size_2775_);
v___x_2778_ = lean_nat_dec_lt(v_size_2770_, v___x_2777_);
lean_dec(v___x_2777_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
lean_inc(v_size_2775_);
lean_inc(v_r_2774_);
lean_inc(v_l_2773_);
lean_inc(v_v_2772_);
lean_inc(v_k_2771_);
lean_del_object(v___x_2768_);
lean_dec(v_l_2759_);
v___x_2779_ = lean_nat_add(v___x_2754_, v_size_2755_);
v___x_2780_ = lean_nat_add(v___x_2779_, v_size_2756_);
lean_dec(v_size_2756_);
if (lean_obj_tag(v_l_2773_) == 0)
{
lean_object* v_size_2781_; 
v_size_2781_ = lean_ctor_get(v_l_2773_, 0);
lean_inc(v_size_2781_);
v___y_2733_ = v_size_2775_;
v___y_2734_ = v___x_2779_;
v___y_2735_ = v_k_2771_;
v___y_2736_ = v_l_2773_;
v___y_2737_ = v_r_2760_;
v___y_2738_ = v___x_2780_;
v___y_2739_ = v_r_2774_;
v___y_2740_ = v___x_2754_;
v___y_2741_ = v_v_2772_;
v___y_2742_ = v_v_2758_;
v___y_2743_ = v_k_2757_;
v___y_2744_ = v_size_2781_;
goto v___jp_2732_;
}
else
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_unsigned_to_nat(0u);
v___y_2733_ = v_size_2775_;
v___y_2734_ = v___x_2779_;
v___y_2735_ = v_k_2771_;
v___y_2736_ = v_l_2773_;
v___y_2737_ = v_r_2760_;
v___y_2738_ = v___x_2780_;
v___y_2739_ = v_r_2774_;
v___y_2740_ = v___x_2754_;
v___y_2741_ = v_v_2772_;
v___y_2742_ = v_v_2758_;
v___y_2743_ = v_k_2757_;
v___y_2744_ = v___x_2782_;
goto v___jp_2732_;
}
}
else
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
lean_del_object(v___x_2730_);
v___x_2783_ = lean_nat_add(v___x_2754_, v_size_2755_);
v___x_2784_ = lean_nat_add(v___x_2783_, v_size_2756_);
lean_dec(v_size_2756_);
v___x_2785_ = lean_nat_add(v___x_2783_, v_size_2770_);
lean_dec(v___x_2783_);
lean_inc_ref(v_l_2727_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 4, v_l_2759_);
lean_ctor_set(v___x_2768_, 3, v_l_2727_);
lean_ctor_set(v___x_2768_, 2, v_v_2726_);
lean_ctor_set(v___x_2768_, 1, v_k_2725_);
lean_ctor_set(v___x_2768_, 0, v___x_2785_);
v___x_2787_ = v___x_2768_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v_k_2725_);
lean_ctor_set(v_reuseFailAlloc_2800_, 2, v_v_2726_);
lean_ctor_set(v_reuseFailAlloc_2800_, 3, v_l_2727_);
lean_ctor_set(v_reuseFailAlloc_2800_, 4, v_l_2759_);
v___x_2787_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
v_isSharedCheck_2794_ = !lean_is_exclusive(v_l_2727_);
if (v_isSharedCheck_2794_ == 0)
{
lean_object* v_unused_2795_; lean_object* v_unused_2796_; lean_object* v_unused_2797_; lean_object* v_unused_2798_; lean_object* v_unused_2799_; 
v_unused_2795_ = lean_ctor_get(v_l_2727_, 4);
lean_dec(v_unused_2795_);
v_unused_2796_ = lean_ctor_get(v_l_2727_, 3);
lean_dec(v_unused_2796_);
v_unused_2797_ = lean_ctor_get(v_l_2727_, 2);
lean_dec(v_unused_2797_);
v_unused_2798_ = lean_ctor_get(v_l_2727_, 1);
lean_dec(v_unused_2798_);
v_unused_2799_ = lean_ctor_get(v_l_2727_, 0);
lean_dec(v_unused_2799_);
v___x_2789_ = v_l_2727_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_dec(v_l_2727_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 4, v_r_2760_);
lean_ctor_set(v___x_2789_, 3, v___x_2787_);
lean_ctor_set(v___x_2789_, 2, v_v_2758_);
lean_ctor_set(v___x_2789_, 1, v_k_2757_);
lean_ctor_set(v___x_2789_, 0, v___x_2784_);
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v_k_2757_);
lean_ctor_set(v_reuseFailAlloc_2793_, 2, v_v_2758_);
lean_ctor_set(v_reuseFailAlloc_2793_, 3, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2793_, 4, v_r_2760_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2807_; 
lean_del_object(v___x_2730_);
v_l_2807_ = lean_ctor_get(v_impl_2753_, 3);
lean_inc(v_l_2807_);
if (lean_obj_tag(v_l_2807_) == 0)
{
lean_object* v_r_2808_; lean_object* v_k_2809_; lean_object* v_v_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2831_; 
v_r_2808_ = lean_ctor_get(v_impl_2753_, 4);
v_k_2809_ = lean_ctor_get(v_impl_2753_, 1);
v_v_2810_ = lean_ctor_get(v_impl_2753_, 2);
v_isSharedCheck_2831_ = !lean_is_exclusive(v_impl_2753_);
if (v_isSharedCheck_2831_ == 0)
{
lean_object* v_unused_2832_; lean_object* v_unused_2833_; 
v_unused_2832_ = lean_ctor_get(v_impl_2753_, 3);
lean_dec(v_unused_2832_);
v_unused_2833_ = lean_ctor_get(v_impl_2753_, 0);
lean_dec(v_unused_2833_);
v___x_2812_ = v_impl_2753_;
v_isShared_2813_ = v_isSharedCheck_2831_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_r_2808_);
lean_inc(v_v_2810_);
lean_inc(v_k_2809_);
lean_dec(v_impl_2753_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2831_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v_k_2814_; lean_object* v_v_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2827_; 
v_k_2814_ = lean_ctor_get(v_l_2807_, 1);
v_v_2815_ = lean_ctor_get(v_l_2807_, 2);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_l_2807_);
if (v_isSharedCheck_2827_ == 0)
{
lean_object* v_unused_2828_; lean_object* v_unused_2829_; lean_object* v_unused_2830_; 
v_unused_2828_ = lean_ctor_get(v_l_2807_, 4);
lean_dec(v_unused_2828_);
v_unused_2829_ = lean_ctor_get(v_l_2807_, 3);
lean_dec(v_unused_2829_);
v_unused_2830_ = lean_ctor_get(v_l_2807_, 0);
lean_dec(v_unused_2830_);
v___x_2817_ = v_l_2807_;
v_isShared_2818_ = v_isSharedCheck_2827_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_v_2815_);
lean_inc(v_k_2814_);
lean_dec(v_l_2807_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2827_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2819_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2808_, 2);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 4, v_r_2808_);
lean_ctor_set(v___x_2817_, 3, v_r_2808_);
lean_ctor_set(v___x_2817_, 2, v_v_2726_);
lean_ctor_set(v___x_2817_, 1, v_k_2725_);
lean_ctor_set(v___x_2817_, 0, v___x_2754_);
v___x_2821_ = v___x_2817_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2754_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_k_2725_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_v_2726_);
lean_ctor_set(v_reuseFailAlloc_2826_, 3, v_r_2808_);
lean_ctor_set(v_reuseFailAlloc_2826_, 4, v_r_2808_);
v___x_2821_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2823_; 
lean_inc(v_r_2808_);
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 3, v_r_2808_);
lean_ctor_set(v___x_2812_, 0, v___x_2754_);
v___x_2823_ = v___x_2812_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2754_);
lean_ctor_set(v_reuseFailAlloc_2825_, 1, v_k_2809_);
lean_ctor_set(v_reuseFailAlloc_2825_, 2, v_v_2810_);
lean_ctor_set(v_reuseFailAlloc_2825_, 3, v_r_2808_);
lean_ctor_set(v_reuseFailAlloc_2825_, 4, v_r_2808_);
v___x_2823_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2824_; 
v___x_2824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2819_);
lean_ctor_set(v___x_2824_, 1, v_k_2814_);
lean_ctor_set(v___x_2824_, 2, v_v_2815_);
lean_ctor_set(v___x_2824_, 3, v___x_2821_);
lean_ctor_set(v___x_2824_, 4, v___x_2823_);
return v___x_2824_;
}
}
}
}
}
else
{
lean_object* v_r_2834_; 
v_r_2834_ = lean_ctor_get(v_impl_2753_, 4);
lean_inc(v_r_2834_);
if (lean_obj_tag(v_r_2834_) == 0)
{
lean_object* v_k_2835_; lean_object* v_v_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2845_; 
v_k_2835_ = lean_ctor_get(v_impl_2753_, 1);
v_v_2836_ = lean_ctor_get(v_impl_2753_, 2);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_impl_2753_);
if (v_isSharedCheck_2845_ == 0)
{
lean_object* v_unused_2846_; lean_object* v_unused_2847_; lean_object* v_unused_2848_; 
v_unused_2846_ = lean_ctor_get(v_impl_2753_, 4);
lean_dec(v_unused_2846_);
v_unused_2847_ = lean_ctor_get(v_impl_2753_, 3);
lean_dec(v_unused_2847_);
v_unused_2848_ = lean_ctor_get(v_impl_2753_, 0);
lean_dec(v_unused_2848_);
v___x_2838_ = v_impl_2753_;
v_isShared_2839_ = v_isSharedCheck_2845_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_v_2836_);
lean_inc(v_k_2835_);
lean_dec(v_impl_2753_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2845_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2840_; lean_object* v___x_2842_; 
v___x_2840_ = lean_unsigned_to_nat(3u);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 4, v_l_2807_);
lean_ctor_set(v___x_2838_, 2, v_v_2726_);
lean_ctor_set(v___x_2838_, 1, v_k_2725_);
lean_ctor_set(v___x_2838_, 0, v___x_2754_);
v___x_2842_ = v___x_2838_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2754_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v_k_2725_);
lean_ctor_set(v_reuseFailAlloc_2844_, 2, v_v_2726_);
lean_ctor_set(v_reuseFailAlloc_2844_, 3, v_l_2807_);
lean_ctor_set(v_reuseFailAlloc_2844_, 4, v_l_2807_);
v___x_2842_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2843_; 
v___x_2843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2840_);
lean_ctor_set(v___x_2843_, 1, v_k_2835_);
lean_ctor_set(v___x_2843_, 2, v_v_2836_);
lean_ctor_set(v___x_2843_, 3, v___x_2842_);
lean_ctor_set(v___x_2843_, 4, v_r_2834_);
return v___x_2843_;
}
}
}
else
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = lean_unsigned_to_nat(2u);
v___x_2850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
lean_ctor_set(v___x_2850_, 1, v_k_2725_);
lean_ctor_set(v___x_2850_, 2, v_v_2726_);
lean_ctor_set(v___x_2850_, 3, v_r_2834_);
lean_ctor_set(v___x_2850_, 4, v_impl_2753_);
return v___x_2850_;
}
}
}
}
v___jp_2851_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2859_ = lean_nat_add(v___y_2852_, v___y_2858_);
lean_dec(v___y_2858_);
lean_dec(v___y_2852_);
v___x_2860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
lean_ctor_set(v___x_2860_, 1, v_k_2725_);
lean_ctor_set(v___x_2860_, 2, v_v_2726_);
lean_ctor_set(v___x_2860_, 3, v___y_2855_);
lean_ctor_set(v___x_2860_, 4, v_r_2728_);
v___x_2861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2861_, 0, v___y_2854_);
lean_ctor_set(v___x_2861_, 1, v___y_2856_);
lean_ctor_set(v___x_2861_, 2, v___y_2857_);
lean_ctor_set(v___x_2861_, 3, v___y_2853_);
lean_ctor_set(v___x_2861_, 4, v___x_2860_);
return v___x_2861_;
}
v___jp_2862_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2875_ = lean_nat_add(v___y_2863_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec(v___y_2863_);
v___x_2876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
lean_ctor_set(v___x_2876_, 1, v___y_2866_);
lean_ctor_set(v___x_2876_, 2, v___y_2872_);
lean_ctor_set(v___x_2876_, 3, v___y_2871_);
lean_ctor_set(v___x_2876_, 4, v___y_2868_);
v___x_2877_ = lean_nat_add(v___y_2870_, v___y_2869_);
lean_dec(v___y_2869_);
if (lean_obj_tag(v___y_2865_) == 0)
{
lean_object* v_size_2878_; 
v_size_2878_ = lean_ctor_get(v___y_2865_, 0);
lean_inc(v_size_2878_);
v___y_2852_ = v___x_2877_;
v___y_2853_ = v___x_2876_;
v___y_2854_ = v___y_2864_;
v___y_2855_ = v___y_2865_;
v___y_2856_ = v___y_2867_;
v___y_2857_ = v___y_2873_;
v___y_2858_ = v_size_2878_;
goto v___jp_2851_;
}
else
{
lean_object* v___x_2879_; 
v___x_2879_ = lean_unsigned_to_nat(0u);
v___y_2852_ = v___x_2877_;
v___y_2853_ = v___x_2876_;
v___y_2854_ = v___y_2864_;
v___y_2855_ = v___y_2865_;
v___y_2856_ = v___y_2867_;
v___y_2857_ = v___y_2873_;
v___y_2858_ = v___x_2879_;
goto v___jp_2851_;
}
}
v___jp_2880_:
{
lean_object* v_impl_2881_; lean_object* v___x_2882_; 
v_impl_2881_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(v_k_2707_, v_v_2708_, v_l_2727_);
v___x_2882_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2728_) == 0)
{
lean_object* v_size_2883_; lean_object* v_size_2884_; lean_object* v_k_2885_; lean_object* v_v_2886_; lean_object* v_l_2887_; lean_object* v_r_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; uint8_t v___x_2891_; 
v_size_2883_ = lean_ctor_get(v_r_2728_, 0);
v_size_2884_ = lean_ctor_get(v_impl_2881_, 0);
lean_inc(v_size_2884_);
v_k_2885_ = lean_ctor_get(v_impl_2881_, 1);
lean_inc(v_k_2885_);
v_v_2886_ = lean_ctor_get(v_impl_2881_, 2);
lean_inc(v_v_2886_);
v_l_2887_ = lean_ctor_get(v_impl_2881_, 3);
lean_inc(v_l_2887_);
v_r_2888_ = lean_ctor_get(v_impl_2881_, 4);
lean_inc(v_r_2888_);
v___x_2889_ = lean_unsigned_to_nat(3u);
v___x_2890_ = lean_nat_mul(v___x_2889_, v_size_2883_);
v___x_2891_ = lean_nat_dec_lt(v___x_2890_, v_size_2884_);
lean_dec(v___x_2890_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
lean_dec(v_r_2888_);
lean_dec(v_l_2887_);
lean_dec(v_v_2886_);
lean_dec(v_k_2885_);
v___x_2892_ = lean_nat_add(v___x_2882_, v_size_2884_);
lean_dec(v_size_2884_);
v___x_2893_ = lean_nat_add(v___x_2892_, v_size_2883_);
lean_dec(v___x_2892_);
v___x_2894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
lean_ctor_set(v___x_2894_, 1, v_k_2725_);
lean_ctor_set(v___x_2894_, 2, v_v_2726_);
lean_ctor_set(v___x_2894_, 3, v_impl_2881_);
lean_ctor_set(v___x_2894_, 4, v_r_2728_);
return v___x_2894_;
}
else
{
lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2931_; 
v_isSharedCheck_2931_ = !lean_is_exclusive(v_impl_2881_);
if (v_isSharedCheck_2931_ == 0)
{
lean_object* v_unused_2932_; lean_object* v_unused_2933_; lean_object* v_unused_2934_; lean_object* v_unused_2935_; lean_object* v_unused_2936_; 
v_unused_2932_ = lean_ctor_get(v_impl_2881_, 4);
lean_dec(v_unused_2932_);
v_unused_2933_ = lean_ctor_get(v_impl_2881_, 3);
lean_dec(v_unused_2933_);
v_unused_2934_ = lean_ctor_get(v_impl_2881_, 2);
lean_dec(v_unused_2934_);
v_unused_2935_ = lean_ctor_get(v_impl_2881_, 1);
lean_dec(v_unused_2935_);
v_unused_2936_ = lean_ctor_get(v_impl_2881_, 0);
lean_dec(v_unused_2936_);
v___x_2896_ = v_impl_2881_;
v_isShared_2897_ = v_isSharedCheck_2931_;
goto v_resetjp_2895_;
}
else
{
lean_dec(v_impl_2881_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2931_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v_size_2898_; lean_object* v_size_2899_; lean_object* v_k_2900_; lean_object* v_v_2901_; lean_object* v_l_2902_; lean_object* v_r_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
v_size_2898_ = lean_ctor_get(v_l_2887_, 0);
v_size_2899_ = lean_ctor_get(v_r_2888_, 0);
v_k_2900_ = lean_ctor_get(v_r_2888_, 1);
v_v_2901_ = lean_ctor_get(v_r_2888_, 2);
v_l_2902_ = lean_ctor_get(v_r_2888_, 3);
v_r_2903_ = lean_ctor_get(v_r_2888_, 4);
v___x_2904_ = lean_unsigned_to_nat(2u);
v___x_2905_ = lean_nat_mul(v___x_2904_, v_size_2898_);
v___x_2906_ = lean_nat_dec_lt(v_size_2899_, v___x_2905_);
lean_dec(v___x_2905_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
lean_inc(v_r_2903_);
lean_inc(v_l_2902_);
lean_inc(v_v_2901_);
lean_inc(v_k_2900_);
lean_del_object(v___x_2896_);
lean_dec(v_r_2888_);
v___x_2907_ = lean_nat_add(v___x_2882_, v_size_2884_);
lean_dec(v_size_2884_);
v___x_2908_ = lean_nat_add(v___x_2907_, v_size_2883_);
lean_dec(v___x_2907_);
v___x_2909_ = lean_nat_add(v___x_2882_, v_size_2898_);
if (lean_obj_tag(v_l_2902_) == 0)
{
lean_object* v_size_2910_; 
v_size_2910_ = lean_ctor_get(v_l_2902_, 0);
lean_inc(v_size_2910_);
lean_inc(v_size_2883_);
v___y_2863_ = v___x_2909_;
v___y_2864_ = v___x_2908_;
v___y_2865_ = v_r_2903_;
v___y_2866_ = v_k_2885_;
v___y_2867_ = v_k_2900_;
v___y_2868_ = v_l_2902_;
v___y_2869_ = v_size_2883_;
v___y_2870_ = v___x_2882_;
v___y_2871_ = v_l_2887_;
v___y_2872_ = v_v_2886_;
v___y_2873_ = v_v_2901_;
v___y_2874_ = v_size_2910_;
goto v___jp_2862_;
}
else
{
lean_object* v___x_2911_; 
v___x_2911_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_2883_);
v___y_2863_ = v___x_2909_;
v___y_2864_ = v___x_2908_;
v___y_2865_ = v_r_2903_;
v___y_2866_ = v_k_2885_;
v___y_2867_ = v_k_2900_;
v___y_2868_ = v_l_2902_;
v___y_2869_ = v_size_2883_;
v___y_2870_ = v___x_2882_;
v___y_2871_ = v_l_2887_;
v___y_2872_ = v_v_2886_;
v___y_2873_ = v_v_2901_;
v___y_2874_ = v___x_2911_;
goto v___jp_2862_;
}
}
else
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2912_ = lean_nat_add(v___x_2882_, v_size_2884_);
lean_dec(v_size_2884_);
v___x_2913_ = lean_nat_add(v___x_2912_, v_size_2883_);
lean_dec(v___x_2912_);
v___x_2914_ = lean_nat_add(v___x_2882_, v_size_2883_);
v___x_2915_ = lean_nat_add(v___x_2914_, v_size_2899_);
lean_dec(v___x_2914_);
lean_inc_ref(v_r_2728_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 4, v_r_2728_);
lean_ctor_set(v___x_2896_, 3, v_r_2888_);
lean_ctor_set(v___x_2896_, 2, v_v_2726_);
lean_ctor_set(v___x_2896_, 1, v_k_2725_);
lean_ctor_set(v___x_2896_, 0, v___x_2915_);
v___x_2917_ = v___x_2896_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_k_2725_);
lean_ctor_set(v_reuseFailAlloc_2930_, 2, v_v_2726_);
lean_ctor_set(v_reuseFailAlloc_2930_, 3, v_r_2888_);
lean_ctor_set(v_reuseFailAlloc_2930_, 4, v_r_2728_);
v___x_2917_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
v_isSharedCheck_2924_ = !lean_is_exclusive(v_r_2728_);
if (v_isSharedCheck_2924_ == 0)
{
lean_object* v_unused_2925_; lean_object* v_unused_2926_; lean_object* v_unused_2927_; lean_object* v_unused_2928_; lean_object* v_unused_2929_; 
v_unused_2925_ = lean_ctor_get(v_r_2728_, 4);
lean_dec(v_unused_2925_);
v_unused_2926_ = lean_ctor_get(v_r_2728_, 3);
lean_dec(v_unused_2926_);
v_unused_2927_ = lean_ctor_get(v_r_2728_, 2);
lean_dec(v_unused_2927_);
v_unused_2928_ = lean_ctor_get(v_r_2728_, 1);
lean_dec(v_unused_2928_);
v_unused_2929_ = lean_ctor_get(v_r_2728_, 0);
lean_dec(v_unused_2929_);
v___x_2919_ = v_r_2728_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_dec(v_r_2728_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 4, v___x_2917_);
lean_ctor_set(v___x_2919_, 3, v_l_2887_);
lean_ctor_set(v___x_2919_, 2, v_v_2886_);
lean_ctor_set(v___x_2919_, 1, v_k_2885_);
lean_ctor_set(v___x_2919_, 0, v___x_2913_);
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2913_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v_k_2885_);
lean_ctor_set(v_reuseFailAlloc_2923_, 2, v_v_2886_);
lean_ctor_set(v_reuseFailAlloc_2923_, 3, v_l_2887_);
lean_ctor_set(v_reuseFailAlloc_2923_, 4, v___x_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2937_; 
v_l_2937_ = lean_ctor_get(v_impl_2881_, 3);
lean_inc(v_l_2937_);
if (lean_obj_tag(v_l_2937_) == 0)
{
lean_object* v_r_2938_; lean_object* v_k_2939_; lean_object* v_v_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2949_; 
v_r_2938_ = lean_ctor_get(v_impl_2881_, 4);
v_k_2939_ = lean_ctor_get(v_impl_2881_, 1);
v_v_2940_ = lean_ctor_get(v_impl_2881_, 2);
v_isSharedCheck_2949_ = !lean_is_exclusive(v_impl_2881_);
if (v_isSharedCheck_2949_ == 0)
{
lean_object* v_unused_2950_; lean_object* v_unused_2951_; 
v_unused_2950_ = lean_ctor_get(v_impl_2881_, 3);
lean_dec(v_unused_2950_);
v_unused_2951_ = lean_ctor_get(v_impl_2881_, 0);
lean_dec(v_unused_2951_);
v___x_2942_ = v_impl_2881_;
v_isShared_2943_ = v_isSharedCheck_2949_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_r_2938_);
lean_inc(v_v_2940_);
lean_inc(v_k_2939_);
lean_dec(v_impl_2881_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2949_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; lean_object* v___x_2946_; 
v___x_2944_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2938_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 3, v_r_2938_);
lean_ctor_set(v___x_2942_, 2, v_v_2726_);
lean_ctor_set(v___x_2942_, 1, v_k_2725_);
lean_ctor_set(v___x_2942_, 0, v___x_2882_);
v___x_2946_ = v___x_2942_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2882_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v_k_2725_);
lean_ctor_set(v_reuseFailAlloc_2948_, 2, v_v_2726_);
lean_ctor_set(v_reuseFailAlloc_2948_, 3, v_r_2938_);
lean_ctor_set(v_reuseFailAlloc_2948_, 4, v_r_2938_);
v___x_2946_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
lean_object* v___x_2947_; 
v___x_2947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2944_);
lean_ctor_set(v___x_2947_, 1, v_k_2939_);
lean_ctor_set(v___x_2947_, 2, v_v_2940_);
lean_ctor_set(v___x_2947_, 3, v_l_2937_);
lean_ctor_set(v___x_2947_, 4, v___x_2946_);
return v___x_2947_;
}
}
}
else
{
lean_object* v_r_2952_; 
v_r_2952_ = lean_ctor_get(v_impl_2881_, 4);
lean_inc(v_r_2952_);
if (lean_obj_tag(v_r_2952_) == 0)
{
lean_object* v_k_2953_; lean_object* v_v_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2975_; 
v_k_2953_ = lean_ctor_get(v_impl_2881_, 1);
v_v_2954_ = lean_ctor_get(v_impl_2881_, 2);
v_isSharedCheck_2975_ = !lean_is_exclusive(v_impl_2881_);
if (v_isSharedCheck_2975_ == 0)
{
lean_object* v_unused_2976_; lean_object* v_unused_2977_; lean_object* v_unused_2978_; 
v_unused_2976_ = lean_ctor_get(v_impl_2881_, 4);
lean_dec(v_unused_2976_);
v_unused_2977_ = lean_ctor_get(v_impl_2881_, 3);
lean_dec(v_unused_2977_);
v_unused_2978_ = lean_ctor_get(v_impl_2881_, 0);
lean_dec(v_unused_2978_);
v___x_2956_ = v_impl_2881_;
v_isShared_2957_ = v_isSharedCheck_2975_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_v_2954_);
lean_inc(v_k_2953_);
lean_dec(v_impl_2881_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2975_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v_k_2958_; lean_object* v_v_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2971_; 
v_k_2958_ = lean_ctor_get(v_r_2952_, 1);
v_v_2959_ = lean_ctor_get(v_r_2952_, 2);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_r_2952_);
if (v_isSharedCheck_2971_ == 0)
{
lean_object* v_unused_2972_; lean_object* v_unused_2973_; lean_object* v_unused_2974_; 
v_unused_2972_ = lean_ctor_get(v_r_2952_, 4);
lean_dec(v_unused_2972_);
v_unused_2973_ = lean_ctor_get(v_r_2952_, 3);
lean_dec(v_unused_2973_);
v_unused_2974_ = lean_ctor_get(v_r_2952_, 0);
lean_dec(v_unused_2974_);
v___x_2961_ = v_r_2952_;
v_isShared_2962_ = v_isSharedCheck_2971_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_v_2959_);
lean_inc(v_k_2958_);
lean_dec(v_r_2952_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2971_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; lean_object* v___x_2965_; 
v___x_2963_ = lean_unsigned_to_nat(3u);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 4, v_l_2937_);
lean_ctor_set(v___x_2961_, 3, v_l_2937_);
lean_ctor_set(v___x_2961_, 2, v_v_2954_);
lean_ctor_set(v___x_2961_, 1, v_k_2953_);
lean_ctor_set(v___x_2961_, 0, v___x_2882_);
v___x_2965_ = v___x_2961_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2882_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_k_2953_);
lean_ctor_set(v_reuseFailAlloc_2970_, 2, v_v_2954_);
lean_ctor_set(v_reuseFailAlloc_2970_, 3, v_l_2937_);
lean_ctor_set(v_reuseFailAlloc_2970_, 4, v_l_2937_);
v___x_2965_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
lean_object* v___x_2967_; 
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 4, v_l_2937_);
lean_ctor_set(v___x_2956_, 2, v_v_2726_);
lean_ctor_set(v___x_2956_, 1, v_k_2725_);
lean_ctor_set(v___x_2956_, 0, v___x_2882_);
v___x_2967_ = v___x_2956_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v___x_2882_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_k_2725_);
lean_ctor_set(v_reuseFailAlloc_2969_, 2, v_v_2726_);
lean_ctor_set(v_reuseFailAlloc_2969_, 3, v_l_2937_);
lean_ctor_set(v_reuseFailAlloc_2969_, 4, v_l_2937_);
v___x_2967_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2968_; 
v___x_2968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2963_);
lean_ctor_set(v___x_2968_, 1, v_k_2958_);
lean_ctor_set(v___x_2968_, 2, v_v_2959_);
lean_ctor_set(v___x_2968_, 3, v___x_2965_);
lean_ctor_set(v___x_2968_, 4, v___x_2967_);
return v___x_2968_;
}
}
}
}
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = lean_unsigned_to_nat(2u);
v___x_2980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
lean_ctor_set(v___x_2980_, 1, v_k_2725_);
lean_ctor_set(v___x_2980_, 2, v_v_2726_);
lean_ctor_set(v___x_2980_, 3, v_impl_2881_);
lean_ctor_set(v___x_2980_, 4, v_r_2952_);
return v___x_2980_;
}
}
}
}
}
}
else
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_unsigned_to_nat(1u);
v___x_2995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2994_);
lean_ctor_set(v___x_2995_, 1, v_k_2707_);
lean_ctor_set(v___x_2995_, 2, v_v_2708_);
lean_ctor_set(v___x_2995_, 3, v_t_2709_);
lean_ctor_set(v___x_2995_, 4, v_t_2709_);
return v___x_2995_;
}
v___jp_2710_:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2721_ = lean_nat_add(v___y_2716_, v___y_2720_);
lean_dec(v___y_2720_);
lean_dec(v___y_2716_);
v___x_2722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
lean_ctor_set(v___x_2722_, 1, v___y_2719_);
lean_ctor_set(v___x_2722_, 2, v___y_2718_);
lean_ctor_set(v___x_2722_, 3, v___y_2715_);
lean_ctor_set(v___x_2722_, 4, v___y_2714_);
v___x_2723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2723_, 0, v___y_2713_);
lean_ctor_set(v___x_2723_, 1, v___y_2712_);
lean_ctor_set(v___x_2723_, 2, v___y_2717_);
lean_ctor_set(v___x_2723_, 3, v___y_2711_);
lean_ctor_set(v___x_2723_, 4, v___x_2722_);
return v___x_2723_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg(lean_object* v_k_2996_, lean_object* v_t_2997_){
_start:
{
if (lean_obj_tag(v_t_2997_) == 0)
{
lean_object* v_k_2998_; lean_object* v_l_2999_; lean_object* v_r_3000_; lean_object* v_fst_3001_; lean_object* v_snd_3002_; lean_object* v_fst_3003_; lean_object* v_snd_3004_; double v___x_3005_; double v___x_3006_; uint8_t v___x_3007_; 
v_k_2998_ = lean_ctor_get(v_t_2997_, 1);
v_l_2999_ = lean_ctor_get(v_t_2997_, 3);
v_r_3000_ = lean_ctor_get(v_t_2997_, 4);
v_fst_3001_ = lean_ctor_get(v_k_2996_, 0);
v_snd_3002_ = lean_ctor_get(v_k_2996_, 1);
v_fst_3003_ = lean_ctor_get(v_k_2998_, 0);
v_snd_3004_ = lean_ctor_get(v_k_2998_, 1);
v___x_3005_ = lean_unbox_float(v_fst_3001_);
v___x_3006_ = lean_unbox_float(v_fst_3003_);
v___x_3007_ = lean_float_decLt(v___x_3005_, v___x_3006_);
if (v___x_3007_ == 0)
{
double v___x_3008_; double v___x_3009_; uint8_t v___x_3010_; 
v___x_3008_ = lean_unbox_float(v_fst_3003_);
v___x_3009_ = lean_unbox_float(v_fst_3001_);
v___x_3010_ = lean_float_decLt(v___x_3008_, v___x_3009_);
if (v___x_3010_ == 0)
{
uint8_t v___x_3011_; 
v___x_3011_ = l_Lean_Name_cmp(v_snd_3002_, v_snd_3004_);
switch(v___x_3011_)
{
case 0:
{
v_t_2997_ = v_l_2999_;
goto _start;
}
case 1:
{
uint8_t v___x_3013_; 
v___x_3013_ = 1;
return v___x_3013_;
}
default: 
{
v_t_2997_ = v_r_3000_;
goto _start;
}
}
}
else
{
v_t_2997_ = v_r_3000_;
goto _start;
}
}
else
{
v_t_2997_ = v_l_2999_;
goto _start;
}
}
else
{
uint8_t v___x_3017_; 
v___x_3017_ = 0;
return v___x_3017_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg___boxed(lean_object* v_k_3018_, lean_object* v_t_3019_){
_start:
{
uint8_t v_res_3020_; lean_object* v_r_3021_; 
v_res_3020_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg(v_k_3018_, v_t_3019_);
lean_dec(v_t_3019_);
lean_dec_ref(v_k_3018_);
v_r_3021_ = lean_box(v_res_3020_);
return v_r_3021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg(double v_frequencyWeight_3022_, double v_fst_3023_, double v_depthFactor_3024_, lean_object* v_denyList_3025_, lean_object* v_as_3026_, size_t v_i_3027_, size_t v_stop_3028_, lean_object* v_b_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v_a_3033_; lean_object* v___y_3038_; lean_object* v___y_3039_; uint8_t v___x_3041_; 
v___x_3041_ = lean_usize_dec_eq(v_i_3027_, v_stop_3028_);
if (v___x_3041_ == 0)
{
lean_object* v_fst_3042_; lean_object* v_snd_3043_; lean_object* v___x_3044_; uint8_t v___y_3046_; uint8_t v___x_3074_; 
v_fst_3042_ = lean_ctor_get(v_b_3029_, 0);
v_snd_3043_ = lean_ctor_get(v_b_3029_, 1);
v___x_3044_ = lean_array_uget_borrowed(v_as_3026_, v_i_3027_);
v___x_3074_ = l_Lean_NameSet_contains(v_fst_3042_, v___x_3044_);
if (v___x_3074_ == 0)
{
uint8_t v___x_3075_; 
v___x_3075_ = l_Lean_NameSet_contains(v_denyList_3025_, v___x_3044_);
v___y_3046_ = v___x_3075_;
goto v___jp_3045_;
}
else
{
v___y_3046_ = v___x_3074_;
goto v___jp_3045_;
}
v___jp_3045_:
{
if (v___y_3046_ == 0)
{
lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3071_; 
lean_inc(v_snd_3043_);
lean_inc(v_fst_3042_);
v_isSharedCheck_3071_ = !lean_is_exclusive(v_b_3029_);
if (v_isSharedCheck_3071_ == 0)
{
lean_object* v_unused_3072_; lean_object* v_unused_3073_; 
v_unused_3072_ = lean_ctor_get(v_b_3029_, 1);
lean_dec(v_unused_3072_);
v_unused_3073_ = lean_ctor_get(v_b_3029_, 0);
lean_dec(v_unused_3073_);
v___x_3048_ = v_b_3029_;
v_isShared_3049_ = v_isSharedCheck_3071_;
goto v_resetjp_3047_;
}
else
{
lean_dec(v_b_3029_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3071_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3050_; 
v___x_3050_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg(v___x_3044_, v_frequencyWeight_3022_, v___y_3030_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3052_; double v___x_3053_; double v___x_3054_; double v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3058_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref(v___x_3050_);
lean_inc(v___x_3044_);
v___x_3052_ = l_Lean_NameSet_insert(v_fst_3042_, v___x_3044_);
v___x_3053_ = lean_float_mul(v_fst_3023_, v_depthFactor_3024_);
v___x_3054_ = lean_unbox_float(v_a_3051_);
lean_dec(v_a_3051_);
v___x_3055_ = lean_float_mul(v___x_3053_, v___x_3054_);
v___x_3056_ = lean_box_float(v___x_3055_);
lean_inc(v___x_3044_);
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 1, v___x_3044_);
lean_ctor_set(v___x_3048_, 0, v___x_3056_);
v___x_3058_ = v___x_3048_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3056_);
lean_ctor_set(v_reuseFailAlloc_3062_, 1, v___x_3044_);
v___x_3058_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
uint8_t v___x_3059_; 
v___x_3059_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg(v___x_3058_, v_snd_3043_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = lean_box(0);
v___x_3061_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(v___x_3058_, v___x_3060_, v_snd_3043_);
v___y_3038_ = v___x_3052_;
v___y_3039_ = v___x_3061_;
goto v___jp_3037_;
}
else
{
lean_dec_ref(v___x_3058_);
v___y_3038_ = v___x_3052_;
v___y_3039_ = v_snd_3043_;
goto v___jp_3037_;
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_del_object(v___x_3048_);
lean_dec(v_snd_3043_);
lean_dec(v_fst_3042_);
v_a_3063_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_3050_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3050_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
}
else
{
v_a_3033_ = v_b_3029_;
goto v___jp_3032_;
}
}
}
else
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v_b_3029_);
return v___x_3076_;
}
v___jp_3032_:
{
size_t v___x_3034_; size_t v___x_3035_; 
v___x_3034_ = ((size_t)1ULL);
v___x_3035_ = lean_usize_add(v_i_3027_, v___x_3034_);
v_i_3027_ = v___x_3035_;
v_b_3029_ = v_a_3033_;
goto _start;
}
v___jp_3037_:
{
lean_object* v___x_3040_; 
v___x_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___y_3038_);
lean_ctor_set(v___x_3040_, 1, v___y_3039_);
v_a_3033_ = v___x_3040_;
goto v___jp_3032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg___boxed(lean_object* v_frequencyWeight_3077_, lean_object* v_fst_3078_, lean_object* v_depthFactor_3079_, lean_object* v_denyList_3080_, lean_object* v_as_3081_, lean_object* v_i_3082_, lean_object* v_stop_3083_, lean_object* v_b_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
double v_frequencyWeight_boxed_3087_; double v_fst_10879__boxed_3088_; double v_depthFactor_boxed_3089_; size_t v_i_boxed_3090_; size_t v_stop_boxed_3091_; lean_object* v_res_3092_; 
v_frequencyWeight_boxed_3087_ = lean_unbox_float(v_frequencyWeight_3077_);
lean_dec_ref(v_frequencyWeight_3077_);
v_fst_10879__boxed_3088_ = lean_unbox_float(v_fst_3078_);
lean_dec_ref(v_fst_3078_);
v_depthFactor_boxed_3089_ = lean_unbox_float(v_depthFactor_3079_);
lean_dec_ref(v_depthFactor_3079_);
v_i_boxed_3090_ = lean_unbox_usize(v_i_3082_);
lean_dec(v_i_3082_);
v_stop_boxed_3091_ = lean_unbox_usize(v_stop_3083_);
lean_dec(v_stop_3083_);
v_res_3092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg(v_frequencyWeight_boxed_3087_, v_fst_10879__boxed_3088_, v_depthFactor_boxed_3089_, v_denyList_3080_, v_as_3081_, v_i_boxed_3090_, v_stop_boxed_3091_, v_b_3084_, v___y_3085_);
lean_dec(v___y_3085_);
lean_dec_ref(v_as_3081_);
lean_dec(v_denyList_3080_);
return v_res_3092_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__1));
v___x_3097_ = l_Lean_MessageData_ofFormat(v___x_3096_);
return v___x_3097_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__3(void){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3098_ = lean_box(1);
v___x_3099_ = l_Lean_MessageData_ofFormat(v___x_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6(lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
if (lean_obj_tag(v_a_3100_) == 0)
{
lean_object* v___x_3102_; 
v___x_3102_ = l_List_reverse___redArg(v_a_3101_);
return v___x_3102_;
}
else
{
lean_object* v_head_3103_; lean_object* v_tail_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3131_; 
v_head_3103_ = lean_ctor_get(v_a_3100_, 0);
v_tail_3104_ = lean_ctor_get(v_a_3100_, 1);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_a_3100_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3106_ = v_a_3100_;
v_isShared_3107_ = v_isSharedCheck_3131_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_tail_3104_);
lean_inc(v_head_3103_);
lean_dec(v_a_3100_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3131_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v_fst_3108_; lean_object* v_snd_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3130_; 
v_fst_3108_ = lean_ctor_get(v_head_3103_, 0);
v_snd_3109_ = lean_ctor_get(v_head_3103_, 1);
v_isSharedCheck_3130_ = !lean_is_exclusive(v_head_3103_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3111_ = v_head_3103_;
v_isShared_3112_ = v_isSharedCheck_3130_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_snd_3109_);
lean_inc(v_fst_3108_);
lean_dec(v_head_3103_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3130_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3116_; 
v___x_3113_ = l_Lean_MessageData_ofName(v_fst_3108_);
v___x_3114_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__2, &l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__2);
if (v_isShared_3112_ == 0)
{
lean_ctor_set_tag(v___x_3111_, 7);
lean_ctor_set(v___x_3111_, 1, v___x_3114_);
lean_ctor_set(v___x_3111_, 0, v___x_3113_);
v___x_3116_ = v___x_3111_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3113_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v___x_3114_);
v___x_3116_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; double v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3117_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__3, &l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__3);
v___x_3118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3116_);
lean_ctor_set(v___x_3118_, 1, v___x_3117_);
v___x_3119_ = lean_unbox_float(v_snd_3109_);
lean_dec(v_snd_3109_);
v___x_3120_ = lean_float_to_string(v___x_3119_);
v___x_3121_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3120_);
v___x_3122_ = l_Lean_MessageData_ofFormat(v___x_3121_);
v___x_3123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3118_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = l_Lean_MessageData_paren(v___x_3123_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 1, v_a_3101_);
lean_ctor_set(v___x_3106_, 0, v___x_3124_);
v___x_3126_ = v___x_3106_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3124_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v_a_3101_);
v___x_3126_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
v_a_3100_ = v_tail_3104_;
v_a_3101_ = v___x_3126_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9(lean_object* v_init_3132_, lean_object* v_x_3133_){
_start:
{
if (lean_obj_tag(v_x_3133_) == 0)
{
lean_object* v_k_3134_; lean_object* v_l_3135_; lean_object* v_r_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v_k_3134_ = lean_ctor_get(v_x_3133_, 1);
v_l_3135_ = lean_ctor_get(v_x_3133_, 3);
v_r_3136_ = lean_ctor_get(v_x_3133_, 4);
v___x_3137_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9(v_init_3132_, v_r_3136_);
lean_inc(v_k_3134_);
v___x_3138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3138_, 0, v_k_3134_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v_init_3132_ = v___x_3138_;
v_x_3133_ = v_l_3135_;
goto _start;
}
else
{
return v_init_3132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9___boxed(lean_object* v_init_3140_, lean_object* v_x_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9(v_init_3140_, v_x_3141_);
lean_dec(v_x_3141_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10(lean_object* v_a_3143_, lean_object* v_a_3144_){
_start:
{
if (lean_obj_tag(v_a_3143_) == 0)
{
lean_object* v___x_3145_; 
v___x_3145_ = l_List_reverse___redArg(v_a_3144_);
return v___x_3145_;
}
else
{
lean_object* v_head_3146_; lean_object* v_tail_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3174_; 
v_head_3146_ = lean_ctor_get(v_a_3143_, 0);
v_tail_3147_ = lean_ctor_get(v_a_3143_, 1);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_a_3143_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3149_ = v_a_3143_;
v_isShared_3150_ = v_isSharedCheck_3174_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_tail_3147_);
lean_inc(v_head_3146_);
lean_dec(v_a_3143_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3174_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v_fst_3151_; lean_object* v_snd_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3173_; 
v_fst_3151_ = lean_ctor_get(v_head_3146_, 0);
v_snd_3152_ = lean_ctor_get(v_head_3146_, 1);
v_isSharedCheck_3173_ = !lean_is_exclusive(v_head_3146_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3154_ = v_head_3146_;
v_isShared_3155_ = v_isSharedCheck_3173_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_snd_3152_);
lean_inc(v_fst_3151_);
lean_dec(v_head_3146_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3173_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
double v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3162_; 
v___x_3156_ = lean_unbox_float(v_fst_3151_);
lean_dec(v_fst_3151_);
v___x_3157_ = lean_float_to_string(v___x_3156_);
v___x_3158_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
v___x_3159_ = l_Lean_MessageData_ofFormat(v___x_3158_);
v___x_3160_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__2, &l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__2);
if (v_isShared_3155_ == 0)
{
lean_ctor_set_tag(v___x_3154_, 7);
lean_ctor_set(v___x_3154_, 1, v___x_3160_);
lean_ctor_set(v___x_3154_, 0, v___x_3159_);
v___x_3162_ = v___x_3154_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3159_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v___x_3160_);
v___x_3162_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3169_; 
v___x_3163_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__3, &l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___closed__3);
v___x_3164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3162_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___x_3165_ = l_Lean_MessageData_ofName(v_snd_3152_);
v___x_3166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3164_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
v___x_3167_ = l_Lean_MessageData_paren(v___x_3166_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 1, v_a_3144_);
lean_ctor_set(v___x_3149_, 0, v___x_3167_);
v___x_3169_ = v___x_3149_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3167_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v_a_3144_);
v___x_3169_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
v_a_3143_ = v_tail_3147_;
v_a_3144_ = v___x_3169_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__7(lean_object* v_init_3175_, lean_object* v_x_3176_){
_start:
{
if (lean_obj_tag(v_x_3176_) == 0)
{
lean_object* v_k_3177_; lean_object* v_l_3178_; lean_object* v_r_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v_k_3177_ = lean_ctor_get(v_x_3176_, 1);
v_l_3178_ = lean_ctor_get(v_x_3176_, 3);
v_r_3179_ = lean_ctor_get(v_x_3176_, 4);
v___x_3180_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__7(v_init_3175_, v_r_3179_);
lean_inc(v_k_3177_);
v___x_3181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3181_, 0, v_k_3177_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v_init_3175_ = v___x_3181_;
v_x_3176_ = v_l_3178_;
goto _start;
}
else
{
return v_init_3175_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__7___boxed(lean_object* v_init_3183_, lean_object* v_x_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__7(v_init_3183_, v_x_3184_);
lean_dec(v_x_3184_);
return v_res_3185_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__0(void){
_start:
{
lean_object* v___x_3186_; double v___x_3187_; 
v___x_3186_ = lean_unsigned_to_nat(0u);
v___x_3187_ = lean_float_of_nat(v___x_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11(lean_object* v_cls_3191_, lean_object* v_msg_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v_ref_3198_; lean_object* v___x_3199_; lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3244_; 
v_ref_3198_ = lean_ctor_get(v___y_3195_, 5);
v___x_3199_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9_spec__10(v_msg_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3202_ = v___x_3199_;
v_isShared_3203_ = v_isSharedCheck_3244_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3244_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v_traceState_3205_; lean_object* v_env_3206_; lean_object* v_nextMacroScope_3207_; lean_object* v_ngen_3208_; lean_object* v_auxDeclNGen_3209_; lean_object* v_cache_3210_; lean_object* v_messages_3211_; lean_object* v_infoState_3212_; lean_object* v_snapshotTasks_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3243_; 
v___x_3204_ = lean_st_ref_take(v___y_3196_);
v_traceState_3205_ = lean_ctor_get(v___x_3204_, 4);
v_env_3206_ = lean_ctor_get(v___x_3204_, 0);
v_nextMacroScope_3207_ = lean_ctor_get(v___x_3204_, 1);
v_ngen_3208_ = lean_ctor_get(v___x_3204_, 2);
v_auxDeclNGen_3209_ = lean_ctor_get(v___x_3204_, 3);
v_cache_3210_ = lean_ctor_get(v___x_3204_, 5);
v_messages_3211_ = lean_ctor_get(v___x_3204_, 6);
v_infoState_3212_ = lean_ctor_get(v___x_3204_, 7);
v_snapshotTasks_3213_ = lean_ctor_get(v___x_3204_, 8);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3215_ = v___x_3204_;
v_isShared_3216_ = v_isSharedCheck_3243_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_snapshotTasks_3213_);
lean_inc(v_infoState_3212_);
lean_inc(v_messages_3211_);
lean_inc(v_cache_3210_);
lean_inc(v_traceState_3205_);
lean_inc(v_auxDeclNGen_3209_);
lean_inc(v_ngen_3208_);
lean_inc(v_nextMacroScope_3207_);
lean_inc(v_env_3206_);
lean_dec(v___x_3204_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3243_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
uint64_t v_tid_3217_; lean_object* v_traces_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3242_; 
v_tid_3217_ = lean_ctor_get_uint64(v_traceState_3205_, sizeof(void*)*1);
v_traces_3218_ = lean_ctor_get(v_traceState_3205_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v_traceState_3205_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3220_ = v_traceState_3205_;
v_isShared_3221_ = v_isSharedCheck_3242_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_traces_3218_);
lean_dec(v_traceState_3205_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3242_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3222_; double v___x_3223_; uint8_t v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3222_ = lean_box(0);
v___x_3223_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__0, &l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__0);
v___x_3224_ = 0;
v___x_3225_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__1));
v___x_3226_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3226_, 0, v_cls_3191_);
lean_ctor_set(v___x_3226_, 1, v___x_3222_);
lean_ctor_set(v___x_3226_, 2, v___x_3225_);
lean_ctor_set_float(v___x_3226_, sizeof(void*)*3, v___x_3223_);
lean_ctor_set_float(v___x_3226_, sizeof(void*)*3 + 8, v___x_3223_);
lean_ctor_set_uint8(v___x_3226_, sizeof(void*)*3 + 16, v___x_3224_);
v___x_3227_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___closed__2));
v___x_3228_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3226_);
lean_ctor_set(v___x_3228_, 1, v_a_3200_);
lean_ctor_set(v___x_3228_, 2, v___x_3227_);
lean_inc(v_ref_3198_);
v___x_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3229_, 0, v_ref_3198_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
v___x_3230_ = l_Lean_PersistentArray_push___redArg(v_traces_3218_, v___x_3229_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 0, v___x_3230_);
v___x_3232_ = v___x_3220_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3230_);
lean_ctor_set_uint64(v_reuseFailAlloc_3241_, sizeof(void*)*1, v_tid_3217_);
v___x_3232_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3234_; 
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 4, v___x_3232_);
v___x_3234_ = v___x_3215_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_env_3206_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v_nextMacroScope_3207_);
lean_ctor_set(v_reuseFailAlloc_3240_, 2, v_ngen_3208_);
lean_ctor_set(v_reuseFailAlloc_3240_, 3, v_auxDeclNGen_3209_);
lean_ctor_set(v_reuseFailAlloc_3240_, 4, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3240_, 5, v_cache_3210_);
lean_ctor_set(v_reuseFailAlloc_3240_, 6, v_messages_3211_);
lean_ctor_set(v_reuseFailAlloc_3240_, 7, v_infoState_3212_);
lean_ctor_set(v_reuseFailAlloc_3240_, 8, v_snapshotTasks_3213_);
v___x_3234_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3235_ = lean_st_ref_set(v___y_3196_, v___x_3234_);
v___x_3236_ = lean_box(0);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 0, v___x_3236_);
v___x_3238_ = v___x_3202_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11___boxed(lean_object* v_cls_3245_, lean_object* v_msg_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11(v_cls_3245_, v_msg_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__8(lean_object* v_a_3253_, lean_object* v_a_3254_){
_start:
{
if (lean_obj_tag(v_a_3253_) == 0)
{
lean_object* v___x_3255_; 
v___x_3255_ = l_List_reverse___redArg(v_a_3254_);
return v___x_3255_;
}
else
{
lean_object* v_head_3256_; lean_object* v_tail_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3266_; 
v_head_3256_ = lean_ctor_get(v_a_3253_, 0);
v_tail_3257_ = lean_ctor_get(v_a_3253_, 1);
v_isSharedCheck_3266_ = !lean_is_exclusive(v_a_3253_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3259_ = v_a_3253_;
v_isShared_3260_ = v_isSharedCheck_3266_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_tail_3257_);
lean_inc(v_head_3256_);
lean_dec(v_a_3253_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3266_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3261_; lean_object* v___x_3263_; 
v___x_3261_ = l_Lean_MessageData_ofName(v_head_3256_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 1, v_a_3254_);
lean_ctor_set(v___x_3259_, 0, v___x_3261_);
v___x_3263_ = v___x_3259_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3261_);
lean_ctor_set(v_reuseFailAlloc_3265_, 1, v_a_3254_);
v___x_3263_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
v_a_3253_ = v_tail_3257_;
v_a_3254_ = v___x_3263_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__4(double v_fst_3267_, lean_object* v_x_3268_, lean_object* v_x_3269_){
_start:
{
if (lean_obj_tag(v_x_3269_) == 0)
{
return v_x_3268_;
}
else
{
lean_object* v_head_3270_; lean_object* v_tail_3271_; lean_object* v_fst_3272_; lean_object* v_snd_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3288_; 
v_head_3270_ = lean_ctor_get(v_x_3269_, 0);
lean_inc(v_head_3270_);
v_tail_3271_ = lean_ctor_get(v_x_3269_, 1);
lean_inc(v_tail_3271_);
lean_dec_ref(v_x_3269_);
v_fst_3272_ = lean_ctor_get(v_head_3270_, 0);
v_snd_3273_ = lean_ctor_get(v_head_3270_, 1);
v_isSharedCheck_3288_ = !lean_is_exclusive(v_head_3270_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3275_ = v_head_3270_;
v_isShared_3276_ = v_isSharedCheck_3288_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_snd_3273_);
lean_inc(v_fst_3272_);
lean_dec(v_head_3270_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3288_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
double v___x_3277_; double v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3281_; 
v___x_3277_ = lean_unbox_float(v_snd_3273_);
lean_dec(v_snd_3273_);
v___x_3278_ = lean_float_mul(v___x_3277_, v_fst_3267_);
v___x_3279_ = lean_box_float(v___x_3278_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 1, v_fst_3272_);
lean_ctor_set(v___x_3275_, 0, v___x_3279_);
v___x_3281_ = v___x_3275_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3279_);
lean_ctor_set(v_reuseFailAlloc_3287_, 1, v_fst_3272_);
v___x_3281_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
uint8_t v___x_3282_; 
v___x_3282_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg(v___x_3281_, v_x_3268_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = lean_box(0);
v___x_3284_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(v___x_3281_, v___x_3283_, v_x_3268_);
v_x_3268_ = v___x_3284_;
v_x_3269_ = v_tail_3271_;
goto _start;
}
else
{
lean_dec_ref(v___x_3281_);
v_x_3269_ = v_tail_3271_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__4___boxed(lean_object* v_fst_3289_, lean_object* v_x_3290_, lean_object* v_x_3291_){
_start:
{
double v_fst_11300__boxed_3292_; lean_object* v_res_3293_; 
v_fst_11300__boxed_3292_ = lean_unbox_float(v_fst_3289_);
lean_dec_ref(v_fst_3289_);
v_res_3293_ = l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__4(v_fst_11300__boxed_3292_, v_x_3290_, v_x_3291_);
return v_res_3293_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__1(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__0));
v___x_3296_ = l_Lean_stringToMessageData(v___x_3295_);
return v___x_3296_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__3(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__2));
v___x_3299_ = l_Lean_stringToMessageData(v___x_3298_);
return v___x_3299_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__5(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__4));
v___x_3302_ = l_Lean_stringToMessageData(v___x_3301_);
return v___x_3302_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__7(void){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__6));
v___x_3305_ = l_Lean_stringToMessageData(v___x_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go(lean_object* v_maxSuggestions_3306_, double v_depthFactor_3307_, double v_frequencyWeight_3308_, lean_object* v_denyList_3309_, lean_object* v_pastTriggers_3310_, lean_object* v_triggerQueue_3311_, lean_object* v_acceptedTheorems_3312_, lean_object* v_queuedTheorems_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_){
_start:
{
lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; double v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v_fst_3327_; lean_object* v_snd_3328_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; double v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___x_3402_; uint8_t v___x_3403_; 
v___x_3402_ = lean_array_get_size(v_acceptedTheorems_3312_);
v___x_3403_ = lean_nat_dec_le(v_maxSuggestions_3306_, v___x_3402_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_triggerQueue_3311_);
if (lean_obj_tag(v___x_3404_) == 0)
{
v___y_3355_ = v_a_3314_;
v___y_3356_ = v_a_3315_;
v___y_3357_ = v_a_3316_;
v___y_3358_ = v_a_3317_;
goto v___jp_3354_;
}
else
{
lean_object* v_val_3405_; lean_object* v_fst_3406_; lean_object* v_snd_3407_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___x_3473_; 
v_val_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_val_3405_);
lean_dec_ref(v___x_3404_);
v_fst_3406_ = lean_ctor_get(v_val_3405_, 0);
lean_inc(v_fst_3406_);
v_snd_3407_ = lean_ctor_get(v_val_3405_, 1);
v___x_3473_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queuedTheorems_3313_);
if (lean_obj_tag(v___x_3473_) == 0)
{
goto v___jp_3427_;
}
else
{
lean_object* v_val_3474_; lean_object* v_fst_3475_; double v___x_3476_; double v___x_3477_; uint8_t v___x_3478_; 
v_val_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_val_3474_);
lean_dec_ref(v___x_3473_);
v_fst_3475_ = lean_ctor_get(v_val_3474_, 0);
lean_inc(v_fst_3475_);
lean_dec(v_val_3474_);
v___x_3476_ = lean_unbox_float(v_fst_3406_);
v___x_3477_ = lean_unbox_float(v_fst_3475_);
lean_dec(v_fst_3475_);
v___x_3478_ = lean_float_decLt(v___x_3476_, v___x_3477_);
if (v___x_3478_ == 0)
{
lean_dec(v_fst_3406_);
lean_dec(v_val_3405_);
v___y_3355_ = v_a_3314_;
v___y_3356_ = v_a_3315_;
v___y_3357_ = v_a_3316_;
v___y_3358_ = v_a_3317_;
goto v___jp_3354_;
}
else
{
goto v___jp_3427_;
}
}
v___jp_3408_:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___redArg(v_snd_3407_, v___y_3412_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3415_; double v___x_3416_; lean_object* v___x_3417_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref(v___x_3413_);
v___x_3415_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v_val_3405_, v_triggerQueue_3311_);
lean_dec(v_val_3405_);
v___x_3416_ = lean_unbox_float(v_fst_3406_);
lean_dec(v_fst_3406_);
v___x_3417_ = l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__4(v___x_3416_, v_queuedTheorems_3313_, v_a_3414_);
v_triggerQueue_3311_ = v___x_3415_;
v_queuedTheorems_3313_ = v___x_3417_;
v_a_3314_ = v___y_3409_;
v_a_3315_ = v___y_3410_;
v_a_3316_ = v___y_3411_;
v_a_3317_ = v___y_3412_;
goto _start;
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_dec(v_fst_3406_);
lean_dec(v_val_3405_);
lean_dec(v_queuedTheorems_3313_);
lean_dec_ref(v_acceptedTheorems_3312_);
lean_dec(v_triggerQueue_3311_);
lean_dec(v_pastTriggers_3310_);
v_a_3419_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3413_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3413_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
v___jp_3427_:
{
lean_object* v_cls_3428_; lean_object* v___x_3429_; 
v_cls_3428_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_));
v___x_3429_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___redArg(v_cls_3428_, v_a_3316_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; uint8_t v___x_3431_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref(v___x_3429_);
v___x_3431_ = lean_unbox(v_a_3430_);
lean_dec(v_a_3430_);
if (v___x_3431_ == 0)
{
v___y_3409_ = v_a_3314_;
v___y_3410_ = v_a_3315_;
v___y_3411_ = v_a_3316_;
v___y_3412_ = v_a_3317_;
goto v___jp_3408_;
}
else
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3432_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__1, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__1_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__1);
lean_inc_ref(v_acceptedTheorems_3312_);
v___x_3433_ = lean_array_to_list(v_acceptedTheorems_3312_);
v___x_3434_ = lean_box(0);
v___x_3435_ = l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6(v___x_3433_, v___x_3434_);
v___x_3436_ = l_Lean_MessageData_ofList(v___x_3435_);
v___x_3437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3432_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
v___x_3438_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__3, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__3_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__3);
v___x_3439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3437_);
lean_ctor_set(v___x_3439_, 1, v___x_3438_);
v___x_3440_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__7(v___x_3434_, v_pastTriggers_3310_);
v___x_3441_ = l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__8(v___x_3440_, v___x_3434_);
v___x_3442_ = l_Lean_MessageData_ofList(v___x_3441_);
v___x_3443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3439_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
v___x_3444_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__5, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__5_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__5);
v___x_3445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3443_);
lean_ctor_set(v___x_3445_, 1, v___x_3444_);
v___x_3446_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9(v___x_3434_, v_triggerQueue_3311_);
v___x_3447_ = l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10(v___x_3446_, v___x_3434_);
v___x_3448_ = l_Lean_MessageData_ofList(v___x_3447_);
v___x_3449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3445_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v___x_3450_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__7, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__7_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__7);
v___x_3451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3449_);
lean_ctor_set(v___x_3451_, 1, v___x_3450_);
v___x_3452_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9(v___x_3434_, v_queuedTheorems_3313_);
v___x_3453_ = l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10(v___x_3452_, v___x_3434_);
v___x_3454_ = l_Lean_MessageData_ofList(v___x_3453_);
v___x_3455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3451_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
v___x_3456_ = l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__11(v_cls_3428_, v___x_3455_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_dec_ref(v___x_3456_);
v___y_3409_ = v_a_3314_;
v___y_3410_ = v_a_3315_;
v___y_3411_ = v_a_3316_;
v___y_3412_ = v_a_3317_;
goto v___jp_3408_;
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_dec(v_fst_3406_);
lean_dec(v_val_3405_);
lean_dec(v_queuedTheorems_3313_);
lean_dec_ref(v_acceptedTheorems_3312_);
lean_dec(v_triggerQueue_3311_);
lean_dec(v_pastTriggers_3310_);
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3456_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3456_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_dec(v_fst_3406_);
lean_dec(v_val_3405_);
lean_dec(v_queuedTheorems_3313_);
lean_dec_ref(v_acceptedTheorems_3312_);
lean_dec(v_triggerQueue_3311_);
lean_dec(v_pastTriggers_3310_);
v_a_3465_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3429_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3429_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
}
}
else
{
lean_object* v___x_3479_; 
lean_dec(v_queuedTheorems_3313_);
lean_dec(v_triggerQueue_3311_);
lean_dec(v_pastTriggers_3310_);
v___x_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3479_, 0, v_acceptedTheorems_3312_);
return v___x_3479_;
}
v___jp_3319_:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3329_ = lean_box_float(v___y_3324_);
v___x_3330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___y_3322_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
v___x_3331_ = lean_array_push(v_acceptedTheorems_3312_, v___x_3330_);
v___x_3332_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v___y_3321_, v_queuedTheorems_3313_);
lean_dec_ref(v___y_3321_);
v_pastTriggers_3310_ = v_fst_3327_;
v_triggerQueue_3311_ = v_snd_3328_;
v_acceptedTheorems_3312_ = v___x_3331_;
v_queuedTheorems_3313_ = v___x_3332_;
v_a_3314_ = v___y_3325_;
v_a_3315_ = v___y_3320_;
v_a_3316_ = v___y_3323_;
v_a_3317_ = v___y_3326_;
goto _start;
}
v___jp_3334_:
{
if (lean_obj_tag(v___y_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v_fst_3344_; lean_object* v_snd_3345_; 
v_a_3343_ = lean_ctor_get(v___y_3342_, 0);
lean_inc(v_a_3343_);
lean_dec_ref(v___y_3342_);
v_fst_3344_ = lean_ctor_get(v_a_3343_, 0);
lean_inc(v_fst_3344_);
v_snd_3345_ = lean_ctor_get(v_a_3343_, 1);
lean_inc(v_snd_3345_);
lean_dec(v_a_3343_);
v___y_3320_ = v___y_3336_;
v___y_3321_ = v___y_3335_;
v___y_3322_ = v___y_3337_;
v___y_3323_ = v___y_3338_;
v___y_3324_ = v___y_3339_;
v___y_3325_ = v___y_3340_;
v___y_3326_ = v___y_3341_;
v_fst_3327_ = v_fst_3344_;
v_snd_3328_ = v_snd_3345_;
goto v___jp_3319_;
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3335_);
lean_dec(v_queuedTheorems_3313_);
lean_dec_ref(v_acceptedTheorems_3312_);
v_a_3346_ = lean_ctor_get(v___y_3342_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___y_3342_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___y_3342_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___y_3342_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
v___jp_3354_:
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queuedTheorems_3313_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v___x_3360_; 
lean_dec(v_queuedTheorems_3313_);
lean_dec(v_triggerQueue_3311_);
lean_dec(v_pastTriggers_3310_);
v___x_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3360_, 0, v_acceptedTheorems_3312_);
return v___x_3360_;
}
else
{
lean_object* v_val_3361_; lean_object* v_fst_3362_; lean_object* v_snd_3363_; lean_object* v___x_3364_; 
v_val_3361_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_val_3361_);
lean_dec_ref(v___x_3359_);
v_fst_3362_ = lean_ctor_get(v_val_3361_, 0);
v_snd_3363_ = lean_ctor_get(v_val_3361_, 1);
lean_inc(v_snd_3363_);
lean_inc(v_snd_3363_);
v___x_3364_ = l_Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0(v_snd_3363_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
lean_dec_ref(v___x_3364_);
v___x_3366_ = l_Lean_ConstantInfo_type(v_a_3365_);
lean_dec(v_a_3365_);
v___x_3367_ = l_Lean_Expr_relevantConstants(v___x_3366_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; uint8_t v___x_3371_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3368_);
lean_dec_ref(v___x_3367_);
v___x_3369_ = lean_unsigned_to_nat(0u);
v___x_3370_ = lean_array_get_size(v_a_3368_);
v___x_3371_ = lean_nat_dec_lt(v___x_3369_, v___x_3370_);
if (v___x_3371_ == 0)
{
double v___x_3372_; 
lean_dec(v_a_3368_);
v___x_3372_ = lean_unbox_float(v_fst_3362_);
v___y_3320_ = v___y_3356_;
v___y_3321_ = v_val_3361_;
v___y_3322_ = v_snd_3363_;
v___y_3323_ = v___y_3357_;
v___y_3324_ = v___x_3372_;
v___y_3325_ = v___y_3355_;
v___y_3326_ = v___y_3358_;
v_fst_3327_ = v_pastTriggers_3310_;
v_snd_3328_ = v_triggerQueue_3311_;
goto v___jp_3319_;
}
else
{
lean_object* v___x_3373_; uint8_t v___x_3374_; 
lean_inc(v_triggerQueue_3311_);
lean_inc(v_pastTriggers_3310_);
v___x_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3373_, 0, v_pastTriggers_3310_);
lean_ctor_set(v___x_3373_, 1, v_triggerQueue_3311_);
v___x_3374_ = lean_nat_dec_le(v___x_3370_, v___x_3370_);
if (v___x_3374_ == 0)
{
if (v___x_3371_ == 0)
{
double v___x_3375_; 
lean_dec_ref(v___x_3373_);
lean_dec(v_a_3368_);
v___x_3375_ = lean_unbox_float(v_fst_3362_);
v___y_3320_ = v___y_3356_;
v___y_3321_ = v_val_3361_;
v___y_3322_ = v_snd_3363_;
v___y_3323_ = v___y_3357_;
v___y_3324_ = v___x_3375_;
v___y_3325_ = v___y_3355_;
v___y_3326_ = v___y_3358_;
v_fst_3327_ = v_pastTriggers_3310_;
v_snd_3328_ = v_triggerQueue_3311_;
goto v___jp_3319_;
}
else
{
size_t v___x_3376_; size_t v___x_3377_; double v___x_3378_; lean_object* v___x_3379_; double v___x_3380_; 
lean_dec(v_triggerQueue_3311_);
lean_dec(v_pastTriggers_3310_);
v___x_3376_ = ((size_t)0ULL);
v___x_3377_ = lean_usize_of_nat(v___x_3370_);
v___x_3378_ = lean_unbox_float(v_fst_3362_);
v___x_3379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg(v_frequencyWeight_3308_, v___x_3378_, v_depthFactor_3307_, v_denyList_3309_, v_a_3368_, v___x_3376_, v___x_3377_, v___x_3373_, v___y_3358_);
lean_dec(v_a_3368_);
v___x_3380_ = lean_unbox_float(v_fst_3362_);
v___y_3335_ = v_val_3361_;
v___y_3336_ = v___y_3356_;
v___y_3337_ = v_snd_3363_;
v___y_3338_ = v___y_3357_;
v___y_3339_ = v___x_3380_;
v___y_3340_ = v___y_3355_;
v___y_3341_ = v___y_3358_;
v___y_3342_ = v___x_3379_;
goto v___jp_3334_;
}
}
else
{
size_t v___x_3381_; size_t v___x_3382_; double v___x_3383_; lean_object* v___x_3384_; double v___x_3385_; 
lean_dec(v_triggerQueue_3311_);
lean_dec(v_pastTriggers_3310_);
v___x_3381_ = ((size_t)0ULL);
v___x_3382_ = lean_usize_of_nat(v___x_3370_);
v___x_3383_ = lean_unbox_float(v_fst_3362_);
v___x_3384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg(v_frequencyWeight_3308_, v___x_3383_, v_depthFactor_3307_, v_denyList_3309_, v_a_3368_, v___x_3381_, v___x_3382_, v___x_3373_, v___y_3358_);
lean_dec(v_a_3368_);
v___x_3385_ = lean_unbox_float(v_fst_3362_);
v___y_3335_ = v_val_3361_;
v___y_3336_ = v___y_3356_;
v___y_3337_ = v_snd_3363_;
v___y_3338_ = v___y_3357_;
v___y_3339_ = v___x_3385_;
v___y_3340_ = v___y_3355_;
v___y_3341_ = v___y_3358_;
v___y_3342_ = v___x_3384_;
goto v___jp_3334_;
}
}
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
lean_dec(v_snd_3363_);
lean_dec(v_val_3361_);
lean_dec(v_queuedTheorems_3313_);
lean_dec_ref(v_acceptedTheorems_3312_);
lean_dec(v_triggerQueue_3311_);
lean_dec(v_pastTriggers_3310_);
v_a_3386_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v___x_3367_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3367_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec(v_snd_3363_);
lean_dec(v_val_3361_);
lean_dec(v_queuedTheorems_3313_);
lean_dec_ref(v_acceptedTheorems_3312_);
lean_dec(v_triggerQueue_3311_);
lean_dec(v_pastTriggers_3310_);
v_a_3394_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3364_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3364_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___boxed(lean_object* v_maxSuggestions_3480_, lean_object* v_depthFactor_3481_, lean_object* v_frequencyWeight_3482_, lean_object* v_denyList_3483_, lean_object* v_pastTriggers_3484_, lean_object* v_triggerQueue_3485_, lean_object* v_acceptedTheorems_3486_, lean_object* v_queuedTheorems_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
double v_depthFactor_boxed_3493_; double v_frequencyWeight_boxed_3494_; lean_object* v_res_3495_; 
v_depthFactor_boxed_3493_ = lean_unbox_float(v_depthFactor_3481_);
lean_dec_ref(v_depthFactor_3481_);
v_frequencyWeight_boxed_3494_ = lean_unbox_float(v_frequencyWeight_3482_);
lean_dec_ref(v_frequencyWeight_3482_);
v_res_3495_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go(v_maxSuggestions_3480_, v_depthFactor_boxed_3493_, v_frequencyWeight_boxed_3494_, v_denyList_3483_, v_pastTriggers_3484_, v_triggerQueue_3485_, v_acceptedTheorems_3486_, v_queuedTheorems_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3490_);
lean_dec(v_a_3489_);
lean_dec_ref(v_a_3488_);
lean_dec(v_denyList_3483_);
lean_dec(v_maxSuggestions_3480_);
return v_res_3495_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0(lean_object* v_00_u03b2_3496_, lean_object* v_k_3497_, lean_object* v_t_3498_){
_start:
{
uint8_t v___x_3499_; 
v___x_3499_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg(v_k_3497_, v_t_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___boxed(lean_object* v_00_u03b2_3500_, lean_object* v_k_3501_, lean_object* v_t_3502_){
_start:
{
uint8_t v_res_3503_; lean_object* v_r_3504_; 
v_res_3503_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0(v_00_u03b2_3500_, v_k_3501_, v_t_3502_);
lean_dec(v_t_3502_);
lean_dec_ref(v_k_3501_);
v_r_3504_ = lean_box(v_res_3503_);
return v_r_3504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1(lean_object* v_00_u03b2_3505_, lean_object* v_k_3506_, lean_object* v_v_3507_, lean_object* v_t_3508_, lean_object* v_hl_3509_){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(v_k_3506_, v_v_3507_, v_t_3508_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2(lean_object* v_00_u03b2_3511_, lean_object* v_k_3512_, lean_object* v_t_3513_, lean_object* v_h_3514_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v_k_3512_, v_t_3513_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___boxed(lean_object* v_00_u03b2_3516_, lean_object* v_k_3517_, lean_object* v_t_3518_, lean_object* v_h_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2(v_00_u03b2_3516_, v_k_3517_, v_t_3518_, v_h_3519_);
lean_dec_ref(v_k_3517_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3(double v_frequencyWeight_3521_, double v_fst_3522_, double v_depthFactor_3523_, lean_object* v_denyList_3524_, lean_object* v_as_3525_, size_t v_i_3526_, size_t v_stop_3527_, lean_object* v_b_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg(v_frequencyWeight_3521_, v_fst_3522_, v_depthFactor_3523_, v_denyList_3524_, v_as_3525_, v_i_3526_, v_stop_3527_, v_b_3528_, v___y_3532_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___boxed(lean_object* v_frequencyWeight_3535_, lean_object* v_fst_3536_, lean_object* v_depthFactor_3537_, lean_object* v_denyList_3538_, lean_object* v_as_3539_, lean_object* v_i_3540_, lean_object* v_stop_3541_, lean_object* v_b_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
double v_frequencyWeight_boxed_3548_; double v_fst_11716__boxed_3549_; double v_depthFactor_boxed_3550_; size_t v_i_boxed_3551_; size_t v_stop_boxed_3552_; lean_object* v_res_3553_; 
v_frequencyWeight_boxed_3548_ = lean_unbox_float(v_frequencyWeight_3535_);
lean_dec_ref(v_frequencyWeight_3535_);
v_fst_11716__boxed_3549_ = lean_unbox_float(v_fst_3536_);
lean_dec_ref(v_fst_3536_);
v_depthFactor_boxed_3550_ = lean_unbox_float(v_depthFactor_3537_);
lean_dec_ref(v_depthFactor_3537_);
v_i_boxed_3551_ = lean_unbox_usize(v_i_3540_);
lean_dec(v_i_3540_);
v_stop_boxed_3552_ = lean_unbox_usize(v_stop_3541_);
lean_dec(v_stop_3541_);
v_res_3553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3(v_frequencyWeight_boxed_3548_, v_fst_11716__boxed_3549_, v_depthFactor_boxed_3550_, v_denyList_3538_, v_as_3539_, v_i_boxed_3551_, v_stop_boxed_3552_, v_b_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec_ref(v_as_3539_);
lean_dec(v_denyList_3538_);
return v_res_3553_;
}
}
static double _init_l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3554_; uint8_t v___x_3555_; lean_object* v___x_3556_; double v___x_3557_; 
v___x_3554_ = lean_unsigned_to_nat(2u);
v___x_3555_ = 1;
v___x_3556_ = lean_unsigned_to_nat(1u);
v___x_3557_ = l_Float_ofScientific(v___x_3556_, v___x_3555_, v___x_3554_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg(lean_object* v_x_3558_, lean_object* v_x_3559_, lean_object* v___y_3560_){
_start:
{
if (lean_obj_tag(v_x_3558_) == 0)
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = l_List_reverse___redArg(v_x_3559_);
v___x_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3562_);
return v___x_3563_;
}
else
{
lean_object* v_head_3564_; lean_object* v_tail_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3585_; 
v_head_3564_ = lean_ctor_get(v_x_3558_, 0);
v_tail_3565_ = lean_ctor_get(v_x_3558_, 1);
v_isSharedCheck_3585_ = !lean_is_exclusive(v_x_3558_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3567_ = v_x_3558_;
v_isShared_3568_ = v_isSharedCheck_3585_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_tail_3565_);
lean_inc(v_head_3564_);
lean_dec(v_x_3558_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3585_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
double v___x_3569_; lean_object* v___x_3570_; 
v___x_3569_ = lean_float_once(&l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0, &l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0_once, _init_l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0);
v___x_3570_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg(v_head_3564_, v___x_3569_, v___y_3560_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3572_; lean_object* v___x_3574_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref(v___x_3570_);
v___x_3572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3572_, 0, v_a_3571_);
lean_ctor_set(v___x_3572_, 1, v_head_3564_);
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 1, v_x_3559_);
lean_ctor_set(v___x_3567_, 0, v___x_3572_);
v___x_3574_ = v___x_3567_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3572_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v_x_3559_);
v___x_3574_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
v_x_3558_ = v_tail_3565_;
v_x_3559_ = v___x_3574_;
goto _start;
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_del_object(v___x_3567_);
lean_dec(v_tail_3565_);
lean_dec(v_head_3564_);
lean_dec(v_x_3559_);
v_a_3577_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3570_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3570_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___boxed(lean_object* v_x_3586_, lean_object* v_x_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg(v_x_3586_, v_x_3587_, v___y_3588_);
lean_dec(v___y_3588_);
return v_res_3590_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3591_; double v___x_3592_; 
v___x_3591_ = lean_unsigned_to_nat(1u);
v___x_3592_ = lean_float_of_nat(v___x_3591_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3(size_t v_sz_3593_, size_t v_i_3594_, lean_object* v_bs_3595_){
_start:
{
uint8_t v___x_3596_; 
v___x_3596_ = lean_usize_dec_lt(v_i_3594_, v_sz_3593_);
if (v___x_3596_ == 0)
{
return v_bs_3595_;
}
else
{
lean_object* v_v_3597_; lean_object* v_fst_3598_; lean_object* v_snd_3599_; lean_object* v___x_3600_; lean_object* v_bs_x27_3601_; double v___x_3602_; double v___x_3603_; double v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; size_t v___x_3607_; size_t v___x_3608_; lean_object* v___x_3609_; 
v_v_3597_ = lean_array_uget_borrowed(v_bs_3595_, v_i_3594_);
v_fst_3598_ = lean_ctor_get(v_v_3597_, 0);
lean_inc(v_fst_3598_);
v_snd_3599_ = lean_ctor_get(v_v_3597_, 1);
lean_inc(v_snd_3599_);
v___x_3600_ = lean_unsigned_to_nat(0u);
v_bs_x27_3601_ = lean_array_uset(v_bs_3595_, v_i_3594_, v___x_3600_);
v___x_3602_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___closed__0);
v___x_3603_ = lean_unbox_float(v_snd_3599_);
lean_dec(v_snd_3599_);
v___x_3604_ = lean_float_div(v___x_3602_, v___x_3603_);
v___x_3605_ = lean_box(0);
v___x_3606_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3606_, 0, v_fst_3598_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
lean_ctor_set_float(v___x_3606_, sizeof(void*)*2, v___x_3604_);
v___x_3607_ = ((size_t)1ULL);
v___x_3608_ = lean_usize_add(v_i_3594_, v___x_3607_);
v___x_3609_ = lean_array_uset(v_bs_x27_3601_, v_i_3594_, v___x_3606_);
v_i_3594_ = v___x_3608_;
v_bs_3595_ = v___x_3609_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___boxed(lean_object* v_sz_3611_, lean_object* v_i_3612_, lean_object* v_bs_3613_){
_start:
{
size_t v_sz_boxed_3614_; size_t v_i_boxed_3615_; lean_object* v_res_3616_; 
v_sz_boxed_3614_ = lean_unbox_usize(v_sz_3611_);
lean_dec(v_sz_3611_);
v_i_boxed_3615_ = lean_unbox_usize(v_i_3612_);
lean_dec(v_i_3612_);
v_res_3616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3(v_sz_boxed_3614_, v_i_boxed_3615_, v_bs_3613_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(lean_object* v_k_3617_, lean_object* v_t_3618_){
_start:
{
if (lean_obj_tag(v_t_3618_) == 0)
{
lean_object* v_k_3619_; lean_object* v_v_3620_; lean_object* v_l_3621_; lean_object* v_r_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_4276_; 
v_k_3619_ = lean_ctor_get(v_t_3618_, 1);
v_v_3620_ = lean_ctor_get(v_t_3618_, 2);
v_l_3621_ = lean_ctor_get(v_t_3618_, 3);
v_r_3622_ = lean_ctor_get(v_t_3618_, 4);
v_isSharedCheck_4276_ = !lean_is_exclusive(v_t_3618_);
if (v_isSharedCheck_4276_ == 0)
{
lean_object* v_unused_4277_; 
v_unused_4277_ = lean_ctor_get(v_t_3618_, 0);
lean_dec(v_unused_4277_);
v___x_3624_ = v_t_3618_;
v_isShared_3625_ = v_isSharedCheck_4276_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_r_3622_);
lean_inc(v_l_3621_);
lean_inc(v_v_3620_);
lean_inc(v_k_3619_);
lean_dec(v_t_3618_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_4276_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
uint8_t v___x_3626_; 
v___x_3626_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3617_, v_k_3619_);
switch(v___x_3626_)
{
case 0:
{
lean_object* v_impl_3627_; lean_object* v___x_3628_; 
v_impl_3627_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(v_k_3617_, v_l_3621_);
v___x_3628_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3627_) == 0)
{
if (lean_obj_tag(v_r_3622_) == 0)
{
lean_object* v_size_3629_; lean_object* v_size_3630_; lean_object* v_k_3631_; lean_object* v_v_3632_; lean_object* v_l_3633_; lean_object* v_r_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; uint8_t v___x_3637_; 
v_size_3629_ = lean_ctor_get(v_impl_3627_, 0);
lean_inc(v_size_3629_);
v_size_3630_ = lean_ctor_get(v_r_3622_, 0);
v_k_3631_ = lean_ctor_get(v_r_3622_, 1);
v_v_3632_ = lean_ctor_get(v_r_3622_, 2);
v_l_3633_ = lean_ctor_get(v_r_3622_, 3);
lean_inc(v_l_3633_);
v_r_3634_ = lean_ctor_get(v_r_3622_, 4);
v___x_3635_ = lean_unsigned_to_nat(3u);
v___x_3636_ = lean_nat_mul(v___x_3635_, v_size_3629_);
v___x_3637_ = lean_nat_dec_lt(v___x_3636_, v_size_3630_);
lean_dec(v___x_3636_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3641_; 
lean_dec(v_l_3633_);
v___x_3638_ = lean_nat_add(v___x_3628_, v_size_3629_);
lean_dec(v_size_3629_);
v___x_3639_ = lean_nat_add(v___x_3638_, v_size_3630_);
lean_dec(v___x_3638_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 3, v_impl_3627_);
lean_ctor_set(v___x_3624_, 0, v___x_3639_);
v___x_3641_ = v___x_3624_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3639_);
lean_ctor_set(v_reuseFailAlloc_3642_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_3642_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_3642_, 3, v_impl_3627_);
lean_ctor_set(v_reuseFailAlloc_3642_, 4, v_r_3622_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
else
{
lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3706_; 
lean_inc(v_r_3634_);
lean_inc(v_v_3632_);
lean_inc(v_k_3631_);
lean_inc(v_size_3630_);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_r_3622_);
if (v_isSharedCheck_3706_ == 0)
{
lean_object* v_unused_3707_; lean_object* v_unused_3708_; lean_object* v_unused_3709_; lean_object* v_unused_3710_; lean_object* v_unused_3711_; 
v_unused_3707_ = lean_ctor_get(v_r_3622_, 4);
lean_dec(v_unused_3707_);
v_unused_3708_ = lean_ctor_get(v_r_3622_, 3);
lean_dec(v_unused_3708_);
v_unused_3709_ = lean_ctor_get(v_r_3622_, 2);
lean_dec(v_unused_3709_);
v_unused_3710_ = lean_ctor_get(v_r_3622_, 1);
lean_dec(v_unused_3710_);
v_unused_3711_ = lean_ctor_get(v_r_3622_, 0);
lean_dec(v_unused_3711_);
v___x_3644_ = v_r_3622_;
v_isShared_3645_ = v_isSharedCheck_3706_;
goto v_resetjp_3643_;
}
else
{
lean_dec(v_r_3622_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3706_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v_size_3646_; lean_object* v_k_3647_; lean_object* v_v_3648_; lean_object* v_l_3649_; lean_object* v_r_3650_; lean_object* v_size_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; uint8_t v___x_3654_; 
v_size_3646_ = lean_ctor_get(v_l_3633_, 0);
v_k_3647_ = lean_ctor_get(v_l_3633_, 1);
v_v_3648_ = lean_ctor_get(v_l_3633_, 2);
v_l_3649_ = lean_ctor_get(v_l_3633_, 3);
v_r_3650_ = lean_ctor_get(v_l_3633_, 4);
v_size_3651_ = lean_ctor_get(v_r_3634_, 0);
v___x_3652_ = lean_unsigned_to_nat(2u);
v___x_3653_ = lean_nat_mul(v___x_3652_, v_size_3651_);
v___x_3654_ = lean_nat_dec_lt(v_size_3646_, v___x_3653_);
lean_dec(v___x_3653_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3682_; 
lean_inc(v_r_3650_);
lean_inc(v_l_3649_);
lean_inc(v_v_3648_);
lean_inc(v_k_3647_);
v_isSharedCheck_3682_ = !lean_is_exclusive(v_l_3633_);
if (v_isSharedCheck_3682_ == 0)
{
lean_object* v_unused_3683_; lean_object* v_unused_3684_; lean_object* v_unused_3685_; lean_object* v_unused_3686_; lean_object* v_unused_3687_; 
v_unused_3683_ = lean_ctor_get(v_l_3633_, 4);
lean_dec(v_unused_3683_);
v_unused_3684_ = lean_ctor_get(v_l_3633_, 3);
lean_dec(v_unused_3684_);
v_unused_3685_ = lean_ctor_get(v_l_3633_, 2);
lean_dec(v_unused_3685_);
v_unused_3686_ = lean_ctor_get(v_l_3633_, 1);
lean_dec(v_unused_3686_);
v_unused_3687_ = lean_ctor_get(v_l_3633_, 0);
lean_dec(v_unused_3687_);
v___x_3656_ = v_l_3633_;
v_isShared_3657_ = v_isSharedCheck_3682_;
goto v_resetjp_3655_;
}
else
{
lean_dec(v_l_3633_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3682_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3672_; 
v___x_3658_ = lean_nat_add(v___x_3628_, v_size_3629_);
lean_dec(v_size_3629_);
v___x_3659_ = lean_nat_add(v___x_3658_, v_size_3630_);
lean_dec(v_size_3630_);
if (lean_obj_tag(v_l_3649_) == 0)
{
lean_object* v_size_3680_; 
v_size_3680_ = lean_ctor_get(v_l_3649_, 0);
lean_inc(v_size_3680_);
v___y_3672_ = v_size_3680_;
goto v___jp_3671_;
}
else
{
lean_object* v___x_3681_; 
v___x_3681_ = lean_unsigned_to_nat(0u);
v___y_3672_ = v___x_3681_;
goto v___jp_3671_;
}
v___jp_3660_:
{
lean_object* v___x_3664_; lean_object* v___x_3666_; 
v___x_3664_ = lean_nat_add(v___y_3661_, v___y_3663_);
lean_dec(v___y_3663_);
lean_dec(v___y_3661_);
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 4, v_r_3634_);
lean_ctor_set(v___x_3656_, 3, v_r_3650_);
lean_ctor_set(v___x_3656_, 2, v_v_3632_);
lean_ctor_set(v___x_3656_, 1, v_k_3631_);
lean_ctor_set(v___x_3656_, 0, v___x_3664_);
v___x_3666_ = v___x_3656_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3664_);
lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_k_3631_);
lean_ctor_set(v_reuseFailAlloc_3670_, 2, v_v_3632_);
lean_ctor_set(v_reuseFailAlloc_3670_, 3, v_r_3650_);
lean_ctor_set(v_reuseFailAlloc_3670_, 4, v_r_3634_);
v___x_3666_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3668_; 
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 4, v___x_3666_);
lean_ctor_set(v___x_3644_, 3, v___y_3662_);
lean_ctor_set(v___x_3644_, 2, v_v_3648_);
lean_ctor_set(v___x_3644_, 1, v_k_3647_);
lean_ctor_set(v___x_3644_, 0, v___x_3659_);
v___x_3668_ = v___x_3644_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3659_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v_k_3647_);
lean_ctor_set(v_reuseFailAlloc_3669_, 2, v_v_3648_);
lean_ctor_set(v_reuseFailAlloc_3669_, 3, v___y_3662_);
lean_ctor_set(v_reuseFailAlloc_3669_, 4, v___x_3666_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
v___jp_3671_:
{
lean_object* v___x_3673_; lean_object* v___x_3675_; 
v___x_3673_ = lean_nat_add(v___x_3658_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec(v___x_3658_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 4, v_l_3649_);
lean_ctor_set(v___x_3624_, 3, v_impl_3627_);
lean_ctor_set(v___x_3624_, 0, v___x_3673_);
v___x_3675_ = v___x_3624_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_3679_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_3679_, 3, v_impl_3627_);
lean_ctor_set(v_reuseFailAlloc_3679_, 4, v_l_3649_);
v___x_3675_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
lean_object* v___x_3676_; 
v___x_3676_ = lean_nat_add(v___x_3628_, v_size_3651_);
if (lean_obj_tag(v_r_3650_) == 0)
{
lean_object* v_size_3677_; 
v_size_3677_ = lean_ctor_get(v_r_3650_, 0);
lean_inc(v_size_3677_);
v___y_3661_ = v___x_3676_;
v___y_3662_ = v___x_3675_;
v___y_3663_ = v_size_3677_;
goto v___jp_3660_;
}
else
{
lean_object* v___x_3678_; 
v___x_3678_ = lean_unsigned_to_nat(0u);
v___y_3661_ = v___x_3676_;
v___y_3662_ = v___x_3675_;
v___y_3663_ = v___x_3678_;
goto v___jp_3660_;
}
}
}
}
}
else
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3692_; 
lean_del_object(v___x_3624_);
v___x_3688_ = lean_nat_add(v___x_3628_, v_size_3629_);
lean_dec(v_size_3629_);
v___x_3689_ = lean_nat_add(v___x_3688_, v_size_3630_);
lean_dec(v_size_3630_);
v___x_3690_ = lean_nat_add(v___x_3688_, v_size_3646_);
lean_dec(v___x_3688_);
lean_inc_ref(v_impl_3627_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 4, v_l_3633_);
lean_ctor_set(v___x_3644_, 3, v_impl_3627_);
lean_ctor_set(v___x_3644_, 2, v_v_3620_);
lean_ctor_set(v___x_3644_, 1, v_k_3619_);
lean_ctor_set(v___x_3644_, 0, v___x_3690_);
v___x_3692_ = v___x_3644_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3690_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_3705_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_3705_, 3, v_impl_3627_);
lean_ctor_set(v_reuseFailAlloc_3705_, 4, v_l_3633_);
v___x_3692_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
v_isSharedCheck_3699_ = !lean_is_exclusive(v_impl_3627_);
if (v_isSharedCheck_3699_ == 0)
{
lean_object* v_unused_3700_; lean_object* v_unused_3701_; lean_object* v_unused_3702_; lean_object* v_unused_3703_; lean_object* v_unused_3704_; 
v_unused_3700_ = lean_ctor_get(v_impl_3627_, 4);
lean_dec(v_unused_3700_);
v_unused_3701_ = lean_ctor_get(v_impl_3627_, 3);
lean_dec(v_unused_3701_);
v_unused_3702_ = lean_ctor_get(v_impl_3627_, 2);
lean_dec(v_unused_3702_);
v_unused_3703_ = lean_ctor_get(v_impl_3627_, 1);
lean_dec(v_unused_3703_);
v_unused_3704_ = lean_ctor_get(v_impl_3627_, 0);
lean_dec(v_unused_3704_);
v___x_3694_ = v_impl_3627_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_dec(v_impl_3627_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 4, v_r_3634_);
lean_ctor_set(v___x_3694_, 3, v___x_3692_);
lean_ctor_set(v___x_3694_, 2, v_v_3632_);
lean_ctor_set(v___x_3694_, 1, v_k_3631_);
lean_ctor_set(v___x_3694_, 0, v___x_3689_);
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3698_, 1, v_k_3631_);
lean_ctor_set(v_reuseFailAlloc_3698_, 2, v_v_3632_);
lean_ctor_set(v_reuseFailAlloc_3698_, 3, v___x_3692_);
lean_ctor_set(v_reuseFailAlloc_3698_, 4, v_r_3634_);
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
}
}
else
{
lean_object* v_size_3712_; lean_object* v___x_3713_; lean_object* v___x_3715_; 
v_size_3712_ = lean_ctor_get(v_impl_3627_, 0);
lean_inc(v_size_3712_);
v___x_3713_ = lean_nat_add(v___x_3628_, v_size_3712_);
lean_dec(v_size_3712_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 3, v_impl_3627_);
lean_ctor_set(v___x_3624_, 0, v___x_3713_);
v___x_3715_ = v___x_3624_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3713_);
lean_ctor_set(v_reuseFailAlloc_3716_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_3716_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_3716_, 3, v_impl_3627_);
lean_ctor_set(v_reuseFailAlloc_3716_, 4, v_r_3622_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
else
{
if (lean_obj_tag(v_r_3622_) == 0)
{
lean_object* v_l_3717_; 
v_l_3717_ = lean_ctor_get(v_r_3622_, 3);
lean_inc(v_l_3717_);
if (lean_obj_tag(v_l_3717_) == 0)
{
lean_object* v_r_3718_; 
v_r_3718_ = lean_ctor_get(v_r_3622_, 4);
lean_inc(v_r_3718_);
if (lean_obj_tag(v_r_3718_) == 0)
{
lean_object* v_size_3719_; lean_object* v_k_3720_; lean_object* v_v_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3734_; 
v_size_3719_ = lean_ctor_get(v_r_3622_, 0);
v_k_3720_ = lean_ctor_get(v_r_3622_, 1);
v_v_3721_ = lean_ctor_get(v_r_3622_, 2);
v_isSharedCheck_3734_ = !lean_is_exclusive(v_r_3622_);
if (v_isSharedCheck_3734_ == 0)
{
lean_object* v_unused_3735_; lean_object* v_unused_3736_; 
v_unused_3735_ = lean_ctor_get(v_r_3622_, 4);
lean_dec(v_unused_3735_);
v_unused_3736_ = lean_ctor_get(v_r_3622_, 3);
lean_dec(v_unused_3736_);
v___x_3723_ = v_r_3622_;
v_isShared_3724_ = v_isSharedCheck_3734_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_v_3721_);
lean_inc(v_k_3720_);
lean_inc(v_size_3719_);
lean_dec(v_r_3622_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3734_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v_size_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3729_; 
v_size_3725_ = lean_ctor_get(v_l_3717_, 0);
v___x_3726_ = lean_nat_add(v___x_3628_, v_size_3719_);
lean_dec(v_size_3719_);
v___x_3727_ = lean_nat_add(v___x_3628_, v_size_3725_);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 4, v_l_3717_);
lean_ctor_set(v___x_3723_, 3, v_impl_3627_);
lean_ctor_set(v___x_3723_, 2, v_v_3620_);
lean_ctor_set(v___x_3723_, 1, v_k_3619_);
lean_ctor_set(v___x_3723_, 0, v___x_3727_);
v___x_3729_ = v___x_3723_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3727_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_3733_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_3733_, 3, v_impl_3627_);
lean_ctor_set(v_reuseFailAlloc_3733_, 4, v_l_3717_);
v___x_3729_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3731_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 4, v_r_3718_);
lean_ctor_set(v___x_3624_, 3, v___x_3729_);
lean_ctor_set(v___x_3624_, 2, v_v_3721_);
lean_ctor_set(v___x_3624_, 1, v_k_3720_);
lean_ctor_set(v___x_3624_, 0, v___x_3726_);
v___x_3731_ = v___x_3624_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3726_);
lean_ctor_set(v_reuseFailAlloc_3732_, 1, v_k_3720_);
lean_ctor_set(v_reuseFailAlloc_3732_, 2, v_v_3721_);
lean_ctor_set(v_reuseFailAlloc_3732_, 3, v___x_3729_);
lean_ctor_set(v_reuseFailAlloc_3732_, 4, v_r_3718_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
else
{
lean_object* v_k_3737_; lean_object* v_v_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3761_; 
v_k_3737_ = lean_ctor_get(v_r_3622_, 1);
v_v_3738_ = lean_ctor_get(v_r_3622_, 2);
v_isSharedCheck_3761_ = !lean_is_exclusive(v_r_3622_);
if (v_isSharedCheck_3761_ == 0)
{
lean_object* v_unused_3762_; lean_object* v_unused_3763_; lean_object* v_unused_3764_; 
v_unused_3762_ = lean_ctor_get(v_r_3622_, 4);
lean_dec(v_unused_3762_);
v_unused_3763_ = lean_ctor_get(v_r_3622_, 3);
lean_dec(v_unused_3763_);
v_unused_3764_ = lean_ctor_get(v_r_3622_, 0);
lean_dec(v_unused_3764_);
v___x_3740_ = v_r_3622_;
v_isShared_3741_ = v_isSharedCheck_3761_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_v_3738_);
lean_inc(v_k_3737_);
lean_dec(v_r_3622_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3761_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v_k_3742_; lean_object* v_v_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3757_; 
v_k_3742_ = lean_ctor_get(v_l_3717_, 1);
v_v_3743_ = lean_ctor_get(v_l_3717_, 2);
v_isSharedCheck_3757_ = !lean_is_exclusive(v_l_3717_);
if (v_isSharedCheck_3757_ == 0)
{
lean_object* v_unused_3758_; lean_object* v_unused_3759_; lean_object* v_unused_3760_; 
v_unused_3758_ = lean_ctor_get(v_l_3717_, 4);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v_l_3717_, 3);
lean_dec(v_unused_3759_);
v_unused_3760_ = lean_ctor_get(v_l_3717_, 0);
lean_dec(v_unused_3760_);
v___x_3745_ = v_l_3717_;
v_isShared_3746_ = v_isSharedCheck_3757_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_v_3743_);
lean_inc(v_k_3742_);
lean_dec(v_l_3717_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3757_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3747_; lean_object* v___x_3749_; 
v___x_3747_ = lean_unsigned_to_nat(3u);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 4, v_r_3718_);
lean_ctor_set(v___x_3745_, 3, v_r_3718_);
lean_ctor_set(v___x_3745_, 2, v_v_3620_);
lean_ctor_set(v___x_3745_, 1, v_k_3619_);
lean_ctor_set(v___x_3745_, 0, v___x_3628_);
v___x_3749_ = v___x_3745_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3628_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_3756_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_3756_, 3, v_r_3718_);
lean_ctor_set(v_reuseFailAlloc_3756_, 4, v_r_3718_);
v___x_3749_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3751_; 
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 3, v_r_3718_);
lean_ctor_set(v___x_3740_, 0, v___x_3628_);
v___x_3751_ = v___x_3740_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3628_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v_k_3737_);
lean_ctor_set(v_reuseFailAlloc_3755_, 2, v_v_3738_);
lean_ctor_set(v_reuseFailAlloc_3755_, 3, v_r_3718_);
lean_ctor_set(v_reuseFailAlloc_3755_, 4, v_r_3718_);
v___x_3751_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
lean_object* v___x_3753_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 4, v___x_3751_);
lean_ctor_set(v___x_3624_, 3, v___x_3749_);
lean_ctor_set(v___x_3624_, 2, v_v_3743_);
lean_ctor_set(v___x_3624_, 1, v_k_3742_);
lean_ctor_set(v___x_3624_, 0, v___x_3747_);
v___x_3753_ = v___x_3624_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3747_);
lean_ctor_set(v_reuseFailAlloc_3754_, 1, v_k_3742_);
lean_ctor_set(v_reuseFailAlloc_3754_, 2, v_v_3743_);
lean_ctor_set(v_reuseFailAlloc_3754_, 3, v___x_3749_);
lean_ctor_set(v_reuseFailAlloc_3754_, 4, v___x_3751_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3765_; 
v_r_3765_ = lean_ctor_get(v_r_3622_, 4);
lean_inc(v_r_3765_);
if (lean_obj_tag(v_r_3765_) == 0)
{
lean_object* v_k_3766_; lean_object* v_v_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3778_; 
v_k_3766_ = lean_ctor_get(v_r_3622_, 1);
v_v_3767_ = lean_ctor_get(v_r_3622_, 2);
v_isSharedCheck_3778_ = !lean_is_exclusive(v_r_3622_);
if (v_isSharedCheck_3778_ == 0)
{
lean_object* v_unused_3779_; lean_object* v_unused_3780_; lean_object* v_unused_3781_; 
v_unused_3779_ = lean_ctor_get(v_r_3622_, 4);
lean_dec(v_unused_3779_);
v_unused_3780_ = lean_ctor_get(v_r_3622_, 3);
lean_dec(v_unused_3780_);
v_unused_3781_ = lean_ctor_get(v_r_3622_, 0);
lean_dec(v_unused_3781_);
v___x_3769_ = v_r_3622_;
v_isShared_3770_ = v_isSharedCheck_3778_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_v_3767_);
lean_inc(v_k_3766_);
lean_dec(v_r_3622_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3778_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3771_; lean_object* v___x_3773_; 
v___x_3771_ = lean_unsigned_to_nat(3u);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 4, v_l_3717_);
lean_ctor_set(v___x_3769_, 2, v_v_3620_);
lean_ctor_set(v___x_3769_, 1, v_k_3619_);
lean_ctor_set(v___x_3769_, 0, v___x_3628_);
v___x_3773_ = v___x_3769_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3628_);
lean_ctor_set(v_reuseFailAlloc_3777_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_3777_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_3777_, 3, v_l_3717_);
lean_ctor_set(v_reuseFailAlloc_3777_, 4, v_l_3717_);
v___x_3773_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
lean_object* v___x_3775_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 4, v_r_3765_);
lean_ctor_set(v___x_3624_, 3, v___x_3773_);
lean_ctor_set(v___x_3624_, 2, v_v_3767_);
lean_ctor_set(v___x_3624_, 1, v_k_3766_);
lean_ctor_set(v___x_3624_, 0, v___x_3771_);
v___x_3775_ = v___x_3624_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3771_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v_k_3766_);
lean_ctor_set(v_reuseFailAlloc_3776_, 2, v_v_3767_);
lean_ctor_set(v_reuseFailAlloc_3776_, 3, v___x_3773_);
lean_ctor_set(v_reuseFailAlloc_3776_, 4, v_r_3765_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
else
{
lean_object* v_size_3782_; lean_object* v_k_3783_; lean_object* v_v_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3795_; 
v_size_3782_ = lean_ctor_get(v_r_3622_, 0);
v_k_3783_ = lean_ctor_get(v_r_3622_, 1);
v_v_3784_ = lean_ctor_get(v_r_3622_, 2);
v_isSharedCheck_3795_ = !lean_is_exclusive(v_r_3622_);
if (v_isSharedCheck_3795_ == 0)
{
lean_object* v_unused_3796_; lean_object* v_unused_3797_; 
v_unused_3796_ = lean_ctor_get(v_r_3622_, 4);
lean_dec(v_unused_3796_);
v_unused_3797_ = lean_ctor_get(v_r_3622_, 3);
lean_dec(v_unused_3797_);
v___x_3786_ = v_r_3622_;
v_isShared_3787_ = v_isSharedCheck_3795_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_v_3784_);
lean_inc(v_k_3783_);
lean_inc(v_size_3782_);
lean_dec(v_r_3622_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3795_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 3, v_r_3765_);
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_size_3782_);
lean_ctor_set(v_reuseFailAlloc_3794_, 1, v_k_3783_);
lean_ctor_set(v_reuseFailAlloc_3794_, 2, v_v_3784_);
lean_ctor_set(v_reuseFailAlloc_3794_, 3, v_r_3765_);
lean_ctor_set(v_reuseFailAlloc_3794_, 4, v_r_3765_);
v___x_3789_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
lean_object* v___x_3790_; lean_object* v___x_3792_; 
v___x_3790_ = lean_unsigned_to_nat(2u);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 4, v___x_3789_);
lean_ctor_set(v___x_3624_, 3, v_r_3765_);
lean_ctor_set(v___x_3624_, 0, v___x_3790_);
v___x_3792_ = v___x_3624_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v___x_3790_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_3793_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_3793_, 3, v_r_3765_);
lean_ctor_set(v_reuseFailAlloc_3793_, 4, v___x_3789_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
}
}
else
{
lean_object* v___x_3799_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 3, v_r_3622_);
lean_ctor_set(v___x_3624_, 0, v___x_3628_);
v___x_3799_ = v___x_3624_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3628_);
lean_ctor_set(v_reuseFailAlloc_3800_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_3800_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_3800_, 3, v_r_3622_);
lean_ctor_set(v_reuseFailAlloc_3800_, 4, v_r_3622_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3624_);
lean_dec(v_v_3620_);
lean_dec(v_k_3619_);
if (lean_obj_tag(v_l_3621_) == 0)
{
if (lean_obj_tag(v_r_3622_) == 0)
{
lean_object* v_size_3801_; lean_object* v_k_3802_; lean_object* v_v_3803_; lean_object* v_l_3804_; lean_object* v_r_3805_; lean_object* v_size_3806_; lean_object* v_k_3807_; lean_object* v_v_3808_; lean_object* v_l_3809_; lean_object* v_r_3810_; lean_object* v___x_3811_; uint8_t v___x_3812_; 
v_size_3801_ = lean_ctor_get(v_l_3621_, 0);
v_k_3802_ = lean_ctor_get(v_l_3621_, 1);
v_v_3803_ = lean_ctor_get(v_l_3621_, 2);
v_l_3804_ = lean_ctor_get(v_l_3621_, 3);
v_r_3805_ = lean_ctor_get(v_l_3621_, 4);
lean_inc(v_r_3805_);
v_size_3806_ = lean_ctor_get(v_r_3622_, 0);
v_k_3807_ = lean_ctor_get(v_r_3622_, 1);
v_v_3808_ = lean_ctor_get(v_r_3622_, 2);
v_l_3809_ = lean_ctor_get(v_r_3622_, 3);
lean_inc(v_l_3809_);
v_r_3810_ = lean_ctor_get(v_r_3622_, 4);
v___x_3811_ = lean_unsigned_to_nat(1u);
v___x_3812_ = lean_nat_dec_lt(v_size_3801_, v_size_3806_);
if (v___x_3812_ == 0)
{
lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3948_; 
lean_inc(v_l_3804_);
lean_inc(v_v_3803_);
lean_inc(v_k_3802_);
v_isSharedCheck_3948_ = !lean_is_exclusive(v_l_3621_);
if (v_isSharedCheck_3948_ == 0)
{
lean_object* v_unused_3949_; lean_object* v_unused_3950_; lean_object* v_unused_3951_; lean_object* v_unused_3952_; lean_object* v_unused_3953_; 
v_unused_3949_ = lean_ctor_get(v_l_3621_, 4);
lean_dec(v_unused_3949_);
v_unused_3950_ = lean_ctor_get(v_l_3621_, 3);
lean_dec(v_unused_3950_);
v_unused_3951_ = lean_ctor_get(v_l_3621_, 2);
lean_dec(v_unused_3951_);
v_unused_3952_ = lean_ctor_get(v_l_3621_, 1);
lean_dec(v_unused_3952_);
v_unused_3953_ = lean_ctor_get(v_l_3621_, 0);
lean_dec(v_unused_3953_);
v___x_3814_ = v_l_3621_;
v_isShared_3815_ = v_isSharedCheck_3948_;
goto v_resetjp_3813_;
}
else
{
lean_dec(v_l_3621_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3948_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3816_; lean_object* v_tree_3817_; 
v___x_3816_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3802_, v_v_3803_, v_l_3804_, v_r_3805_);
v_tree_3817_ = lean_ctor_get(v___x_3816_, 2);
lean_inc(v_tree_3817_);
if (lean_obj_tag(v_tree_3817_) == 0)
{
lean_object* v_k_3818_; lean_object* v_v_3819_; lean_object* v_size_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v_k_3818_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_k_3818_);
v_v_3819_ = lean_ctor_get(v___x_3816_, 1);
lean_inc(v_v_3819_);
lean_dec_ref(v___x_3816_);
v_size_3820_ = lean_ctor_get(v_tree_3817_, 0);
v___x_3821_ = lean_unsigned_to_nat(3u);
v___x_3822_ = lean_nat_mul(v___x_3821_, v_size_3820_);
v___x_3823_ = lean_nat_dec_lt(v___x_3822_, v_size_3806_);
lean_dec(v___x_3822_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3827_; 
lean_dec(v_l_3809_);
v___x_3824_ = lean_nat_add(v___x_3811_, v_size_3820_);
v___x_3825_ = lean_nat_add(v___x_3824_, v_size_3806_);
lean_dec(v___x_3824_);
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 4, v_r_3622_);
lean_ctor_set(v___x_3814_, 3, v_tree_3817_);
lean_ctor_set(v___x_3814_, 2, v_v_3819_);
lean_ctor_set(v___x_3814_, 1, v_k_3818_);
lean_ctor_set(v___x_3814_, 0, v___x_3825_);
v___x_3827_ = v___x_3814_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3825_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v_k_3818_);
lean_ctor_set(v_reuseFailAlloc_3828_, 2, v_v_3819_);
lean_ctor_set(v_reuseFailAlloc_3828_, 3, v_tree_3817_);
lean_ctor_set(v_reuseFailAlloc_3828_, 4, v_r_3622_);
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
lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3883_; 
lean_inc(v_r_3810_);
lean_inc(v_v_3808_);
lean_inc(v_k_3807_);
lean_inc(v_size_3806_);
v_isSharedCheck_3883_ = !lean_is_exclusive(v_r_3622_);
if (v_isSharedCheck_3883_ == 0)
{
lean_object* v_unused_3884_; lean_object* v_unused_3885_; lean_object* v_unused_3886_; lean_object* v_unused_3887_; lean_object* v_unused_3888_; 
v_unused_3884_ = lean_ctor_get(v_r_3622_, 4);
lean_dec(v_unused_3884_);
v_unused_3885_ = lean_ctor_get(v_r_3622_, 3);
lean_dec(v_unused_3885_);
v_unused_3886_ = lean_ctor_get(v_r_3622_, 2);
lean_dec(v_unused_3886_);
v_unused_3887_ = lean_ctor_get(v_r_3622_, 1);
lean_dec(v_unused_3887_);
v_unused_3888_ = lean_ctor_get(v_r_3622_, 0);
lean_dec(v_unused_3888_);
v___x_3830_ = v_r_3622_;
v_isShared_3831_ = v_isSharedCheck_3883_;
goto v_resetjp_3829_;
}
else
{
lean_dec(v_r_3622_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3883_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v_size_3832_; lean_object* v_k_3833_; lean_object* v_v_3834_; lean_object* v_l_3835_; lean_object* v_r_3836_; lean_object* v_size_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; uint8_t v___x_3840_; 
v_size_3832_ = lean_ctor_get(v_l_3809_, 0);
v_k_3833_ = lean_ctor_get(v_l_3809_, 1);
v_v_3834_ = lean_ctor_get(v_l_3809_, 2);
v_l_3835_ = lean_ctor_get(v_l_3809_, 3);
v_r_3836_ = lean_ctor_get(v_l_3809_, 4);
v_size_3837_ = lean_ctor_get(v_r_3810_, 0);
v___x_3838_ = lean_unsigned_to_nat(2u);
v___x_3839_ = lean_nat_mul(v___x_3838_, v_size_3837_);
v___x_3840_ = lean_nat_dec_lt(v_size_3832_, v___x_3839_);
lean_dec(v___x_3839_);
if (v___x_3840_ == 0)
{
lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3868_; 
lean_inc(v_r_3836_);
lean_inc(v_l_3835_);
lean_inc(v_v_3834_);
lean_inc(v_k_3833_);
v_isSharedCheck_3868_ = !lean_is_exclusive(v_l_3809_);
if (v_isSharedCheck_3868_ == 0)
{
lean_object* v_unused_3869_; lean_object* v_unused_3870_; lean_object* v_unused_3871_; lean_object* v_unused_3872_; lean_object* v_unused_3873_; 
v_unused_3869_ = lean_ctor_get(v_l_3809_, 4);
lean_dec(v_unused_3869_);
v_unused_3870_ = lean_ctor_get(v_l_3809_, 3);
lean_dec(v_unused_3870_);
v_unused_3871_ = lean_ctor_get(v_l_3809_, 2);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_l_3809_, 1);
lean_dec(v_unused_3872_);
v_unused_3873_ = lean_ctor_get(v_l_3809_, 0);
lean_dec(v_unused_3873_);
v___x_3842_ = v_l_3809_;
v_isShared_3843_ = v_isSharedCheck_3868_;
goto v_resetjp_3841_;
}
else
{
lean_dec(v_l_3809_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3868_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3858_; 
v___x_3844_ = lean_nat_add(v___x_3811_, v_size_3820_);
v___x_3845_ = lean_nat_add(v___x_3844_, v_size_3806_);
lean_dec(v_size_3806_);
if (lean_obj_tag(v_l_3835_) == 0)
{
lean_object* v_size_3866_; 
v_size_3866_ = lean_ctor_get(v_l_3835_, 0);
lean_inc(v_size_3866_);
v___y_3858_ = v_size_3866_;
goto v___jp_3857_;
}
else
{
lean_object* v___x_3867_; 
v___x_3867_ = lean_unsigned_to_nat(0u);
v___y_3858_ = v___x_3867_;
goto v___jp_3857_;
}
v___jp_3846_:
{
lean_object* v___x_3850_; lean_object* v___x_3852_; 
v___x_3850_ = lean_nat_add(v___y_3847_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec(v___y_3847_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 4, v_r_3810_);
lean_ctor_set(v___x_3842_, 3, v_r_3836_);
lean_ctor_set(v___x_3842_, 2, v_v_3808_);
lean_ctor_set(v___x_3842_, 1, v_k_3807_);
lean_ctor_set(v___x_3842_, 0, v___x_3850_);
v___x_3852_ = v___x_3842_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3850_);
lean_ctor_set(v_reuseFailAlloc_3856_, 1, v_k_3807_);
lean_ctor_set(v_reuseFailAlloc_3856_, 2, v_v_3808_);
lean_ctor_set(v_reuseFailAlloc_3856_, 3, v_r_3836_);
lean_ctor_set(v_reuseFailAlloc_3856_, 4, v_r_3810_);
v___x_3852_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
lean_object* v___x_3854_; 
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 4, v___x_3852_);
lean_ctor_set(v___x_3830_, 3, v___y_3848_);
lean_ctor_set(v___x_3830_, 2, v_v_3834_);
lean_ctor_set(v___x_3830_, 1, v_k_3833_);
lean_ctor_set(v___x_3830_, 0, v___x_3845_);
v___x_3854_ = v___x_3830_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3845_);
lean_ctor_set(v_reuseFailAlloc_3855_, 1, v_k_3833_);
lean_ctor_set(v_reuseFailAlloc_3855_, 2, v_v_3834_);
lean_ctor_set(v_reuseFailAlloc_3855_, 3, v___y_3848_);
lean_ctor_set(v_reuseFailAlloc_3855_, 4, v___x_3852_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
v___jp_3857_:
{
lean_object* v___x_3859_; lean_object* v___x_3861_; 
v___x_3859_ = lean_nat_add(v___x_3844_, v___y_3858_);
lean_dec(v___y_3858_);
lean_dec(v___x_3844_);
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 4, v_l_3835_);
lean_ctor_set(v___x_3814_, 3, v_tree_3817_);
lean_ctor_set(v___x_3814_, 2, v_v_3819_);
lean_ctor_set(v___x_3814_, 1, v_k_3818_);
lean_ctor_set(v___x_3814_, 0, v___x_3859_);
v___x_3861_ = v___x_3814_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_k_3818_);
lean_ctor_set(v_reuseFailAlloc_3865_, 2, v_v_3819_);
lean_ctor_set(v_reuseFailAlloc_3865_, 3, v_tree_3817_);
lean_ctor_set(v_reuseFailAlloc_3865_, 4, v_l_3835_);
v___x_3861_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3862_; 
v___x_3862_ = lean_nat_add(v___x_3811_, v_size_3837_);
if (lean_obj_tag(v_r_3836_) == 0)
{
lean_object* v_size_3863_; 
v_size_3863_ = lean_ctor_get(v_r_3836_, 0);
lean_inc(v_size_3863_);
v___y_3847_ = v___x_3862_;
v___y_3848_ = v___x_3861_;
v___y_3849_ = v_size_3863_;
goto v___jp_3846_;
}
else
{
lean_object* v___x_3864_; 
v___x_3864_ = lean_unsigned_to_nat(0u);
v___y_3847_ = v___x_3862_;
v___y_3848_ = v___x_3861_;
v___y_3849_ = v___x_3864_;
goto v___jp_3846_;
}
}
}
}
}
else
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3878_; 
v___x_3874_ = lean_nat_add(v___x_3811_, v_size_3820_);
v___x_3875_ = lean_nat_add(v___x_3874_, v_size_3806_);
lean_dec(v_size_3806_);
v___x_3876_ = lean_nat_add(v___x_3874_, v_size_3832_);
lean_dec(v___x_3874_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 4, v_l_3809_);
lean_ctor_set(v___x_3830_, 3, v_tree_3817_);
lean_ctor_set(v___x_3830_, 2, v_v_3819_);
lean_ctor_set(v___x_3830_, 1, v_k_3818_);
lean_ctor_set(v___x_3830_, 0, v___x_3876_);
v___x_3878_ = v___x_3830_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3876_);
lean_ctor_set(v_reuseFailAlloc_3882_, 1, v_k_3818_);
lean_ctor_set(v_reuseFailAlloc_3882_, 2, v_v_3819_);
lean_ctor_set(v_reuseFailAlloc_3882_, 3, v_tree_3817_);
lean_ctor_set(v_reuseFailAlloc_3882_, 4, v_l_3809_);
v___x_3878_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
lean_object* v___x_3880_; 
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 4, v_r_3810_);
lean_ctor_set(v___x_3814_, 3, v___x_3878_);
lean_ctor_set(v___x_3814_, 2, v_v_3808_);
lean_ctor_set(v___x_3814_, 1, v_k_3807_);
lean_ctor_set(v___x_3814_, 0, v___x_3875_);
v___x_3880_ = v___x_3814_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v___x_3875_);
lean_ctor_set(v_reuseFailAlloc_3881_, 1, v_k_3807_);
lean_ctor_set(v_reuseFailAlloc_3881_, 2, v_v_3808_);
lean_ctor_set(v_reuseFailAlloc_3881_, 3, v___x_3878_);
lean_ctor_set(v_reuseFailAlloc_3881_, 4, v_r_3810_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
}
}
else
{
lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3942_; 
lean_inc(v_r_3810_);
lean_inc(v_v_3808_);
lean_inc(v_k_3807_);
lean_inc(v_size_3806_);
v_isSharedCheck_3942_ = !lean_is_exclusive(v_r_3622_);
if (v_isSharedCheck_3942_ == 0)
{
lean_object* v_unused_3943_; lean_object* v_unused_3944_; lean_object* v_unused_3945_; lean_object* v_unused_3946_; lean_object* v_unused_3947_; 
v_unused_3943_ = lean_ctor_get(v_r_3622_, 4);
lean_dec(v_unused_3943_);
v_unused_3944_ = lean_ctor_get(v_r_3622_, 3);
lean_dec(v_unused_3944_);
v_unused_3945_ = lean_ctor_get(v_r_3622_, 2);
lean_dec(v_unused_3945_);
v_unused_3946_ = lean_ctor_get(v_r_3622_, 1);
lean_dec(v_unused_3946_);
v_unused_3947_ = lean_ctor_get(v_r_3622_, 0);
lean_dec(v_unused_3947_);
v___x_3890_ = v_r_3622_;
v_isShared_3891_ = v_isSharedCheck_3942_;
goto v_resetjp_3889_;
}
else
{
lean_dec(v_r_3622_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3942_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
if (lean_obj_tag(v_l_3809_) == 0)
{
if (lean_obj_tag(v_r_3810_) == 0)
{
lean_object* v_k_3892_; lean_object* v_v_3893_; lean_object* v_size_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3898_; 
v_k_3892_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_k_3892_);
v_v_3893_ = lean_ctor_get(v___x_3816_, 1);
lean_inc(v_v_3893_);
lean_dec_ref(v___x_3816_);
v_size_3894_ = lean_ctor_get(v_l_3809_, 0);
v___x_3895_ = lean_nat_add(v___x_3811_, v_size_3806_);
lean_dec(v_size_3806_);
v___x_3896_ = lean_nat_add(v___x_3811_, v_size_3894_);
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 4, v_l_3809_);
lean_ctor_set(v___x_3890_, 3, v_tree_3817_);
lean_ctor_set(v___x_3890_, 2, v_v_3893_);
lean_ctor_set(v___x_3890_, 1, v_k_3892_);
lean_ctor_set(v___x_3890_, 0, v___x_3896_);
v___x_3898_ = v___x_3890_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v___x_3896_);
lean_ctor_set(v_reuseFailAlloc_3902_, 1, v_k_3892_);
lean_ctor_set(v_reuseFailAlloc_3902_, 2, v_v_3893_);
lean_ctor_set(v_reuseFailAlloc_3902_, 3, v_tree_3817_);
lean_ctor_set(v_reuseFailAlloc_3902_, 4, v_l_3809_);
v___x_3898_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
lean_object* v___x_3900_; 
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 4, v_r_3810_);
lean_ctor_set(v___x_3814_, 3, v___x_3898_);
lean_ctor_set(v___x_3814_, 2, v_v_3808_);
lean_ctor_set(v___x_3814_, 1, v_k_3807_);
lean_ctor_set(v___x_3814_, 0, v___x_3895_);
v___x_3900_ = v___x_3814_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3895_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v_k_3807_);
lean_ctor_set(v_reuseFailAlloc_3901_, 2, v_v_3808_);
lean_ctor_set(v_reuseFailAlloc_3901_, 3, v___x_3898_);
lean_ctor_set(v_reuseFailAlloc_3901_, 4, v_r_3810_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
}
else
{
lean_object* v_k_3903_; lean_object* v_v_3904_; lean_object* v_k_3905_; lean_object* v_v_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3920_; 
lean_dec(v_size_3806_);
v_k_3903_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_k_3903_);
v_v_3904_ = lean_ctor_get(v___x_3816_, 1);
lean_inc(v_v_3904_);
lean_dec_ref(v___x_3816_);
v_k_3905_ = lean_ctor_get(v_l_3809_, 1);
v_v_3906_ = lean_ctor_get(v_l_3809_, 2);
v_isSharedCheck_3920_ = !lean_is_exclusive(v_l_3809_);
if (v_isSharedCheck_3920_ == 0)
{
lean_object* v_unused_3921_; lean_object* v_unused_3922_; lean_object* v_unused_3923_; 
v_unused_3921_ = lean_ctor_get(v_l_3809_, 4);
lean_dec(v_unused_3921_);
v_unused_3922_ = lean_ctor_get(v_l_3809_, 3);
lean_dec(v_unused_3922_);
v_unused_3923_ = lean_ctor_get(v_l_3809_, 0);
lean_dec(v_unused_3923_);
v___x_3908_ = v_l_3809_;
v_isShared_3909_ = v_isSharedCheck_3920_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_v_3906_);
lean_inc(v_k_3905_);
lean_dec(v_l_3809_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3920_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3910_; lean_object* v___x_3912_; 
v___x_3910_ = lean_unsigned_to_nat(3u);
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 4, v_r_3810_);
lean_ctor_set(v___x_3908_, 3, v_r_3810_);
lean_ctor_set(v___x_3908_, 2, v_v_3904_);
lean_ctor_set(v___x_3908_, 1, v_k_3903_);
lean_ctor_set(v___x_3908_, 0, v___x_3811_);
v___x_3912_ = v___x_3908_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3919_, 1, v_k_3903_);
lean_ctor_set(v_reuseFailAlloc_3919_, 2, v_v_3904_);
lean_ctor_set(v_reuseFailAlloc_3919_, 3, v_r_3810_);
lean_ctor_set(v_reuseFailAlloc_3919_, 4, v_r_3810_);
v___x_3912_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
lean_object* v___x_3914_; 
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 3, v_r_3810_);
lean_ctor_set(v___x_3890_, 0, v___x_3811_);
v___x_3914_ = v___x_3890_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3918_, 1, v_k_3807_);
lean_ctor_set(v_reuseFailAlloc_3918_, 2, v_v_3808_);
lean_ctor_set(v_reuseFailAlloc_3918_, 3, v_r_3810_);
lean_ctor_set(v_reuseFailAlloc_3918_, 4, v_r_3810_);
v___x_3914_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
lean_object* v___x_3916_; 
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 4, v___x_3914_);
lean_ctor_set(v___x_3814_, 3, v___x_3912_);
lean_ctor_set(v___x_3814_, 2, v_v_3906_);
lean_ctor_set(v___x_3814_, 1, v_k_3905_);
lean_ctor_set(v___x_3814_, 0, v___x_3910_);
v___x_3916_ = v___x_3814_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3910_);
lean_ctor_set(v_reuseFailAlloc_3917_, 1, v_k_3905_);
lean_ctor_set(v_reuseFailAlloc_3917_, 2, v_v_3906_);
lean_ctor_set(v_reuseFailAlloc_3917_, 3, v___x_3912_);
lean_ctor_set(v_reuseFailAlloc_3917_, 4, v___x_3914_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3810_) == 0)
{
lean_object* v_k_3924_; lean_object* v_v_3925_; lean_object* v___x_3926_; lean_object* v___x_3928_; 
lean_dec(v_size_3806_);
v_k_3924_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_k_3924_);
v_v_3925_ = lean_ctor_get(v___x_3816_, 1);
lean_inc(v_v_3925_);
lean_dec_ref(v___x_3816_);
v___x_3926_ = lean_unsigned_to_nat(3u);
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 4, v_l_3809_);
lean_ctor_set(v___x_3890_, 2, v_v_3925_);
lean_ctor_set(v___x_3890_, 1, v_k_3924_);
lean_ctor_set(v___x_3890_, 0, v___x_3811_);
v___x_3928_ = v___x_3890_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3932_, 1, v_k_3924_);
lean_ctor_set(v_reuseFailAlloc_3932_, 2, v_v_3925_);
lean_ctor_set(v_reuseFailAlloc_3932_, 3, v_l_3809_);
lean_ctor_set(v_reuseFailAlloc_3932_, 4, v_l_3809_);
v___x_3928_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3930_; 
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 4, v_r_3810_);
lean_ctor_set(v___x_3814_, 3, v___x_3928_);
lean_ctor_set(v___x_3814_, 2, v_v_3808_);
lean_ctor_set(v___x_3814_, 1, v_k_3807_);
lean_ctor_set(v___x_3814_, 0, v___x_3926_);
v___x_3930_ = v___x_3814_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3931_, 1, v_k_3807_);
lean_ctor_set(v_reuseFailAlloc_3931_, 2, v_v_3808_);
lean_ctor_set(v_reuseFailAlloc_3931_, 3, v___x_3928_);
lean_ctor_set(v_reuseFailAlloc_3931_, 4, v_r_3810_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
else
{
lean_object* v_k_3933_; lean_object* v_v_3934_; lean_object* v___x_3936_; 
v_k_3933_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_k_3933_);
v_v_3934_ = lean_ctor_get(v___x_3816_, 1);
lean_inc(v_v_3934_);
lean_dec_ref(v___x_3816_);
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 3, v_r_3810_);
v___x_3936_ = v___x_3890_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_size_3806_);
lean_ctor_set(v_reuseFailAlloc_3941_, 1, v_k_3807_);
lean_ctor_set(v_reuseFailAlloc_3941_, 2, v_v_3808_);
lean_ctor_set(v_reuseFailAlloc_3941_, 3, v_r_3810_);
lean_ctor_set(v_reuseFailAlloc_3941_, 4, v_r_3810_);
v___x_3936_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
lean_object* v___x_3937_; lean_object* v___x_3939_; 
v___x_3937_ = lean_unsigned_to_nat(2u);
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 4, v___x_3936_);
lean_ctor_set(v___x_3814_, 3, v_r_3810_);
lean_ctor_set(v___x_3814_, 2, v_v_3934_);
lean_ctor_set(v___x_3814_, 1, v_k_3933_);
lean_ctor_set(v___x_3814_, 0, v___x_3937_);
v___x_3939_ = v___x_3814_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3937_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v_k_3933_);
lean_ctor_set(v_reuseFailAlloc_3940_, 2, v_v_3934_);
lean_ctor_set(v_reuseFailAlloc_3940_, 3, v_r_3810_);
lean_ctor_set(v_reuseFailAlloc_3940_, 4, v___x_3936_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
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
lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_4106_; 
lean_inc(v_r_3810_);
lean_inc(v_v_3808_);
lean_inc(v_k_3807_);
v_isSharedCheck_4106_ = !lean_is_exclusive(v_r_3622_);
if (v_isSharedCheck_4106_ == 0)
{
lean_object* v_unused_4107_; lean_object* v_unused_4108_; lean_object* v_unused_4109_; lean_object* v_unused_4110_; lean_object* v_unused_4111_; 
v_unused_4107_ = lean_ctor_get(v_r_3622_, 4);
lean_dec(v_unused_4107_);
v_unused_4108_ = lean_ctor_get(v_r_3622_, 3);
lean_dec(v_unused_4108_);
v_unused_4109_ = lean_ctor_get(v_r_3622_, 2);
lean_dec(v_unused_4109_);
v_unused_4110_ = lean_ctor_get(v_r_3622_, 1);
lean_dec(v_unused_4110_);
v_unused_4111_ = lean_ctor_get(v_r_3622_, 0);
lean_dec(v_unused_4111_);
v___x_3955_ = v_r_3622_;
v_isShared_3956_ = v_isSharedCheck_4106_;
goto v_resetjp_3954_;
}
else
{
lean_dec(v_r_3622_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_4106_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3957_; lean_object* v_tree_3958_; 
v___x_3957_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3807_, v_v_3808_, v_l_3809_, v_r_3810_);
v_tree_3958_ = lean_ctor_get(v___x_3957_, 2);
lean_inc(v_tree_3958_);
if (lean_obj_tag(v_tree_3958_) == 0)
{
lean_object* v_k_3959_; lean_object* v_v_3960_; lean_object* v_size_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; 
v_k_3959_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_k_3959_);
v_v_3960_ = lean_ctor_get(v___x_3957_, 1);
lean_inc(v_v_3960_);
lean_dec_ref(v___x_3957_);
v_size_3961_ = lean_ctor_get(v_tree_3958_, 0);
v___x_3962_ = lean_unsigned_to_nat(3u);
v___x_3963_ = lean_nat_mul(v___x_3962_, v_size_3961_);
v___x_3964_ = lean_nat_dec_lt(v___x_3963_, v_size_3801_);
lean_dec(v___x_3963_);
if (v___x_3964_ == 0)
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3968_; 
lean_dec(v_r_3805_);
v___x_3965_ = lean_nat_add(v___x_3811_, v_size_3801_);
v___x_3966_ = lean_nat_add(v___x_3965_, v_size_3961_);
lean_dec(v___x_3965_);
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 4, v_tree_3958_);
lean_ctor_set(v___x_3955_, 3, v_l_3621_);
lean_ctor_set(v___x_3955_, 2, v_v_3960_);
lean_ctor_set(v___x_3955_, 1, v_k_3959_);
lean_ctor_set(v___x_3955_, 0, v___x_3966_);
v___x_3968_ = v___x_3955_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3966_);
lean_ctor_set(v_reuseFailAlloc_3969_, 1, v_k_3959_);
lean_ctor_set(v_reuseFailAlloc_3969_, 2, v_v_3960_);
lean_ctor_set(v_reuseFailAlloc_3969_, 3, v_l_3621_);
lean_ctor_set(v_reuseFailAlloc_3969_, 4, v_tree_3958_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
else
{
lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_4035_; 
lean_inc(v_l_3804_);
lean_inc(v_v_3803_);
lean_inc(v_k_3802_);
lean_inc(v_size_3801_);
v_isSharedCheck_4035_ = !lean_is_exclusive(v_l_3621_);
if (v_isSharedCheck_4035_ == 0)
{
lean_object* v_unused_4036_; lean_object* v_unused_4037_; lean_object* v_unused_4038_; lean_object* v_unused_4039_; lean_object* v_unused_4040_; 
v_unused_4036_ = lean_ctor_get(v_l_3621_, 4);
lean_dec(v_unused_4036_);
v_unused_4037_ = lean_ctor_get(v_l_3621_, 3);
lean_dec(v_unused_4037_);
v_unused_4038_ = lean_ctor_get(v_l_3621_, 2);
lean_dec(v_unused_4038_);
v_unused_4039_ = lean_ctor_get(v_l_3621_, 1);
lean_dec(v_unused_4039_);
v_unused_4040_ = lean_ctor_get(v_l_3621_, 0);
lean_dec(v_unused_4040_);
v___x_3971_ = v_l_3621_;
v_isShared_3972_ = v_isSharedCheck_4035_;
goto v_resetjp_3970_;
}
else
{
lean_dec(v_l_3621_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_4035_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v_size_3973_; lean_object* v_size_3974_; lean_object* v_k_3975_; lean_object* v_v_3976_; lean_object* v_l_3977_; lean_object* v_r_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; uint8_t v___x_3981_; 
v_size_3973_ = lean_ctor_get(v_l_3804_, 0);
v_size_3974_ = lean_ctor_get(v_r_3805_, 0);
v_k_3975_ = lean_ctor_get(v_r_3805_, 1);
v_v_3976_ = lean_ctor_get(v_r_3805_, 2);
v_l_3977_ = lean_ctor_get(v_r_3805_, 3);
v_r_3978_ = lean_ctor_get(v_r_3805_, 4);
v___x_3979_ = lean_unsigned_to_nat(2u);
v___x_3980_ = lean_nat_mul(v___x_3979_, v_size_3973_);
v___x_3981_ = lean_nat_dec_lt(v_size_3974_, v___x_3980_);
lean_dec(v___x_3980_);
if (v___x_3981_ == 0)
{
lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_4019_; 
lean_inc(v_r_3978_);
lean_inc(v_l_3977_);
lean_inc(v_v_3976_);
lean_inc(v_k_3975_);
lean_del_object(v___x_3971_);
v_isSharedCheck_4019_ = !lean_is_exclusive(v_r_3805_);
if (v_isSharedCheck_4019_ == 0)
{
lean_object* v_unused_4020_; lean_object* v_unused_4021_; lean_object* v_unused_4022_; lean_object* v_unused_4023_; lean_object* v_unused_4024_; 
v_unused_4020_ = lean_ctor_get(v_r_3805_, 4);
lean_dec(v_unused_4020_);
v_unused_4021_ = lean_ctor_get(v_r_3805_, 3);
lean_dec(v_unused_4021_);
v_unused_4022_ = lean_ctor_get(v_r_3805_, 2);
lean_dec(v_unused_4022_);
v_unused_4023_ = lean_ctor_get(v_r_3805_, 1);
lean_dec(v_unused_4023_);
v_unused_4024_ = lean_ctor_get(v_r_3805_, 0);
lean_dec(v_unused_4024_);
v___x_3983_ = v_r_3805_;
v_isShared_3984_ = v_isSharedCheck_4019_;
goto v_resetjp_3982_;
}
else
{
lean_dec(v_r_3805_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_4019_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___x_4007_; lean_object* v___y_4009_; 
v___x_3985_ = lean_nat_add(v___x_3811_, v_size_3801_);
lean_dec(v_size_3801_);
v___x_3986_ = lean_nat_add(v___x_3985_, v_size_3961_);
lean_dec(v___x_3985_);
v___x_4007_ = lean_nat_add(v___x_3811_, v_size_3973_);
if (lean_obj_tag(v_l_3977_) == 0)
{
lean_object* v_size_4017_; 
v_size_4017_ = lean_ctor_get(v_l_3977_, 0);
lean_inc(v_size_4017_);
v___y_4009_ = v_size_4017_;
goto v___jp_4008_;
}
else
{
lean_object* v___x_4018_; 
v___x_4018_ = lean_unsigned_to_nat(0u);
v___y_4009_ = v___x_4018_;
goto v___jp_4008_;
}
v___jp_3987_:
{
lean_object* v___x_3991_; lean_object* v___x_3993_; 
v___x_3991_ = lean_nat_add(v___y_3988_, v___y_3990_);
lean_dec(v___y_3990_);
lean_dec(v___y_3988_);
lean_inc_ref(v_tree_3958_);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 4, v_tree_3958_);
lean_ctor_set(v___x_3983_, 3, v_r_3978_);
lean_ctor_set(v___x_3983_, 2, v_v_3960_);
lean_ctor_set(v___x_3983_, 1, v_k_3959_);
lean_ctor_set(v___x_3983_, 0, v___x_3991_);
v___x_3993_ = v___x_3983_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v___x_3991_);
lean_ctor_set(v_reuseFailAlloc_4006_, 1, v_k_3959_);
lean_ctor_set(v_reuseFailAlloc_4006_, 2, v_v_3960_);
lean_ctor_set(v_reuseFailAlloc_4006_, 3, v_r_3978_);
lean_ctor_set(v_reuseFailAlloc_4006_, 4, v_tree_3958_);
v___x_3993_ = v_reuseFailAlloc_4006_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
v_isSharedCheck_4000_ = !lean_is_exclusive(v_tree_3958_);
if (v_isSharedCheck_4000_ == 0)
{
lean_object* v_unused_4001_; lean_object* v_unused_4002_; lean_object* v_unused_4003_; lean_object* v_unused_4004_; lean_object* v_unused_4005_; 
v_unused_4001_ = lean_ctor_get(v_tree_3958_, 4);
lean_dec(v_unused_4001_);
v_unused_4002_ = lean_ctor_get(v_tree_3958_, 3);
lean_dec(v_unused_4002_);
v_unused_4003_ = lean_ctor_get(v_tree_3958_, 2);
lean_dec(v_unused_4003_);
v_unused_4004_ = lean_ctor_get(v_tree_3958_, 1);
lean_dec(v_unused_4004_);
v_unused_4005_ = lean_ctor_get(v_tree_3958_, 0);
lean_dec(v_unused_4005_);
v___x_3995_ = v_tree_3958_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_dec(v_tree_3958_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 4, v___x_3993_);
lean_ctor_set(v___x_3995_, 3, v___y_3989_);
lean_ctor_set(v___x_3995_, 2, v_v_3976_);
lean_ctor_set(v___x_3995_, 1, v_k_3975_);
lean_ctor_set(v___x_3995_, 0, v___x_3986_);
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3986_);
lean_ctor_set(v_reuseFailAlloc_3999_, 1, v_k_3975_);
lean_ctor_set(v_reuseFailAlloc_3999_, 2, v_v_3976_);
lean_ctor_set(v_reuseFailAlloc_3999_, 3, v___y_3989_);
lean_ctor_set(v_reuseFailAlloc_3999_, 4, v___x_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
v___jp_4008_:
{
lean_object* v___x_4010_; lean_object* v___x_4012_; 
v___x_4010_ = lean_nat_add(v___x_4007_, v___y_4009_);
lean_dec(v___y_4009_);
lean_dec(v___x_4007_);
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 4, v_l_3977_);
lean_ctor_set(v___x_3955_, 3, v_l_3804_);
lean_ctor_set(v___x_3955_, 2, v_v_3803_);
lean_ctor_set(v___x_3955_, 1, v_k_3802_);
lean_ctor_set(v___x_3955_, 0, v___x_4010_);
v___x_4012_ = v___x_3955_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v___x_4010_);
lean_ctor_set(v_reuseFailAlloc_4016_, 1, v_k_3802_);
lean_ctor_set(v_reuseFailAlloc_4016_, 2, v_v_3803_);
lean_ctor_set(v_reuseFailAlloc_4016_, 3, v_l_3804_);
lean_ctor_set(v_reuseFailAlloc_4016_, 4, v_l_3977_);
v___x_4012_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
lean_object* v___x_4013_; 
v___x_4013_ = lean_nat_add(v___x_3811_, v_size_3961_);
if (lean_obj_tag(v_r_3978_) == 0)
{
lean_object* v_size_4014_; 
v_size_4014_ = lean_ctor_get(v_r_3978_, 0);
lean_inc(v_size_4014_);
v___y_3988_ = v___x_4013_;
v___y_3989_ = v___x_4012_;
v___y_3990_ = v_size_4014_;
goto v___jp_3987_;
}
else
{
lean_object* v___x_4015_; 
v___x_4015_ = lean_unsigned_to_nat(0u);
v___y_3988_ = v___x_4013_;
v___y_3989_ = v___x_4012_;
v___y_3990_ = v___x_4015_;
goto v___jp_3987_;
}
}
}
}
}
else
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4030_; 
v___x_4025_ = lean_nat_add(v___x_3811_, v_size_3801_);
lean_dec(v_size_3801_);
v___x_4026_ = lean_nat_add(v___x_4025_, v_size_3961_);
lean_dec(v___x_4025_);
v___x_4027_ = lean_nat_add(v___x_3811_, v_size_3961_);
v___x_4028_ = lean_nat_add(v___x_4027_, v_size_3974_);
lean_dec(v___x_4027_);
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 4, v_tree_3958_);
lean_ctor_set(v___x_3955_, 3, v_r_3805_);
lean_ctor_set(v___x_3955_, 2, v_v_3960_);
lean_ctor_set(v___x_3955_, 1, v_k_3959_);
lean_ctor_set(v___x_3955_, 0, v___x_4028_);
v___x_4030_ = v___x_3955_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4028_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v_k_3959_);
lean_ctor_set(v_reuseFailAlloc_4034_, 2, v_v_3960_);
lean_ctor_set(v_reuseFailAlloc_4034_, 3, v_r_3805_);
lean_ctor_set(v_reuseFailAlloc_4034_, 4, v_tree_3958_);
v___x_4030_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4032_; 
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 4, v___x_4030_);
lean_ctor_set(v___x_3971_, 0, v___x_4026_);
v___x_4032_ = v___x_3971_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4026_);
lean_ctor_set(v_reuseFailAlloc_4033_, 1, v_k_3802_);
lean_ctor_set(v_reuseFailAlloc_4033_, 2, v_v_3803_);
lean_ctor_set(v_reuseFailAlloc_4033_, 3, v_l_3804_);
lean_ctor_set(v_reuseFailAlloc_4033_, 4, v___x_4030_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3804_) == 0)
{
lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4064_; 
lean_inc_ref(v_l_3804_);
lean_inc(v_v_3803_);
lean_inc(v_k_3802_);
lean_inc(v_size_3801_);
v_isSharedCheck_4064_ = !lean_is_exclusive(v_l_3621_);
if (v_isSharedCheck_4064_ == 0)
{
lean_object* v_unused_4065_; lean_object* v_unused_4066_; lean_object* v_unused_4067_; lean_object* v_unused_4068_; lean_object* v_unused_4069_; 
v_unused_4065_ = lean_ctor_get(v_l_3621_, 4);
lean_dec(v_unused_4065_);
v_unused_4066_ = lean_ctor_get(v_l_3621_, 3);
lean_dec(v_unused_4066_);
v_unused_4067_ = lean_ctor_get(v_l_3621_, 2);
lean_dec(v_unused_4067_);
v_unused_4068_ = lean_ctor_get(v_l_3621_, 1);
lean_dec(v_unused_4068_);
v_unused_4069_ = lean_ctor_get(v_l_3621_, 0);
lean_dec(v_unused_4069_);
v___x_4042_ = v_l_3621_;
v_isShared_4043_ = v_isSharedCheck_4064_;
goto v_resetjp_4041_;
}
else
{
lean_dec(v_l_3621_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4064_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
if (lean_obj_tag(v_r_3805_) == 0)
{
lean_object* v_k_4044_; lean_object* v_v_4045_; lean_object* v_size_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4050_; 
v_k_4044_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_k_4044_);
v_v_4045_ = lean_ctor_get(v___x_3957_, 1);
lean_inc(v_v_4045_);
lean_dec_ref(v___x_3957_);
v_size_4046_ = lean_ctor_get(v_r_3805_, 0);
v___x_4047_ = lean_nat_add(v___x_3811_, v_size_3801_);
lean_dec(v_size_3801_);
v___x_4048_ = lean_nat_add(v___x_3811_, v_size_4046_);
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 4, v_tree_3958_);
lean_ctor_set(v___x_3955_, 3, v_r_3805_);
lean_ctor_set(v___x_3955_, 2, v_v_4045_);
lean_ctor_set(v___x_3955_, 1, v_k_4044_);
lean_ctor_set(v___x_3955_, 0, v___x_4048_);
v___x_4050_ = v___x_3955_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v___x_4048_);
lean_ctor_set(v_reuseFailAlloc_4054_, 1, v_k_4044_);
lean_ctor_set(v_reuseFailAlloc_4054_, 2, v_v_4045_);
lean_ctor_set(v_reuseFailAlloc_4054_, 3, v_r_3805_);
lean_ctor_set(v_reuseFailAlloc_4054_, 4, v_tree_3958_);
v___x_4050_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
lean_object* v___x_4052_; 
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 4, v___x_4050_);
lean_ctor_set(v___x_4042_, 0, v___x_4047_);
v___x_4052_ = v___x_4042_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_4047_);
lean_ctor_set(v_reuseFailAlloc_4053_, 1, v_k_3802_);
lean_ctor_set(v_reuseFailAlloc_4053_, 2, v_v_3803_);
lean_ctor_set(v_reuseFailAlloc_4053_, 3, v_l_3804_);
lean_ctor_set(v_reuseFailAlloc_4053_, 4, v___x_4050_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
else
{
lean_object* v_k_4055_; lean_object* v_v_4056_; lean_object* v___x_4057_; lean_object* v___x_4059_; 
lean_dec(v_size_3801_);
v_k_4055_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_k_4055_);
v_v_4056_ = lean_ctor_get(v___x_3957_, 1);
lean_inc(v_v_4056_);
lean_dec_ref(v___x_3957_);
v___x_4057_ = lean_unsigned_to_nat(3u);
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 4, v_r_3805_);
lean_ctor_set(v___x_3955_, 3, v_r_3805_);
lean_ctor_set(v___x_3955_, 2, v_v_4056_);
lean_ctor_set(v___x_3955_, 1, v_k_4055_);
lean_ctor_set(v___x_3955_, 0, v___x_3811_);
v___x_4059_ = v___x_3955_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_4063_, 1, v_k_4055_);
lean_ctor_set(v_reuseFailAlloc_4063_, 2, v_v_4056_);
lean_ctor_set(v_reuseFailAlloc_4063_, 3, v_r_3805_);
lean_ctor_set(v_reuseFailAlloc_4063_, 4, v_r_3805_);
v___x_4059_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
lean_object* v___x_4061_; 
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 4, v___x_4059_);
lean_ctor_set(v___x_4042_, 0, v___x_4057_);
v___x_4061_ = v___x_4042_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4057_);
lean_ctor_set(v_reuseFailAlloc_4062_, 1, v_k_3802_);
lean_ctor_set(v_reuseFailAlloc_4062_, 2, v_v_3803_);
lean_ctor_set(v_reuseFailAlloc_4062_, 3, v_l_3804_);
lean_ctor_set(v_reuseFailAlloc_4062_, 4, v___x_4059_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3805_) == 0)
{
lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4094_; 
lean_inc(v_l_3804_);
lean_inc(v_v_3803_);
lean_inc(v_k_3802_);
v_isSharedCheck_4094_ = !lean_is_exclusive(v_l_3621_);
if (v_isSharedCheck_4094_ == 0)
{
lean_object* v_unused_4095_; lean_object* v_unused_4096_; lean_object* v_unused_4097_; lean_object* v_unused_4098_; lean_object* v_unused_4099_; 
v_unused_4095_ = lean_ctor_get(v_l_3621_, 4);
lean_dec(v_unused_4095_);
v_unused_4096_ = lean_ctor_get(v_l_3621_, 3);
lean_dec(v_unused_4096_);
v_unused_4097_ = lean_ctor_get(v_l_3621_, 2);
lean_dec(v_unused_4097_);
v_unused_4098_ = lean_ctor_get(v_l_3621_, 1);
lean_dec(v_unused_4098_);
v_unused_4099_ = lean_ctor_get(v_l_3621_, 0);
lean_dec(v_unused_4099_);
v___x_4071_ = v_l_3621_;
v_isShared_4072_ = v_isSharedCheck_4094_;
goto v_resetjp_4070_;
}
else
{
lean_dec(v_l_3621_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4094_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v_k_4073_; lean_object* v_v_4074_; lean_object* v_k_4075_; lean_object* v_v_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4090_; 
v_k_4073_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_k_4073_);
v_v_4074_ = lean_ctor_get(v___x_3957_, 1);
lean_inc(v_v_4074_);
lean_dec_ref(v___x_3957_);
v_k_4075_ = lean_ctor_get(v_r_3805_, 1);
v_v_4076_ = lean_ctor_get(v_r_3805_, 2);
v_isSharedCheck_4090_ = !lean_is_exclusive(v_r_3805_);
if (v_isSharedCheck_4090_ == 0)
{
lean_object* v_unused_4091_; lean_object* v_unused_4092_; lean_object* v_unused_4093_; 
v_unused_4091_ = lean_ctor_get(v_r_3805_, 4);
lean_dec(v_unused_4091_);
v_unused_4092_ = lean_ctor_get(v_r_3805_, 3);
lean_dec(v_unused_4092_);
v_unused_4093_ = lean_ctor_get(v_r_3805_, 0);
lean_dec(v_unused_4093_);
v___x_4078_ = v_r_3805_;
v_isShared_4079_ = v_isSharedCheck_4090_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_v_4076_);
lean_inc(v_k_4075_);
lean_dec(v_r_3805_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4090_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4080_; lean_object* v___x_4082_; 
v___x_4080_ = lean_unsigned_to_nat(3u);
if (v_isShared_4079_ == 0)
{
lean_ctor_set(v___x_4078_, 4, v_l_3804_);
lean_ctor_set(v___x_4078_, 3, v_l_3804_);
lean_ctor_set(v___x_4078_, 2, v_v_3803_);
lean_ctor_set(v___x_4078_, 1, v_k_3802_);
lean_ctor_set(v___x_4078_, 0, v___x_3811_);
v___x_4082_ = v___x_4078_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_4089_, 1, v_k_3802_);
lean_ctor_set(v_reuseFailAlloc_4089_, 2, v_v_3803_);
lean_ctor_set(v_reuseFailAlloc_4089_, 3, v_l_3804_);
lean_ctor_set(v_reuseFailAlloc_4089_, 4, v_l_3804_);
v___x_4082_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
lean_object* v___x_4084_; 
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 4, v_l_3804_);
lean_ctor_set(v___x_3955_, 3, v_l_3804_);
lean_ctor_set(v___x_3955_, 2, v_v_4074_);
lean_ctor_set(v___x_3955_, 1, v_k_4073_);
lean_ctor_set(v___x_3955_, 0, v___x_3811_);
v___x_4084_ = v___x_3955_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_4088_, 1, v_k_4073_);
lean_ctor_set(v_reuseFailAlloc_4088_, 2, v_v_4074_);
lean_ctor_set(v_reuseFailAlloc_4088_, 3, v_l_3804_);
lean_ctor_set(v_reuseFailAlloc_4088_, 4, v_l_3804_);
v___x_4084_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
lean_object* v___x_4086_; 
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 4, v___x_4084_);
lean_ctor_set(v___x_4071_, 3, v___x_4082_);
lean_ctor_set(v___x_4071_, 2, v_v_4076_);
lean_ctor_set(v___x_4071_, 1, v_k_4075_);
lean_ctor_set(v___x_4071_, 0, v___x_4080_);
v___x_4086_ = v___x_4071_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v___x_4080_);
lean_ctor_set(v_reuseFailAlloc_4087_, 1, v_k_4075_);
lean_ctor_set(v_reuseFailAlloc_4087_, 2, v_v_4076_);
lean_ctor_set(v_reuseFailAlloc_4087_, 3, v___x_4082_);
lean_ctor_set(v_reuseFailAlloc_4087_, 4, v___x_4084_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
}
}
else
{
lean_object* v_k_4100_; lean_object* v_v_4101_; lean_object* v___x_4102_; lean_object* v___x_4104_; 
v_k_4100_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_k_4100_);
v_v_4101_ = lean_ctor_get(v___x_3957_, 1);
lean_inc(v_v_4101_);
lean_dec_ref(v___x_3957_);
v___x_4102_ = lean_unsigned_to_nat(2u);
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 4, v_r_3805_);
lean_ctor_set(v___x_3955_, 3, v_l_3621_);
lean_ctor_set(v___x_3955_, 2, v_v_4101_);
lean_ctor_set(v___x_3955_, 1, v_k_4100_);
lean_ctor_set(v___x_3955_, 0, v___x_4102_);
v___x_4104_ = v___x_3955_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4102_);
lean_ctor_set(v_reuseFailAlloc_4105_, 1, v_k_4100_);
lean_ctor_set(v_reuseFailAlloc_4105_, 2, v_v_4101_);
lean_ctor_set(v_reuseFailAlloc_4105_, 3, v_l_3621_);
lean_ctor_set(v_reuseFailAlloc_4105_, 4, v_r_3805_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
}
}
}
else
{
return v_l_3621_;
}
}
else
{
return v_r_3622_;
}
}
default: 
{
lean_object* v_impl_4112_; lean_object* v___x_4113_; 
v_impl_4112_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(v_k_3617_, v_r_3622_);
v___x_4113_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_4112_) == 0)
{
if (lean_obj_tag(v_l_3621_) == 0)
{
lean_object* v_size_4114_; lean_object* v_size_4115_; lean_object* v_k_4116_; lean_object* v_v_4117_; lean_object* v_l_4118_; lean_object* v_r_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; uint8_t v___x_4122_; 
v_size_4114_ = lean_ctor_get(v_impl_4112_, 0);
lean_inc(v_size_4114_);
v_size_4115_ = lean_ctor_get(v_l_3621_, 0);
v_k_4116_ = lean_ctor_get(v_l_3621_, 1);
v_v_4117_ = lean_ctor_get(v_l_3621_, 2);
v_l_4118_ = lean_ctor_get(v_l_3621_, 3);
v_r_4119_ = lean_ctor_get(v_l_3621_, 4);
lean_inc(v_r_4119_);
v___x_4120_ = lean_unsigned_to_nat(3u);
v___x_4121_ = lean_nat_mul(v___x_4120_, v_size_4114_);
v___x_4122_ = lean_nat_dec_lt(v___x_4121_, v_size_4115_);
lean_dec(v___x_4121_);
if (v___x_4122_ == 0)
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4126_; 
lean_dec(v_r_4119_);
v___x_4123_ = lean_nat_add(v___x_4113_, v_size_4115_);
v___x_4124_ = lean_nat_add(v___x_4123_, v_size_4114_);
lean_dec(v_size_4114_);
lean_dec(v___x_4123_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 4, v_impl_4112_);
lean_ctor_set(v___x_3624_, 0, v___x_4124_);
v___x_4126_ = v___x_3624_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4124_);
lean_ctor_set(v_reuseFailAlloc_4127_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_4127_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_4127_, 3, v_l_3621_);
lean_ctor_set(v_reuseFailAlloc_4127_, 4, v_impl_4112_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
return v___x_4126_;
}
}
else
{
lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4193_; 
lean_inc(v_l_4118_);
lean_inc(v_v_4117_);
lean_inc(v_k_4116_);
lean_inc(v_size_4115_);
v_isSharedCheck_4193_ = !lean_is_exclusive(v_l_3621_);
if (v_isSharedCheck_4193_ == 0)
{
lean_object* v_unused_4194_; lean_object* v_unused_4195_; lean_object* v_unused_4196_; lean_object* v_unused_4197_; lean_object* v_unused_4198_; 
v_unused_4194_ = lean_ctor_get(v_l_3621_, 4);
lean_dec(v_unused_4194_);
v_unused_4195_ = lean_ctor_get(v_l_3621_, 3);
lean_dec(v_unused_4195_);
v_unused_4196_ = lean_ctor_get(v_l_3621_, 2);
lean_dec(v_unused_4196_);
v_unused_4197_ = lean_ctor_get(v_l_3621_, 1);
lean_dec(v_unused_4197_);
v_unused_4198_ = lean_ctor_get(v_l_3621_, 0);
lean_dec(v_unused_4198_);
v___x_4129_ = v_l_3621_;
v_isShared_4130_ = v_isSharedCheck_4193_;
goto v_resetjp_4128_;
}
else
{
lean_dec(v_l_3621_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4193_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v_size_4131_; lean_object* v_size_4132_; lean_object* v_k_4133_; lean_object* v_v_4134_; lean_object* v_l_4135_; lean_object* v_r_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; uint8_t v___x_4139_; 
v_size_4131_ = lean_ctor_get(v_l_4118_, 0);
v_size_4132_ = lean_ctor_get(v_r_4119_, 0);
v_k_4133_ = lean_ctor_get(v_r_4119_, 1);
v_v_4134_ = lean_ctor_get(v_r_4119_, 2);
v_l_4135_ = lean_ctor_get(v_r_4119_, 3);
v_r_4136_ = lean_ctor_get(v_r_4119_, 4);
v___x_4137_ = lean_unsigned_to_nat(2u);
v___x_4138_ = lean_nat_mul(v___x_4137_, v_size_4131_);
v___x_4139_ = lean_nat_dec_lt(v_size_4132_, v___x_4138_);
lean_dec(v___x_4138_);
if (v___x_4139_ == 0)
{
lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4168_; 
lean_inc(v_r_4136_);
lean_inc(v_l_4135_);
lean_inc(v_v_4134_);
lean_inc(v_k_4133_);
v_isSharedCheck_4168_ = !lean_is_exclusive(v_r_4119_);
if (v_isSharedCheck_4168_ == 0)
{
lean_object* v_unused_4169_; lean_object* v_unused_4170_; lean_object* v_unused_4171_; lean_object* v_unused_4172_; lean_object* v_unused_4173_; 
v_unused_4169_ = lean_ctor_get(v_r_4119_, 4);
lean_dec(v_unused_4169_);
v_unused_4170_ = lean_ctor_get(v_r_4119_, 3);
lean_dec(v_unused_4170_);
v_unused_4171_ = lean_ctor_get(v_r_4119_, 2);
lean_dec(v_unused_4171_);
v_unused_4172_ = lean_ctor_get(v_r_4119_, 1);
lean_dec(v_unused_4172_);
v_unused_4173_ = lean_ctor_get(v_r_4119_, 0);
lean_dec(v_unused_4173_);
v___x_4141_ = v_r_4119_;
v_isShared_4142_ = v_isSharedCheck_4168_;
goto v_resetjp_4140_;
}
else
{
lean_dec(v_r_4119_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4168_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___x_4156_; lean_object* v___y_4158_; 
v___x_4143_ = lean_nat_add(v___x_4113_, v_size_4115_);
lean_dec(v_size_4115_);
v___x_4144_ = lean_nat_add(v___x_4143_, v_size_4114_);
lean_dec(v___x_4143_);
v___x_4156_ = lean_nat_add(v___x_4113_, v_size_4131_);
if (lean_obj_tag(v_l_4135_) == 0)
{
lean_object* v_size_4166_; 
v_size_4166_ = lean_ctor_get(v_l_4135_, 0);
lean_inc(v_size_4166_);
v___y_4158_ = v_size_4166_;
goto v___jp_4157_;
}
else
{
lean_object* v___x_4167_; 
v___x_4167_ = lean_unsigned_to_nat(0u);
v___y_4158_ = v___x_4167_;
goto v___jp_4157_;
}
v___jp_4145_:
{
lean_object* v___x_4149_; lean_object* v___x_4151_; 
v___x_4149_ = lean_nat_add(v___y_4147_, v___y_4148_);
lean_dec(v___y_4148_);
lean_dec(v___y_4147_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 4, v_impl_4112_);
lean_ctor_set(v___x_4141_, 3, v_r_4136_);
lean_ctor_set(v___x_4141_, 2, v_v_3620_);
lean_ctor_set(v___x_4141_, 1, v_k_3619_);
lean_ctor_set(v___x_4141_, 0, v___x_4149_);
v___x_4151_ = v___x_4141_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4149_);
lean_ctor_set(v_reuseFailAlloc_4155_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_4155_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_4155_, 3, v_r_4136_);
lean_ctor_set(v_reuseFailAlloc_4155_, 4, v_impl_4112_);
v___x_4151_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
lean_object* v___x_4153_; 
if (v_isShared_4130_ == 0)
{
lean_ctor_set(v___x_4129_, 4, v___x_4151_);
lean_ctor_set(v___x_4129_, 3, v___y_4146_);
lean_ctor_set(v___x_4129_, 2, v_v_4134_);
lean_ctor_set(v___x_4129_, 1, v_k_4133_);
lean_ctor_set(v___x_4129_, 0, v___x_4144_);
v___x_4153_ = v___x_4129_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v___x_4144_);
lean_ctor_set(v_reuseFailAlloc_4154_, 1, v_k_4133_);
lean_ctor_set(v_reuseFailAlloc_4154_, 2, v_v_4134_);
lean_ctor_set(v_reuseFailAlloc_4154_, 3, v___y_4146_);
lean_ctor_set(v_reuseFailAlloc_4154_, 4, v___x_4151_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
v___jp_4157_:
{
lean_object* v___x_4159_; lean_object* v___x_4161_; 
v___x_4159_ = lean_nat_add(v___x_4156_, v___y_4158_);
lean_dec(v___y_4158_);
lean_dec(v___x_4156_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 4, v_l_4135_);
lean_ctor_set(v___x_3624_, 3, v_l_4118_);
lean_ctor_set(v___x_3624_, 2, v_v_4117_);
lean_ctor_set(v___x_3624_, 1, v_k_4116_);
lean_ctor_set(v___x_3624_, 0, v___x_4159_);
v___x_4161_ = v___x_3624_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4159_);
lean_ctor_set(v_reuseFailAlloc_4165_, 1, v_k_4116_);
lean_ctor_set(v_reuseFailAlloc_4165_, 2, v_v_4117_);
lean_ctor_set(v_reuseFailAlloc_4165_, 3, v_l_4118_);
lean_ctor_set(v_reuseFailAlloc_4165_, 4, v_l_4135_);
v___x_4161_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
lean_object* v___x_4162_; 
v___x_4162_ = lean_nat_add(v___x_4113_, v_size_4114_);
lean_dec(v_size_4114_);
if (lean_obj_tag(v_r_4136_) == 0)
{
lean_object* v_size_4163_; 
v_size_4163_ = lean_ctor_get(v_r_4136_, 0);
lean_inc(v_size_4163_);
v___y_4146_ = v___x_4161_;
v___y_4147_ = v___x_4162_;
v___y_4148_ = v_size_4163_;
goto v___jp_4145_;
}
else
{
lean_object* v___x_4164_; 
v___x_4164_ = lean_unsigned_to_nat(0u);
v___y_4146_ = v___x_4161_;
v___y_4147_ = v___x_4162_;
v___y_4148_ = v___x_4164_;
goto v___jp_4145_;
}
}
}
}
}
else
{
lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4179_; 
lean_del_object(v___x_3624_);
v___x_4174_ = lean_nat_add(v___x_4113_, v_size_4115_);
lean_dec(v_size_4115_);
v___x_4175_ = lean_nat_add(v___x_4174_, v_size_4114_);
lean_dec(v___x_4174_);
v___x_4176_ = lean_nat_add(v___x_4113_, v_size_4114_);
lean_dec(v_size_4114_);
v___x_4177_ = lean_nat_add(v___x_4176_, v_size_4132_);
lean_dec(v___x_4176_);
lean_inc_ref(v_impl_4112_);
if (v_isShared_4130_ == 0)
{
lean_ctor_set(v___x_4129_, 4, v_impl_4112_);
lean_ctor_set(v___x_4129_, 3, v_r_4119_);
lean_ctor_set(v___x_4129_, 2, v_v_3620_);
lean_ctor_set(v___x_4129_, 1, v_k_3619_);
lean_ctor_set(v___x_4129_, 0, v___x_4177_);
v___x_4179_ = v___x_4129_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v___x_4177_);
lean_ctor_set(v_reuseFailAlloc_4192_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_4192_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_4192_, 3, v_r_4119_);
lean_ctor_set(v_reuseFailAlloc_4192_, 4, v_impl_4112_);
v___x_4179_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4186_; 
v_isSharedCheck_4186_ = !lean_is_exclusive(v_impl_4112_);
if (v_isSharedCheck_4186_ == 0)
{
lean_object* v_unused_4187_; lean_object* v_unused_4188_; lean_object* v_unused_4189_; lean_object* v_unused_4190_; lean_object* v_unused_4191_; 
v_unused_4187_ = lean_ctor_get(v_impl_4112_, 4);
lean_dec(v_unused_4187_);
v_unused_4188_ = lean_ctor_get(v_impl_4112_, 3);
lean_dec(v_unused_4188_);
v_unused_4189_ = lean_ctor_get(v_impl_4112_, 2);
lean_dec(v_unused_4189_);
v_unused_4190_ = lean_ctor_get(v_impl_4112_, 1);
lean_dec(v_unused_4190_);
v_unused_4191_ = lean_ctor_get(v_impl_4112_, 0);
lean_dec(v_unused_4191_);
v___x_4181_ = v_impl_4112_;
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
else
{
lean_dec(v_impl_4112_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4184_; 
if (v_isShared_4182_ == 0)
{
lean_ctor_set(v___x_4181_, 4, v___x_4179_);
lean_ctor_set(v___x_4181_, 3, v_l_4118_);
lean_ctor_set(v___x_4181_, 2, v_v_4117_);
lean_ctor_set(v___x_4181_, 1, v_k_4116_);
lean_ctor_set(v___x_4181_, 0, v___x_4175_);
v___x_4184_ = v___x_4181_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v___x_4175_);
lean_ctor_set(v_reuseFailAlloc_4185_, 1, v_k_4116_);
lean_ctor_set(v_reuseFailAlloc_4185_, 2, v_v_4117_);
lean_ctor_set(v_reuseFailAlloc_4185_, 3, v_l_4118_);
lean_ctor_set(v_reuseFailAlloc_4185_, 4, v___x_4179_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_4199_; lean_object* v___x_4200_; lean_object* v___x_4202_; 
v_size_4199_ = lean_ctor_get(v_impl_4112_, 0);
lean_inc(v_size_4199_);
v___x_4200_ = lean_nat_add(v___x_4113_, v_size_4199_);
lean_dec(v_size_4199_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 4, v_impl_4112_);
lean_ctor_set(v___x_3624_, 0, v___x_4200_);
v___x_4202_ = v___x_3624_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v___x_4200_);
lean_ctor_set(v_reuseFailAlloc_4203_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_4203_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_4203_, 3, v_l_3621_);
lean_ctor_set(v_reuseFailAlloc_4203_, 4, v_impl_4112_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
else
{
if (lean_obj_tag(v_l_3621_) == 0)
{
lean_object* v_l_4204_; 
v_l_4204_ = lean_ctor_get(v_l_3621_, 3);
if (lean_obj_tag(v_l_4204_) == 0)
{
lean_object* v_r_4205_; 
lean_inc_ref(v_l_4204_);
v_r_4205_ = lean_ctor_get(v_l_3621_, 4);
lean_inc(v_r_4205_);
if (lean_obj_tag(v_r_4205_) == 0)
{
lean_object* v_size_4206_; lean_object* v_k_4207_; lean_object* v_v_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4221_; 
v_size_4206_ = lean_ctor_get(v_l_3621_, 0);
v_k_4207_ = lean_ctor_get(v_l_3621_, 1);
v_v_4208_ = lean_ctor_get(v_l_3621_, 2);
v_isSharedCheck_4221_ = !lean_is_exclusive(v_l_3621_);
if (v_isSharedCheck_4221_ == 0)
{
lean_object* v_unused_4222_; lean_object* v_unused_4223_; 
v_unused_4222_ = lean_ctor_get(v_l_3621_, 4);
lean_dec(v_unused_4222_);
v_unused_4223_ = lean_ctor_get(v_l_3621_, 3);
lean_dec(v_unused_4223_);
v___x_4210_ = v_l_3621_;
v_isShared_4211_ = v_isSharedCheck_4221_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_v_4208_);
lean_inc(v_k_4207_);
lean_inc(v_size_4206_);
lean_dec(v_l_3621_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4221_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v_size_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4216_; 
v_size_4212_ = lean_ctor_get(v_r_4205_, 0);
v___x_4213_ = lean_nat_add(v___x_4113_, v_size_4206_);
lean_dec(v_size_4206_);
v___x_4214_ = lean_nat_add(v___x_4113_, v_size_4212_);
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 4, v_impl_4112_);
lean_ctor_set(v___x_4210_, 3, v_r_4205_);
lean_ctor_set(v___x_4210_, 2, v_v_3620_);
lean_ctor_set(v___x_4210_, 1, v_k_3619_);
lean_ctor_set(v___x_4210_, 0, v___x_4214_);
v___x_4216_ = v___x_4210_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4214_);
lean_ctor_set(v_reuseFailAlloc_4220_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_4220_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_4220_, 3, v_r_4205_);
lean_ctor_set(v_reuseFailAlloc_4220_, 4, v_impl_4112_);
v___x_4216_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
lean_object* v___x_4218_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 4, v___x_4216_);
lean_ctor_set(v___x_3624_, 3, v_l_4204_);
lean_ctor_set(v___x_3624_, 2, v_v_4208_);
lean_ctor_set(v___x_3624_, 1, v_k_4207_);
lean_ctor_set(v___x_3624_, 0, v___x_4213_);
v___x_4218_ = v___x_3624_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4213_);
lean_ctor_set(v_reuseFailAlloc_4219_, 1, v_k_4207_);
lean_ctor_set(v_reuseFailAlloc_4219_, 2, v_v_4208_);
lean_ctor_set(v_reuseFailAlloc_4219_, 3, v_l_4204_);
lean_ctor_set(v_reuseFailAlloc_4219_, 4, v___x_4216_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
else
{
lean_object* v_k_4224_; lean_object* v_v_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4236_; 
v_k_4224_ = lean_ctor_get(v_l_3621_, 1);
v_v_4225_ = lean_ctor_get(v_l_3621_, 2);
v_isSharedCheck_4236_ = !lean_is_exclusive(v_l_3621_);
if (v_isSharedCheck_4236_ == 0)
{
lean_object* v_unused_4237_; lean_object* v_unused_4238_; lean_object* v_unused_4239_; 
v_unused_4237_ = lean_ctor_get(v_l_3621_, 4);
lean_dec(v_unused_4237_);
v_unused_4238_ = lean_ctor_get(v_l_3621_, 3);
lean_dec(v_unused_4238_);
v_unused_4239_ = lean_ctor_get(v_l_3621_, 0);
lean_dec(v_unused_4239_);
v___x_4227_ = v_l_3621_;
v_isShared_4228_ = v_isSharedCheck_4236_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_v_4225_);
lean_inc(v_k_4224_);
lean_dec(v_l_3621_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4236_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4229_; lean_object* v___x_4231_; 
v___x_4229_ = lean_unsigned_to_nat(3u);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 3, v_r_4205_);
lean_ctor_set(v___x_4227_, 2, v_v_3620_);
lean_ctor_set(v___x_4227_, 1, v_k_3619_);
lean_ctor_set(v___x_4227_, 0, v___x_4113_);
v___x_4231_ = v___x_4227_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4113_);
lean_ctor_set(v_reuseFailAlloc_4235_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_4235_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_4235_, 3, v_r_4205_);
lean_ctor_set(v_reuseFailAlloc_4235_, 4, v_r_4205_);
v___x_4231_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
lean_object* v___x_4233_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 4, v___x_4231_);
lean_ctor_set(v___x_3624_, 3, v_l_4204_);
lean_ctor_set(v___x_3624_, 2, v_v_4225_);
lean_ctor_set(v___x_3624_, 1, v_k_4224_);
lean_ctor_set(v___x_3624_, 0, v___x_4229_);
v___x_4233_ = v___x_3624_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v___x_4229_);
lean_ctor_set(v_reuseFailAlloc_4234_, 1, v_k_4224_);
lean_ctor_set(v_reuseFailAlloc_4234_, 2, v_v_4225_);
lean_ctor_set(v_reuseFailAlloc_4234_, 3, v_l_4204_);
lean_ctor_set(v_reuseFailAlloc_4234_, 4, v___x_4231_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
}
}
else
{
lean_object* v_r_4240_; 
v_r_4240_ = lean_ctor_get(v_l_3621_, 4);
lean_inc(v_r_4240_);
if (lean_obj_tag(v_r_4240_) == 0)
{
lean_object* v_k_4241_; lean_object* v_v_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4265_; 
lean_inc(v_l_4204_);
v_k_4241_ = lean_ctor_get(v_l_3621_, 1);
v_v_4242_ = lean_ctor_get(v_l_3621_, 2);
v_isSharedCheck_4265_ = !lean_is_exclusive(v_l_3621_);
if (v_isSharedCheck_4265_ == 0)
{
lean_object* v_unused_4266_; lean_object* v_unused_4267_; lean_object* v_unused_4268_; 
v_unused_4266_ = lean_ctor_get(v_l_3621_, 4);
lean_dec(v_unused_4266_);
v_unused_4267_ = lean_ctor_get(v_l_3621_, 3);
lean_dec(v_unused_4267_);
v_unused_4268_ = lean_ctor_get(v_l_3621_, 0);
lean_dec(v_unused_4268_);
v___x_4244_ = v_l_3621_;
v_isShared_4245_ = v_isSharedCheck_4265_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_v_4242_);
lean_inc(v_k_4241_);
lean_dec(v_l_3621_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4265_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v_k_4246_; lean_object* v_v_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4261_; 
v_k_4246_ = lean_ctor_get(v_r_4240_, 1);
v_v_4247_ = lean_ctor_get(v_r_4240_, 2);
v_isSharedCheck_4261_ = !lean_is_exclusive(v_r_4240_);
if (v_isSharedCheck_4261_ == 0)
{
lean_object* v_unused_4262_; lean_object* v_unused_4263_; lean_object* v_unused_4264_; 
v_unused_4262_ = lean_ctor_get(v_r_4240_, 4);
lean_dec(v_unused_4262_);
v_unused_4263_ = lean_ctor_get(v_r_4240_, 3);
lean_dec(v_unused_4263_);
v_unused_4264_ = lean_ctor_get(v_r_4240_, 0);
lean_dec(v_unused_4264_);
v___x_4249_ = v_r_4240_;
v_isShared_4250_ = v_isSharedCheck_4261_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_v_4247_);
lean_inc(v_k_4246_);
lean_dec(v_r_4240_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4261_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4251_; lean_object* v___x_4253_; 
v___x_4251_ = lean_unsigned_to_nat(3u);
if (v_isShared_4250_ == 0)
{
lean_ctor_set(v___x_4249_, 4, v_l_4204_);
lean_ctor_set(v___x_4249_, 3, v_l_4204_);
lean_ctor_set(v___x_4249_, 2, v_v_4242_);
lean_ctor_set(v___x_4249_, 1, v_k_4241_);
lean_ctor_set(v___x_4249_, 0, v___x_4113_);
v___x_4253_ = v___x_4249_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v___x_4113_);
lean_ctor_set(v_reuseFailAlloc_4260_, 1, v_k_4241_);
lean_ctor_set(v_reuseFailAlloc_4260_, 2, v_v_4242_);
lean_ctor_set(v_reuseFailAlloc_4260_, 3, v_l_4204_);
lean_ctor_set(v_reuseFailAlloc_4260_, 4, v_l_4204_);
v___x_4253_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
lean_object* v___x_4255_; 
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 4, v_l_4204_);
lean_ctor_set(v___x_4244_, 2, v_v_3620_);
lean_ctor_set(v___x_4244_, 1, v_k_3619_);
lean_ctor_set(v___x_4244_, 0, v___x_4113_);
v___x_4255_ = v___x_4244_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v___x_4113_);
lean_ctor_set(v_reuseFailAlloc_4259_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_4259_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_4259_, 3, v_l_4204_);
lean_ctor_set(v_reuseFailAlloc_4259_, 4, v_l_4204_);
v___x_4255_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
lean_object* v___x_4257_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 4, v___x_4255_);
lean_ctor_set(v___x_3624_, 3, v___x_4253_);
lean_ctor_set(v___x_3624_, 2, v_v_4247_);
lean_ctor_set(v___x_3624_, 1, v_k_4246_);
lean_ctor_set(v___x_3624_, 0, v___x_4251_);
v___x_4257_ = v___x_3624_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v___x_4251_);
lean_ctor_set(v_reuseFailAlloc_4258_, 1, v_k_4246_);
lean_ctor_set(v_reuseFailAlloc_4258_, 2, v_v_4247_);
lean_ctor_set(v_reuseFailAlloc_4258_, 3, v___x_4253_);
lean_ctor_set(v_reuseFailAlloc_4258_, 4, v___x_4255_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
}
}
else
{
lean_object* v___x_4269_; lean_object* v___x_4271_; 
v___x_4269_ = lean_unsigned_to_nat(2u);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 4, v_r_4240_);
lean_ctor_set(v___x_3624_, 0, v___x_4269_);
v___x_4271_ = v___x_3624_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v___x_4269_);
lean_ctor_set(v_reuseFailAlloc_4272_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_4272_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_4272_, 3, v_l_3621_);
lean_ctor_set(v_reuseFailAlloc_4272_, 4, v_r_4240_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
}
else
{
lean_object* v___x_4274_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 4, v_l_3621_);
lean_ctor_set(v___x_3624_, 0, v___x_4113_);
v___x_4274_ = v___x_3624_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v___x_4113_);
lean_ctor_set(v_reuseFailAlloc_4275_, 1, v_k_3619_);
lean_ctor_set(v_reuseFailAlloc_4275_, 2, v_v_3620_);
lean_ctor_set(v_reuseFailAlloc_4275_, 3, v_l_3621_);
lean_ctor_set(v_reuseFailAlloc_4275_, 4, v_l_3621_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
}
}
}
else
{
return v_t_3618_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg___boxed(lean_object* v_k_4278_, lean_object* v_t_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(v_k_4278_, v_t_4279_);
lean_dec(v_k_4278_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1(lean_object* v_init_4281_, lean_object* v_x_4282_){
_start:
{
if (lean_obj_tag(v_x_4282_) == 0)
{
lean_object* v_k_4283_; lean_object* v_l_4284_; lean_object* v_r_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v_k_4283_ = lean_ctor_get(v_x_4282_, 1);
v_l_4284_ = lean_ctor_get(v_x_4282_, 3);
v_r_4285_ = lean_ctor_get(v_x_4282_, 4);
v___x_4286_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1(v_init_4281_, v_l_4284_);
v___x_4287_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(v_k_4283_, v___x_4286_);
v_init_4281_ = v___x_4287_;
v_x_4282_ = v_r_4285_;
goto _start;
}
else
{
return v_init_4281_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1___boxed(lean_object* v_init_4289_, lean_object* v_x_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1(v_init_4289_, v_x_4290_);
lean_dec(v_x_4290_);
return v_res_4291_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNon(lean_object* v_names_4292_, lean_object* v_maxSuggestions_4293_, double v_depthFactor_4294_, double v_frequencyWeight_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_){
_start:
{
lean_object* v___x_4301_; lean_object* v_env_4302_; lean_object* v___x_4303_; lean_object* v_toEnvExtension_4304_; lean_object* v_asyncMode_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
v___x_4301_ = lean_st_ref_get(v_a_4299_);
v_env_4302_ = lean_ctor_get(v___x_4301_, 0);
lean_inc_ref(v_env_4302_);
lean_dec(v___x_4301_);
v___x_4303_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerDenyListExt;
v_toEnvExtension_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc_ref(v_toEnvExtension_4304_);
v_asyncMode_4305_ = lean_ctor_get(v_toEnvExtension_4304_, 2);
lean_inc(v_asyncMode_4305_);
lean_dec_ref(v_toEnvExtension_4304_);
v___x_4306_ = lean_box(1);
v___x_4307_ = lean_box(0);
v___x_4308_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4306_, v___x_4303_, v_env_4302_, v_asyncMode_4305_, v___x_4307_);
lean_dec(v_asyncMode_4305_);
v___x_4309_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1(v_names_4292_, v___x_4308_);
v___x_4310_ = lean_box(0);
v___x_4311_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__7(v___x_4310_, v___x_4309_);
v___x_4312_ = l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg(v___x_4311_, v___x_4310_, v_a_4299_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; lean_object* v___f_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4313_);
lean_dec_ref(v___x_4312_);
v___f_4314_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___closed__0));
v___x_4315_ = l_Std_TreeSet_ofList___redArg(v_a_4313_, v___f_4314_);
v___x_4316_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1___closed__0));
v___x_4317_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go(v_maxSuggestions_4293_, v_depthFactor_4294_, v_frequencyWeight_4295_, v___x_4308_, v___x_4309_, v___x_4315_, v___x_4316_, v___x_4306_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_);
lean_dec(v___x_4308_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4328_; 
v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4320_ = v___x_4317_;
v_isShared_4321_ = v_isSharedCheck_4328_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4317_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4328_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
size_t v_sz_4322_; size_t v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4326_; 
v_sz_4322_ = lean_array_size(v_a_4318_);
v___x_4323_ = ((size_t)0ULL);
v___x_4324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3(v_sz_4322_, v___x_4323_, v_a_4318_);
if (v_isShared_4321_ == 0)
{
lean_ctor_set(v___x_4320_, 0, v___x_4324_);
v___x_4326_ = v___x_4320_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v___x_4324_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
return v___x_4326_;
}
}
}
else
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4336_; 
v_a_4329_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4331_ = v___x_4317_;
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4317_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4334_; 
if (v_isShared_4332_ == 0)
{
v___x_4334_ = v___x_4331_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
lean_dec(v___x_4309_);
lean_dec(v___x_4308_);
v_a_4337_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_4312_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4312_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNon___boxed(lean_object* v_names_4345_, lean_object* v_maxSuggestions_4346_, lean_object* v_depthFactor_4347_, lean_object* v_frequencyWeight_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_){
_start:
{
double v_depthFactor_boxed_4354_; double v_frequencyWeight_boxed_4355_; lean_object* v_res_4356_; 
v_depthFactor_boxed_4354_ = lean_unbox_float(v_depthFactor_4347_);
lean_dec_ref(v_depthFactor_4347_);
v_frequencyWeight_boxed_4355_ = lean_unbox_float(v_frequencyWeight_4348_);
lean_dec_ref(v_frequencyWeight_4348_);
v_res_4356_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNon(v_names_4345_, v_maxSuggestions_4346_, v_depthFactor_boxed_4354_, v_frequencyWeight_boxed_4355_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_);
lean_dec(v_a_4352_);
lean_dec_ref(v_a_4351_);
lean_dec(v_a_4350_);
lean_dec_ref(v_a_4349_);
lean_dec(v_maxSuggestions_4346_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0(lean_object* v_00_u03b2_4357_, lean_object* v_k_4358_, lean_object* v_t_4359_, lean_object* v_h_4360_){
_start:
{
lean_object* v___x_4361_; 
v___x_4361_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(v_k_4358_, v_t_4359_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___boxed(lean_object* v_00_u03b2_4362_, lean_object* v_k_4363_, lean_object* v_t_4364_, lean_object* v_h_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0(v_00_u03b2_4362_, v_k_4363_, v_t_4364_, v_h_4365_);
lean_dec(v_k_4363_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1(lean_object* v_init_4367_, lean_object* v_t_4368_){
_start:
{
lean_object* v___x_4369_; 
v___x_4369_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1(v_init_4367_, v_t_4368_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1___boxed(lean_object* v_init_4370_, lean_object* v_t_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1(v_init_4370_, v_t_4371_);
lean_dec(v_t_4371_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2(lean_object* v_x_4373_, lean_object* v_x_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
lean_object* v___x_4380_; 
v___x_4380_ = l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg(v_x_4373_, v_x_4374_, v___y_4378_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___boxed(lean_object* v_x_4381_, lean_object* v_x_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2(v_x_4381_, v_x_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
lean_dec(v___y_4386_);
lean_dec_ref(v___y_4385_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_sineQuaNonSelector(double v_depthFactor_4389_, lean_object* v_g_4390_, lean_object* v_config_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_){
_start:
{
lean_object* v___x_4397_; 
v___x_4397_ = l_Lean_MVarId_getRelevantConstants(v_g_4390_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_object* v_a_4398_; lean_object* v_maxSuggestions_4399_; double v___x_4400_; lean_object* v___x_4401_; 
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_a_4398_);
lean_dec_ref(v___x_4397_);
v_maxSuggestions_4399_ = lean_ctor_get(v_config_4391_, 0);
lean_inc(v_maxSuggestions_4399_);
lean_dec_ref(v_config_4391_);
v___x_4400_ = lean_float_once(&l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0, &l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0_once, _init_l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0);
v___x_4401_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNon(v_a_4398_, v_maxSuggestions_4399_, v_depthFactor_4389_, v___x_4400_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4411_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4404_ = v___x_4401_;
v_isShared_4405_ = v_isSharedCheck_4411_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4401_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4411_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4409_; 
v___x_4406_ = lean_unsigned_to_nat(0u);
v___x_4407_ = l_Array_extract___redArg(v_a_4402_, v___x_4406_, v_maxSuggestions_4399_);
lean_dec(v_a_4402_);
if (v_isShared_4405_ == 0)
{
lean_ctor_set(v___x_4404_, 0, v___x_4407_);
v___x_4409_ = v___x_4404_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v___x_4407_);
v___x_4409_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
return v___x_4409_;
}
}
}
else
{
lean_dec(v_maxSuggestions_4399_);
return v___x_4401_;
}
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
lean_dec_ref(v_config_4391_);
v_a_4412_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4397_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4397_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4417_; 
if (v_isShared_4415_ == 0)
{
v___x_4417_ = v___x_4414_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_sineQuaNonSelector___boxed(lean_object* v_depthFactor_4420_, lean_object* v_g_4421_, lean_object* v_config_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_){
_start:
{
double v_depthFactor_boxed_4428_; lean_object* v_res_4429_; 
v_depthFactor_boxed_4428_ = lean_unbox_float(v_depthFactor_4420_);
lean_dec_ref(v_depthFactor_4420_);
v_res_4429_ = l_Lean_LibrarySuggestions_sineQuaNonSelector(v_depthFactor_boxed_4428_, v_g_4421_, v_config_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_);
lean_dec(v_a_4426_);
lean_dec_ref(v_a_4425_);
lean_dec(v_a_4424_);
lean_dec_ref(v_a_4423_);
return v_res_4429_;
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
