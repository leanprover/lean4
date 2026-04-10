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
lean_object* lean_float_to_string(double);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_paren(lean_object*);
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
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Std_TreeSet_ofList___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
static const lean_array_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "sine qua non premise selection extension"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "sineQueNon"};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(67, 84, 59, 241, 113, 198, 42, 47)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value;
static const lean_array_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__7_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__6_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__8_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__9_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__7(lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__0_value;
static const lean_ctor_object l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__0_value)}};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__1_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__2;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__3;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg(double, double, double, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__4(double, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__0 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__0_value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__1 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__1_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__2;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "acceptedTheorems: "};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__3 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__3_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__4;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\npastTriggers: "};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__5 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__5_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__6;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\ntriggerQueue: "};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__7 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__7_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__8;
static const lean_string_object l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "\nqueuedTheorems: "};
static const lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__9 = (const lean_object*)&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__9_value;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__10;
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
v_asyncMode_521_ = lean_ctor_get(v_toEnvExtension_520_, 2);
v___x_522_ = lean_box(1);
v___x_523_ = lean_box(0);
v___x_524_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_522_, v___x_519_, v_env_518_, v_asyncMode_521_, v___x_523_);
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
v___x_845_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
lean_ctor_set(v___x_845_, 2, v___x_844_);
lean_ctor_set(v___x_845_, 3, v___x_844_);
lean_ctor_set(v___x_845_, 4, v___x_843_);
lean_ctor_set(v___x_845_, 5, v___x_843_);
lean_ctor_set(v___x_845_, 6, v___x_843_);
lean_ctor_set(v___x_845_, 7, v___x_843_);
lean_ctor_set(v___x_845_, 8, v___x_843_);
lean_ctor_set(v___x_845_, 9, v___x_843_);
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
double v___x_854__boxed_1429_; lean_object* v_res_1430_; 
v___x_854__boxed_1429_ = lean_unbox_float(v___x_1422_);
lean_dec_ref(v___x_1422_);
v_res_1430_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3___lam__0(v___x_1421_, v___x_854__boxed_1429_, v___x_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
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
lean_object* v___x_1551_; lean_object* v_map_u2082_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; size_t v_sz_1555_; size_t v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___f_1560_; lean_object* v_ents_1561_; lean_object* v___x_1562_; 
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
v_ents_1561_ = l___private_Lean_LibrarySuggestions_SymbolFrequency_0__Lean_Environment_unsafeRunMetaM___redArg(v___x_1553_, v_env_1550_, v___f_1560_);
lean_inc_n(v_ents_1561_, 2);
v___x_1562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1562_, 0, v_ents_1561_);
lean_ctor_set(v___x_1562_, 1, v_ents_1561_);
lean_ctor_set(v___x_1562_, 2, v_ents_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0(lean_object* v_00_u03b2_1563_, lean_object* v_m_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___redArg(v_m_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0___boxed(lean_object* v_00_u03b2_1566_, lean_object* v_m_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0(v_00_u03b2_1566_, v_m_1567_);
lean_dec_ref(v_m_1567_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0(lean_object* v_00_u03c3_1569_, lean_object* v_00_u03b2_1570_, lean_object* v_map_1571_, lean_object* v_f_1572_, lean_object* v_init_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___redArg(v_map_1571_, v_f_1572_, v_init_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0___boxed(lean_object* v_00_u03c3_1575_, lean_object* v_00_u03b2_1576_, lean_object* v_map_1577_, lean_object* v_f_1578_, lean_object* v_init_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0(v_00_u03c3_1575_, v_00_u03b2_1576_, v_map_1577_, v_f_1578_, v_init_1579_);
lean_dec_ref(v_map_1577_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1___redArg(lean_object* v_map_1581_, lean_object* v_f_1582_, lean_object* v_init_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1582_, v_map_1581_, v_init_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_1585_, lean_object* v_f_1586_, lean_object* v_init_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1___redArg(v_map_1585_, v_f_1586_, v_init_1587_);
lean_dec_ref(v_map_1585_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_1589_, lean_object* v_00_u03b2_1590_, lean_object* v_map_1591_, lean_object* v_f_1592_, lean_object* v_init_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1592_, v_map_1591_, v_init_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1595_, lean_object* v_00_u03b2_1596_, lean_object* v_map_1597_, lean_object* v_f_1598_, lean_object* v_init_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1(v_00_u03c3_1595_, v_00_u03b2_1596_, v_map_1597_, v_f_1598_, v_init_1599_);
lean_dec_ref(v_map_1597_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_1601_, lean_object* v_00_u03b1_1602_, lean_object* v_00_u03b2_1603_, lean_object* v_f_1604_, lean_object* v_x_1605_, lean_object* v_x_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1604_, v_x_1605_, v_x_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_1608_, lean_object* v_00_u03b1_1609_, lean_object* v_00_u03b2_1610_, lean_object* v_f_1611_, lean_object* v_x_1612_, lean_object* v_x_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_1608_, v_00_u03b1_1609_, v_00_u03b2_1610_, v_f_1611_, v_x_1612_, v_x_1613_);
lean_dec_ref(v_x_1612_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b1_1615_, lean_object* v_00_u03b2_1616_, lean_object* v_00_u03c3_1617_, lean_object* v_f_1618_, lean_object* v_as_1619_, size_t v_i_1620_, size_t v_stop_1621_, lean_object* v_b_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_f_1618_, v_as_1619_, v_i_1620_, v_stop_1621_, v_b_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1624_, lean_object* v_00_u03b2_1625_, lean_object* v_00_u03c3_1626_, lean_object* v_f_1627_, lean_object* v_as_1628_, lean_object* v_i_1629_, lean_object* v_stop_1630_, lean_object* v_b_1631_){
_start:
{
size_t v_i_boxed_1632_; size_t v_stop_boxed_1633_; lean_object* v_res_1634_; 
v_i_boxed_1632_ = lean_unbox_usize(v_i_1629_);
lean_dec(v_i_1629_);
v_stop_boxed_1633_ = lean_unbox_usize(v_stop_1630_);
lean_dec(v_stop_1630_);
v_res_1634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__4(v_00_u03b1_1624_, v_00_u03b2_1625_, v_00_u03c3_1626_, v_f_1627_, v_as_1628_, v_i_boxed_1632_, v_stop_boxed_1633_, v_b_1631_);
lean_dec_ref(v_as_1628_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03c3_1635_, lean_object* v_00_u03b1_1636_, lean_object* v_00_u03b2_1637_, lean_object* v_f_1638_, lean_object* v_keys_1639_, lean_object* v_vals_1640_, lean_object* v_heq_1641_, lean_object* v_i_1642_, lean_object* v_acc_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_f_1638_, v_keys_1639_, v_vals_1640_, v_i_1642_, v_acc_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03c3_1645_, lean_object* v_00_u03b1_1646_, lean_object* v_00_u03b2_1647_, lean_object* v_f_1648_, lean_object* v_keys_1649_, lean_object* v_vals_1650_, lean_object* v_heq_1651_, lean_object* v_i_1652_, lean_object* v_acc_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03c3_1645_, v_00_u03b1_1646_, v_00_u03b2_1647_, v_f_1648_, v_keys_1649_, v_vals_1650_, v_heq_1651_, v_i_1652_, v_acc_1653_);
lean_dec_ref(v_vals_1650_);
lean_dec_ref(v_keys_1649_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(lean_object* v_x_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = ((lean_object*)(l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_));
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed(lean_object* v_x_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__0_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(v_x_1659_);
lean_dec_ref(v_x_1659_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(lean_object* v_x_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = ((lean_object*)(l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_));
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed(lean_object* v_x_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(v_x_1666_);
lean_dec_ref(v_x_1666_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(lean_object* v_env_1668_, lean_object* v_x_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt_unsafe__3(v_env_1668_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed(lean_object* v_env_1671_, lean_object* v_x_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__2_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(v_env_1671_, v_x_1672_);
lean_dec_ref(v_x_1672_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(lean_object* v_a_1674_, uint8_t v_a_1675_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed(lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
uint8_t v_a_110__boxed_1678_; lean_object* v_res_1679_; 
v_a_110__boxed_1678_ = lean_unbox(v_a_1677_);
v_res_1679_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__3_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(v_a_1676_, v_a_110__boxed_1678_);
lean_dec_ref(v_a_1676_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(lean_object* v_mapss_1680_, lean_object* v_x_1681_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1683_, 0, v_mapss_1680_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed(lean_object* v_mapss_1684_, lean_object* v_x_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__4_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(v_mapss_1684_, v_x_1685_);
lean_dec_ref(v_x_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(lean_object* v___x_1688_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1688_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed(lean_object* v___x_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn___lam__5_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(v___x_1691_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l_Lean_LibrarySuggestions_SineQuaNon_initFn___closed__10_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_));
v___x_1720_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2____boxed(lean_object* v_a_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_();
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_228879371____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = lean_box(0);
v___x_1725_ = lean_st_mk_ref(v___x_1724_);
v___x_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_228879371____hygCtx___hyg_2____boxed(lean_object* v_a_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_228879371____hygCtx___hyg_2_();
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__0(lean_object* v_as_1729_, size_t v_i_1730_, size_t v_stop_1731_, lean_object* v_b_1732_){
_start:
{
uint8_t v___x_1733_; 
v___x_1733_ = lean_usize_dec_eq(v_i_1730_, v_stop_1731_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; size_t v___x_1736_; size_t v___x_1737_; 
v___x_1734_ = lean_array_uget_borrowed(v_as_1729_, v_i_1730_);
lean_inc(v___x_1734_);
v___x_1735_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_combineTriggers(v_b_1732_, v___x_1734_);
v___x_1736_ = ((size_t)1ULL);
v___x_1737_ = lean_usize_add(v_i_1730_, v___x_1736_);
v_i_1730_ = v___x_1737_;
v_b_1732_ = v___x_1735_;
goto _start;
}
else
{
return v_b_1732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__0___boxed(lean_object* v_as_1739_, lean_object* v_i_1740_, lean_object* v_stop_1741_, lean_object* v_b_1742_){
_start:
{
size_t v_i_boxed_1743_; size_t v_stop_boxed_1744_; lean_object* v_res_1745_; 
v_i_boxed_1743_ = lean_unbox_usize(v_i_1740_);
lean_dec(v_i_1740_);
v_stop_boxed_1744_ = lean_unbox_usize(v_stop_1741_);
lean_dec(v_stop_1741_);
v_res_1745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__0(v_as_1739_, v_i_boxed_1743_, v_stop_boxed_1744_, v_b_1742_);
lean_dec_ref(v_as_1739_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__1(lean_object* v_as_1746_, size_t v_i_1747_, size_t v_stop_1748_, lean_object* v_b_1749_){
_start:
{
lean_object* v___y_1751_; uint8_t v___x_1755_; 
v___x_1755_ = lean_usize_dec_eq(v_i_1747_, v_stop_1748_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1756_ = lean_array_uget_borrowed(v_as_1746_, v_i_1747_);
v___x_1757_ = lean_unsigned_to_nat(0u);
v___x_1758_ = lean_array_get_size(v___x_1756_);
v___x_1759_ = lean_nat_dec_lt(v___x_1757_, v___x_1758_);
if (v___x_1759_ == 0)
{
v___y_1751_ = v_b_1749_;
goto v___jp_1750_;
}
else
{
uint8_t v___x_1760_; 
v___x_1760_ = lean_nat_dec_le(v___x_1758_, v___x_1758_);
if (v___x_1760_ == 0)
{
if (v___x_1759_ == 0)
{
v___y_1751_ = v_b_1749_;
goto v___jp_1750_;
}
else
{
size_t v___x_1761_; size_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = ((size_t)0ULL);
v___x_1762_ = lean_usize_of_nat(v___x_1758_);
v___x_1763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__0(v___x_1756_, v___x_1761_, v___x_1762_, v_b_1749_);
v___y_1751_ = v___x_1763_;
goto v___jp_1750_;
}
}
else
{
size_t v___x_1764_; size_t v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = ((size_t)0ULL);
v___x_1765_ = lean_usize_of_nat(v___x_1758_);
v___x_1766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__0(v___x_1756_, v___x_1764_, v___x_1765_, v_b_1749_);
v___y_1751_ = v___x_1766_;
goto v___jp_1750_;
}
}
}
else
{
return v_b_1749_;
}
v___jp_1750_:
{
size_t v___x_1752_; size_t v___x_1753_; 
v___x_1752_ = ((size_t)1ULL);
v___x_1753_ = lean_usize_add(v_i_1747_, v___x_1752_);
v_i_1747_ = v___x_1753_;
v_b_1749_ = v___y_1751_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__1___boxed(lean_object* v_as_1767_, lean_object* v_i_1768_, lean_object* v_stop_1769_, lean_object* v_b_1770_){
_start:
{
size_t v_i_boxed_1771_; size_t v_stop_boxed_1772_; lean_object* v_res_1773_; 
v_i_boxed_1771_ = lean_unbox_usize(v_i_1768_);
lean_dec(v_i_1768_);
v_stop_boxed_1772_ = lean_unbox_usize(v_stop_1769_);
lean_dec(v_stop_1769_);
v_res_1773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__1(v_as_1767_, v_i_boxed_1771_, v_stop_boxed_1772_, v_b_1770_);
lean_dec_ref(v_as_1767_);
return v_res_1773_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___closed__0(void){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Array_instInhabited(lean_box(0));
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg(lean_object* v_a_1775_){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersRef;
v___x_1778_ = lean_st_ref_get(v___x_1777_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v___x_1779_; lean_object* v___y_1781_; lean_object* v_env_1785_; lean_object* v___x_1786_; lean_object* v_toEnvExtension_1787_; lean_object* v_asyncMode_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1779_ = lean_st_ref_get(v_a_1775_);
v_env_1785_ = lean_ctor_get(v___x_1779_, 0);
lean_inc_ref(v_env_1785_);
lean_dec(v___x_1779_);
v___x_1786_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonExt;
v_toEnvExtension_1787_ = lean_ctor_get(v___x_1786_, 0);
v_asyncMode_1788_ = lean_ctor_get(v_toEnvExtension_1787_, 2);
v___x_1789_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___closed__0, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___closed__0_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___closed__0);
v___x_1790_ = lean_box(0);
v___x_1791_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1789_, v___x_1786_, v_env_1785_, v_asyncMode_1788_, v___x_1790_);
v___x_1792_ = lean_box(1);
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_array_get_size(v___x_1791_);
v___x_1795_ = lean_nat_dec_lt(v___x_1793_, v___x_1794_);
if (v___x_1795_ == 0)
{
lean_dec(v___x_1791_);
v___y_1781_ = v___x_1792_;
goto v___jp_1780_;
}
else
{
uint8_t v___x_1796_; 
v___x_1796_ = lean_nat_dec_le(v___x_1794_, v___x_1794_);
if (v___x_1796_ == 0)
{
if (v___x_1795_ == 0)
{
lean_dec(v___x_1791_);
v___y_1781_ = v___x_1792_;
goto v___jp_1780_;
}
else
{
size_t v___x_1797_; size_t v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = ((size_t)0ULL);
v___x_1798_ = lean_usize_of_nat(v___x_1794_);
v___x_1799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__1(v___x_1791_, v___x_1797_, v___x_1798_, v___x_1792_);
lean_dec(v___x_1791_);
v___y_1781_ = v___x_1799_;
goto v___jp_1780_;
}
}
else
{
size_t v___x_1800_; size_t v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = ((size_t)0ULL);
v___x_1801_ = lean_usize_of_nat(v___x_1794_);
v___x_1802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap_spec__1(v___x_1791_, v___x_1800_, v___x_1801_, v___x_1792_);
lean_dec(v___x_1791_);
v___y_1781_ = v___x_1802_;
goto v___jp_1780_;
}
}
v___jp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_inc(v___y_1781_);
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___y_1781_);
v___x_1783_ = lean_st_ref_set(v___x_1777_, v___x_1782_);
v___x_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___y_1781_);
return v___x_1784_;
}
}
else
{
lean_object* v_val_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
v_val_1803_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1778_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_val_1803_);
lean_dec(v___x_1778_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set_tag(v___x_1805_, 0);
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_val_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg___boxed(lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg(v_a_1811_);
lean_dec(v_a_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap(lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg(v_a_1815_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___boxed(lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap(v_a_1818_, v_a_1819_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___redArg(lean_object* v_trigger_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v___x_1825_; lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1835_; 
v___x_1825_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg(v_a_1823_);
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1835_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1835_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1830_ = lean_box(0);
v___x_1831_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_localSymbolFrequency_spec__0___redArg(v_a_1826_, v_trigger_1822_, v___x_1830_);
lean_dec(v_a_1826_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1831_);
v___x_1833_ = v___x_1828_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___redArg___boxed(lean_object* v_trigger_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___redArg(v_trigger_1836_, v_a_1837_);
lean_dec(v_a_1837_);
lean_dec(v_trigger_1836_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems(lean_object* v_trigger_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___redArg(v_trigger_1840_, v_a_1842_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___boxed(lean_object* v_trigger_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems(v_trigger_1845_, v_a_1846_, v_a_1847_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
lean_dec(v_trigger_1845_);
return v_res_1849_;
}
}
LEAN_EXPORT uint8_t l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1___lam__0(lean_object* v_decl_1850_, lean_object* v_x_1851_){
_start:
{
lean_object* v_fst_1852_; uint8_t v___x_1853_; 
v_fst_1852_ = lean_ctor_get(v_x_1851_, 0);
v___x_1853_ = lean_name_eq(v_fst_1852_, v_decl_1850_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1___lam__0___boxed(lean_object* v_decl_1854_, lean_object* v_x_1855_){
_start:
{
uint8_t v_res_1856_; lean_object* v_r_1857_; 
v_res_1856_ = l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1___lam__0(v_decl_1854_, v_x_1855_);
lean_dec_ref(v_x_1855_);
lean_dec(v_decl_1854_);
v_r_1857_ = lean_box(v_res_1856_);
return v_r_1857_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1(lean_object* v_decl_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
if (lean_obj_tag(v_a_1859_) == 0)
{
lean_object* v___x_1861_; 
lean_dec(v_decl_1858_);
v___x_1861_ = lean_array_to_list(v_a_1860_);
return v___x_1861_;
}
else
{
lean_object* v_head_1862_; lean_object* v_tail_1863_; lean_object* v_val_1865_; lean_object* v_fst_1868_; lean_object* v_snd_1869_; lean_object* v___f_1870_; lean_object* v___x_1871_; 
v_head_1862_ = lean_ctor_get(v_a_1859_, 0);
lean_inc(v_head_1862_);
v_tail_1863_ = lean_ctor_get(v_a_1859_, 1);
lean_inc(v_tail_1863_);
lean_dec_ref(v_a_1859_);
v_fst_1868_ = lean_ctor_get(v_head_1862_, 0);
lean_inc(v_fst_1868_);
v_snd_1869_ = lean_ctor_get(v_head_1862_, 1);
lean_inc(v_snd_1869_);
lean_dec(v_head_1862_);
lean_inc(v_decl_1858_);
v___f_1870_ = lean_alloc_closure((void*)(l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1870_, 0, v_decl_1858_);
v___x_1871_ = l_List_find_x3f___redArg(v___f_1870_, v_snd_1869_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_dec(v_fst_1868_);
if (lean_obj_tag(v___x_1871_) == 0)
{
v_a_1859_ = v_tail_1863_;
goto _start;
}
else
{
lean_object* v_val_1873_; 
v_val_1873_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_val_1873_);
lean_dec_ref(v___x_1871_);
v_val_1865_ = v_val_1873_;
goto v___jp_1864_;
}
}
else
{
lean_object* v_val_1874_; lean_object* v_snd_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
v_val_1874_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_val_1874_);
lean_dec_ref(v___x_1871_);
v_snd_1875_ = lean_ctor_get(v_val_1874_, 1);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_val_1874_);
if (v_isSharedCheck_1882_ == 0)
{
lean_object* v_unused_1883_; 
v_unused_1883_ = lean_ctor_get(v_val_1874_, 0);
lean_dec(v_unused_1883_);
v___x_1877_ = v_val_1874_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_snd_1875_);
lean_dec(v_val_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v_fst_1868_);
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_fst_1868_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_snd_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
v_val_1865_ = v___x_1880_;
goto v___jp_1864_;
}
}
}
v___jp_1864_:
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_array_push(v_a_1860_, v_val_1865_);
v_a_1859_ = v_tail_1863_;
v_a_1860_ = v___x_1866_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__0(lean_object* v_init_1884_, lean_object* v_x_1885_){
_start:
{
if (lean_obj_tag(v_x_1885_) == 0)
{
lean_object* v_k_1886_; lean_object* v_v_1887_; lean_object* v_l_1888_; lean_object* v_r_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_k_1886_ = lean_ctor_get(v_x_1885_, 1);
v_v_1887_ = lean_ctor_get(v_x_1885_, 2);
v_l_1888_ = lean_ctor_get(v_x_1885_, 3);
v_r_1889_ = lean_ctor_get(v_x_1885_, 4);
v___x_1890_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__0(v_init_1884_, v_r_1889_);
lean_inc(v_v_1887_);
lean_inc(v_k_1886_);
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v_k_1886_);
lean_ctor_set(v___x_1891_, 1, v_v_1887_);
v___x_1892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
lean_ctor_set(v___x_1892_, 1, v___x_1890_);
v_init_1884_ = v___x_1892_;
v_x_1885_ = v_l_1888_;
goto _start;
}
else
{
return v_init_1884_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__0___boxed(lean_object* v_init_1894_, lean_object* v_x_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__0(v_init_1894_, v_x_1895_);
lean_dec(v_x_1895_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___redArg(lean_object* v_decl_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v___x_1900_; lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1912_; 
v___x_1900_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggerMap___redArg(v_a_1898_);
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1912_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1912_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1905_ = lean_box(0);
v___x_1906_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__0(v___x_1905_, v_a_1901_);
lean_dec(v_a_1901_);
v___x_1907_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1___closed__0));
v___x_1908_ = l_List_filterMapTR_go___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor_spec__1(v_decl_1897_, v___x_1906_, v___x_1907_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1908_);
v___x_1910_ = v___x_1903_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___redArg___boxed(lean_object* v_decl_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___redArg(v_decl_1913_, v_a_1914_);
lean_dec(v_a_1914_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor(lean_object* v_decl_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___redArg(v_decl_1917_, v_a_1919_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor___boxed(lean_object* v_decl_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTriggersFor(v_decl_1922_, v_a_1923_, v_a_1924_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
return v_res_1926_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___lam__0(lean_object* v_x_1927_, lean_object* v_y_1928_){
_start:
{
lean_object* v_fst_1929_; lean_object* v_snd_1930_; lean_object* v_fst_1931_; lean_object* v_snd_1932_; double v___x_1933_; double v___x_1934_; uint8_t v___x_1935_; 
v_fst_1929_ = lean_ctor_get(v_x_1927_, 0);
v_snd_1930_ = lean_ctor_get(v_x_1927_, 1);
v_fst_1931_ = lean_ctor_get(v_y_1928_, 0);
v_snd_1932_ = lean_ctor_get(v_y_1928_, 1);
v___x_1933_ = lean_unbox_float(v_fst_1929_);
v___x_1934_ = lean_unbox_float(v_fst_1931_);
v___x_1935_ = lean_float_decLt(v___x_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
double v___x_1936_; double v___x_1937_; uint8_t v___x_1938_; 
v___x_1936_ = lean_unbox_float(v_fst_1931_);
v___x_1937_ = lean_unbox_float(v_fst_1929_);
v___x_1938_ = lean_float_decLt(v___x_1936_, v___x_1937_);
if (v___x_1938_ == 0)
{
uint8_t v___x_1939_; 
v___x_1939_ = l_Lean_Name_cmp(v_snd_1930_, v_snd_1932_);
return v___x_1939_;
}
else
{
uint8_t v___x_1940_; 
v___x_1940_ = 2;
return v___x_1940_;
}
}
else
{
uint8_t v___x_1941_; 
v___x_1941_ = 0;
return v___x_1941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___lam__0___boxed(lean_object* v_x_1942_, lean_object* v_y_1943_){
_start:
{
uint8_t v_res_1944_; lean_object* v_r_1945_; 
v_res_1944_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___lam__0(v_x_1942_, v_y_1943_);
lean_dec_ref(v_y_1943_);
lean_dec_ref(v_x_1942_);
v_r_1945_ = lean_box(v_res_1944_);
return v_r_1945_;
}
}
static double _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___closed__0(void){
_start:
{
lean_object* v___x_1948_; uint8_t v___x_1949_; lean_object* v___x_1950_; double v___x_1951_; 
v___x_1948_ = lean_unsigned_to_nat(1u);
v___x_1949_ = 1;
v___x_1950_ = lean_unsigned_to_nat(10u);
v___x_1951_ = l_Float_ofScientific(v___x_1950_, v___x_1949_, v___x_1948_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg(lean_object* v_n_1952_, double v_frequencyWeight_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = l_Lean_LibrarySuggestions_symbolFrequency___redArg(v_n_1952_, v_a_1954_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1972_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_1972_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1972_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; double v___x_1962_; lean_object* v___x_1963_; double v___x_1964_; double v___x_1965_; double v___x_1966_; double v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1961_ = lean_unsigned_to_nat(1u);
v___x_1962_ = lean_float_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___closed__0, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___closed__0_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___closed__0);
v___x_1963_ = lean_nat_add(v_a_1957_, v___x_1961_);
lean_dec(v_a_1957_);
v___x_1964_ = lean_float_of_nat(v___x_1963_);
v___x_1965_ = log2(v___x_1964_);
v___x_1966_ = lean_float_mul(v_frequencyWeight_1953_, v___x_1965_);
v___x_1967_ = lean_float_add(v___x_1962_, v___x_1966_);
v___x_1968_ = lean_box_float(v___x_1967_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1968_);
v___x_1970_ = v___x_1959_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
v_a_1973_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1956_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1956_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg___boxed(lean_object* v_n_1981_, lean_object* v_frequencyWeight_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
double v_frequencyWeight_boxed_1985_; lean_object* v_res_1986_; 
v_frequencyWeight_boxed_1985_ = lean_unbox_float(v_frequencyWeight_1982_);
lean_dec_ref(v_frequencyWeight_1982_);
v_res_1986_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg(v_n_1981_, v_frequencyWeight_boxed_1985_, v_a_1983_);
lean_dec(v_a_1983_);
lean_dec(v_n_1981_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore(lean_object* v_n_1987_, double v_frequencyWeight_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg(v_n_1987_, v_frequencyWeight_1988_, v_a_1992_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___boxed(lean_object* v_n_1995_, lean_object* v_frequencyWeight_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
double v_frequencyWeight_boxed_2002_; lean_object* v_res_2003_; 
v_frequencyWeight_boxed_2002_ = lean_unbox_float(v_frequencyWeight_1996_);
lean_dec_ref(v_frequencyWeight_1996_);
v_res_2003_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore(v_n_1995_, v_frequencyWeight_boxed_2002_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec(v_n_1995_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__7(lean_object* v_a_2004_, lean_object* v_a_2005_){
_start:
{
if (lean_obj_tag(v_a_2004_) == 0)
{
lean_object* v___x_2006_; 
v___x_2006_ = l_List_reverse___redArg(v_a_2005_);
return v___x_2006_;
}
else
{
lean_object* v_head_2007_; lean_object* v_tail_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2017_; 
v_head_2007_ = lean_ctor_get(v_a_2004_, 0);
v_tail_2008_ = lean_ctor_get(v_a_2004_, 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_a_2004_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2010_ = v_a_2004_;
v_isShared_2011_ = v_isSharedCheck_2017_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_tail_2008_);
lean_inc(v_head_2007_);
lean_dec(v_a_2004_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2017_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2012_ = l_Lean_MessageData_ofName(v_head_2007_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v_a_2005_);
lean_ctor_set(v___x_2010_, 0, v___x_2012_);
v___x_2014_ = v___x_2010_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_a_2005_);
v___x_2014_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
v_a_2004_ = v_tail_2008_;
v_a_2005_ = v___x_2014_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__1));
v___x_2022_ = l_Lean_MessageData_ofFormat(v___x_2021_);
return v___x_2022_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__3(void){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = lean_box(1);
v___x_2024_ = l_Lean_MessageData_ofFormat(v___x_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5(lean_object* v_a_2025_, lean_object* v_a_2026_){
_start:
{
if (lean_obj_tag(v_a_2025_) == 0)
{
lean_object* v___x_2027_; 
v___x_2027_ = l_List_reverse___redArg(v_a_2026_);
return v___x_2027_;
}
else
{
lean_object* v_head_2028_; lean_object* v_tail_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2056_; 
v_head_2028_ = lean_ctor_get(v_a_2025_, 0);
v_tail_2029_ = lean_ctor_get(v_a_2025_, 1);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_a_2025_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2031_ = v_a_2025_;
v_isShared_2032_ = v_isSharedCheck_2056_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_tail_2029_);
lean_inc(v_head_2028_);
lean_dec(v_a_2025_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2056_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v_fst_2033_; lean_object* v_snd_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2055_; 
v_fst_2033_ = lean_ctor_get(v_head_2028_, 0);
v_snd_2034_ = lean_ctor_get(v_head_2028_, 1);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_head_2028_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2036_ = v_head_2028_;
v_isShared_2037_ = v_isSharedCheck_2055_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_snd_2034_);
lean_inc(v_fst_2033_);
lean_dec(v_head_2028_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2055_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2038_ = l_Lean_MessageData_ofName(v_fst_2033_);
v___x_2039_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__2, &l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__2);
if (v_isShared_2037_ == 0)
{
lean_ctor_set_tag(v___x_2036_, 7);
lean_ctor_set(v___x_2036_, 1, v___x_2039_);
lean_ctor_set(v___x_2036_, 0, v___x_2038_);
v___x_2041_ = v___x_2036_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; double v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2051_; 
v___x_2042_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__3, &l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__3);
v___x_2043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2041_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = lean_unbox_float(v_snd_2034_);
lean_dec(v_snd_2034_);
v___x_2045_ = lean_float_to_string(v___x_2044_);
v___x_2046_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
v___x_2047_ = l_Lean_MessageData_ofFormat(v___x_2046_);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2043_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
v___x_2049_ = l_Lean_MessageData_paren(v___x_2048_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 1, v_a_2026_);
lean_ctor_set(v___x_2031_, 0, v___x_2049_);
v___x_2051_ = v___x_2031_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_a_2026_);
v___x_2051_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
v_a_2025_ = v_tail_2029_;
v_a_2026_ = v___x_2051_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(lean_object* v_k_2057_, lean_object* v_t_2058_){
_start:
{
lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; 
if (lean_obj_tag(v_t_2058_) == 0)
{
lean_object* v_k_2073_; lean_object* v_v_2074_; lean_object* v_l_2075_; lean_object* v_r_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2719_; 
v_k_2073_ = lean_ctor_get(v_t_2058_, 1);
v_v_2074_ = lean_ctor_get(v_t_2058_, 2);
v_l_2075_ = lean_ctor_get(v_t_2058_, 3);
v_r_2076_ = lean_ctor_get(v_t_2058_, 4);
v_isSharedCheck_2719_ = !lean_is_exclusive(v_t_2058_);
if (v_isSharedCheck_2719_ == 0)
{
lean_object* v_unused_2720_; 
v_unused_2720_ = lean_ctor_get(v_t_2058_, 0);
lean_dec(v_unused_2720_);
v___x_2078_ = v_t_2058_;
v_isShared_2079_ = v_isSharedCheck_2719_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_r_2076_);
lean_inc(v_l_2075_);
lean_inc(v_v_2074_);
lean_inc(v_k_2073_);
lean_dec(v_t_2058_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2719_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v_fst_2397_; lean_object* v_snd_2398_; lean_object* v_fst_2399_; lean_object* v_snd_2400_; double v___x_2401_; double v___x_2402_; uint8_t v___x_2403_; 
v_fst_2397_ = lean_ctor_get(v_k_2057_, 0);
v_snd_2398_ = lean_ctor_get(v_k_2057_, 1);
v_fst_2399_ = lean_ctor_get(v_k_2073_, 0);
v_snd_2400_ = lean_ctor_get(v_k_2073_, 1);
v___x_2401_ = lean_unbox_float(v_fst_2397_);
v___x_2402_ = lean_unbox_float(v_fst_2399_);
v___x_2403_ = lean_float_decLt(v___x_2401_, v___x_2402_);
if (v___x_2403_ == 0)
{
double v___x_2404_; double v___x_2405_; uint8_t v___x_2406_; 
v___x_2404_ = lean_unbox_float(v_fst_2399_);
v___x_2405_ = lean_unbox_float(v_fst_2397_);
v___x_2406_ = lean_float_decLt(v___x_2404_, v___x_2405_);
if (v___x_2406_ == 0)
{
uint8_t v___x_2407_; 
v___x_2407_ = l_Lean_Name_cmp(v_snd_2398_, v_snd_2400_);
switch(v___x_2407_)
{
case 0:
{
lean_del_object(v___x_2078_);
goto v___jp_2265_;
}
case 1:
{
lean_del_object(v___x_2078_);
lean_dec(v_v_2074_);
lean_dec(v_k_2073_);
if (lean_obj_tag(v_l_2075_) == 0)
{
if (lean_obj_tag(v_r_2076_) == 0)
{
lean_object* v_size_2408_; lean_object* v_k_2409_; lean_object* v_v_2410_; lean_object* v_l_2411_; lean_object* v_r_2412_; lean_object* v_size_2413_; lean_object* v_k_2414_; lean_object* v_v_2415_; lean_object* v_l_2416_; lean_object* v_r_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; 
v_size_2408_ = lean_ctor_get(v_l_2075_, 0);
v_k_2409_ = lean_ctor_get(v_l_2075_, 1);
v_v_2410_ = lean_ctor_get(v_l_2075_, 2);
v_l_2411_ = lean_ctor_get(v_l_2075_, 3);
v_r_2412_ = lean_ctor_get(v_l_2075_, 4);
lean_inc(v_r_2412_);
v_size_2413_ = lean_ctor_get(v_r_2076_, 0);
v_k_2414_ = lean_ctor_get(v_r_2076_, 1);
v_v_2415_ = lean_ctor_get(v_r_2076_, 2);
v_l_2416_ = lean_ctor_get(v_r_2076_, 3);
lean_inc(v_l_2416_);
v_r_2417_ = lean_ctor_get(v_r_2076_, 4);
v___x_2418_ = lean_unsigned_to_nat(1u);
v___x_2419_ = lean_nat_dec_lt(v_size_2408_, v_size_2413_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2555_; 
lean_inc(v_l_2411_);
lean_inc(v_v_2410_);
lean_inc(v_k_2409_);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_l_2075_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; lean_object* v_unused_2557_; lean_object* v_unused_2558_; lean_object* v_unused_2559_; lean_object* v_unused_2560_; 
v_unused_2556_ = lean_ctor_get(v_l_2075_, 4);
lean_dec(v_unused_2556_);
v_unused_2557_ = lean_ctor_get(v_l_2075_, 3);
lean_dec(v_unused_2557_);
v_unused_2558_ = lean_ctor_get(v_l_2075_, 2);
lean_dec(v_unused_2558_);
v_unused_2559_ = lean_ctor_get(v_l_2075_, 1);
lean_dec(v_unused_2559_);
v_unused_2560_ = lean_ctor_get(v_l_2075_, 0);
lean_dec(v_unused_2560_);
v___x_2421_ = v_l_2075_;
v_isShared_2422_ = v_isSharedCheck_2555_;
goto v_resetjp_2420_;
}
else
{
lean_dec(v_l_2075_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2555_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2423_; lean_object* v_tree_2424_; 
v___x_2423_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2409_, v_v_2410_, v_l_2411_, v_r_2412_);
v_tree_2424_ = lean_ctor_get(v___x_2423_, 2);
lean_inc(v_tree_2424_);
if (lean_obj_tag(v_tree_2424_) == 0)
{
lean_object* v_k_2425_; lean_object* v_v_2426_; lean_object* v_size_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; uint8_t v___x_2430_; 
v_k_2425_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_k_2425_);
v_v_2426_ = lean_ctor_get(v___x_2423_, 1);
lean_inc(v_v_2426_);
lean_dec_ref(v___x_2423_);
v_size_2427_ = lean_ctor_get(v_tree_2424_, 0);
v___x_2428_ = lean_unsigned_to_nat(3u);
v___x_2429_ = lean_nat_mul(v___x_2428_, v_size_2427_);
v___x_2430_ = lean_nat_dec_lt(v___x_2429_, v_size_2413_);
lean_dec(v___x_2429_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2434_; 
lean_dec(v_l_2416_);
v___x_2431_ = lean_nat_add(v___x_2418_, v_size_2427_);
v___x_2432_ = lean_nat_add(v___x_2431_, v_size_2413_);
lean_dec(v___x_2431_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v_r_2076_);
lean_ctor_set(v___x_2421_, 3, v_tree_2424_);
lean_ctor_set(v___x_2421_, 2, v_v_2426_);
lean_ctor_set(v___x_2421_, 1, v_k_2425_);
lean_ctor_set(v___x_2421_, 0, v___x_2432_);
v___x_2434_ = v___x_2421_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v_k_2425_);
lean_ctor_set(v_reuseFailAlloc_2435_, 2, v_v_2426_);
lean_ctor_set(v_reuseFailAlloc_2435_, 3, v_tree_2424_);
lean_ctor_set(v_reuseFailAlloc_2435_, 4, v_r_2076_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
else
{
lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2490_; 
lean_inc(v_r_2417_);
lean_inc(v_v_2415_);
lean_inc(v_k_2414_);
lean_inc(v_size_2413_);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_r_2076_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; lean_object* v_unused_2492_; lean_object* v_unused_2493_; lean_object* v_unused_2494_; lean_object* v_unused_2495_; 
v_unused_2491_ = lean_ctor_get(v_r_2076_, 4);
lean_dec(v_unused_2491_);
v_unused_2492_ = lean_ctor_get(v_r_2076_, 3);
lean_dec(v_unused_2492_);
v_unused_2493_ = lean_ctor_get(v_r_2076_, 2);
lean_dec(v_unused_2493_);
v_unused_2494_ = lean_ctor_get(v_r_2076_, 1);
lean_dec(v_unused_2494_);
v_unused_2495_ = lean_ctor_get(v_r_2076_, 0);
lean_dec(v_unused_2495_);
v___x_2437_ = v_r_2076_;
v_isShared_2438_ = v_isSharedCheck_2490_;
goto v_resetjp_2436_;
}
else
{
lean_dec(v_r_2076_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2490_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v_size_2439_; lean_object* v_k_2440_; lean_object* v_v_2441_; lean_object* v_l_2442_; lean_object* v_r_2443_; lean_object* v_size_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; 
v_size_2439_ = lean_ctor_get(v_l_2416_, 0);
v_k_2440_ = lean_ctor_get(v_l_2416_, 1);
v_v_2441_ = lean_ctor_get(v_l_2416_, 2);
v_l_2442_ = lean_ctor_get(v_l_2416_, 3);
v_r_2443_ = lean_ctor_get(v_l_2416_, 4);
v_size_2444_ = lean_ctor_get(v_r_2417_, 0);
v___x_2445_ = lean_unsigned_to_nat(2u);
v___x_2446_ = lean_nat_mul(v___x_2445_, v_size_2444_);
v___x_2447_ = lean_nat_dec_lt(v_size_2439_, v___x_2446_);
lean_dec(v___x_2446_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2475_; 
lean_inc(v_r_2443_);
lean_inc(v_l_2442_);
lean_inc(v_v_2441_);
lean_inc(v_k_2440_);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_l_2416_);
if (v_isSharedCheck_2475_ == 0)
{
lean_object* v_unused_2476_; lean_object* v_unused_2477_; lean_object* v_unused_2478_; lean_object* v_unused_2479_; lean_object* v_unused_2480_; 
v_unused_2476_ = lean_ctor_get(v_l_2416_, 4);
lean_dec(v_unused_2476_);
v_unused_2477_ = lean_ctor_get(v_l_2416_, 3);
lean_dec(v_unused_2477_);
v_unused_2478_ = lean_ctor_get(v_l_2416_, 2);
lean_dec(v_unused_2478_);
v_unused_2479_ = lean_ctor_get(v_l_2416_, 1);
lean_dec(v_unused_2479_);
v_unused_2480_ = lean_ctor_get(v_l_2416_, 0);
lean_dec(v_unused_2480_);
v___x_2449_ = v_l_2416_;
v_isShared_2450_ = v_isSharedCheck_2475_;
goto v_resetjp_2448_;
}
else
{
lean_dec(v_l_2416_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2475_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2465_; 
v___x_2451_ = lean_nat_add(v___x_2418_, v_size_2427_);
v___x_2452_ = lean_nat_add(v___x_2451_, v_size_2413_);
lean_dec(v_size_2413_);
if (lean_obj_tag(v_l_2442_) == 0)
{
lean_object* v_size_2473_; 
v_size_2473_ = lean_ctor_get(v_l_2442_, 0);
lean_inc(v_size_2473_);
v___y_2465_ = v_size_2473_;
goto v___jp_2464_;
}
else
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_unsigned_to_nat(0u);
v___y_2465_ = v___x_2474_;
goto v___jp_2464_;
}
v___jp_2453_:
{
lean_object* v___x_2457_; lean_object* v___x_2459_; 
v___x_2457_ = lean_nat_add(v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec(v___y_2455_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 4, v_r_2417_);
lean_ctor_set(v___x_2449_, 3, v_r_2443_);
lean_ctor_set(v___x_2449_, 2, v_v_2415_);
lean_ctor_set(v___x_2449_, 1, v_k_2414_);
lean_ctor_set(v___x_2449_, 0, v___x_2457_);
v___x_2459_ = v___x_2449_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v_k_2414_);
lean_ctor_set(v_reuseFailAlloc_2463_, 2, v_v_2415_);
lean_ctor_set(v_reuseFailAlloc_2463_, 3, v_r_2443_);
lean_ctor_set(v_reuseFailAlloc_2463_, 4, v_r_2417_);
v___x_2459_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
lean_object* v___x_2461_; 
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 4, v___x_2459_);
lean_ctor_set(v___x_2437_, 3, v___y_2454_);
lean_ctor_set(v___x_2437_, 2, v_v_2441_);
lean_ctor_set(v___x_2437_, 1, v_k_2440_);
lean_ctor_set(v___x_2437_, 0, v___x_2452_);
v___x_2461_ = v___x_2437_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v_k_2440_);
lean_ctor_set(v_reuseFailAlloc_2462_, 2, v_v_2441_);
lean_ctor_set(v_reuseFailAlloc_2462_, 3, v___y_2454_);
lean_ctor_set(v_reuseFailAlloc_2462_, 4, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
v___jp_2464_:
{
lean_object* v___x_2466_; lean_object* v___x_2468_; 
v___x_2466_ = lean_nat_add(v___x_2451_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec(v___x_2451_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v_l_2442_);
lean_ctor_set(v___x_2421_, 3, v_tree_2424_);
lean_ctor_set(v___x_2421_, 2, v_v_2426_);
lean_ctor_set(v___x_2421_, 1, v_k_2425_);
lean_ctor_set(v___x_2421_, 0, v___x_2466_);
v___x_2468_ = v___x_2421_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_k_2425_);
lean_ctor_set(v_reuseFailAlloc_2472_, 2, v_v_2426_);
lean_ctor_set(v_reuseFailAlloc_2472_, 3, v_tree_2424_);
lean_ctor_set(v_reuseFailAlloc_2472_, 4, v_l_2442_);
v___x_2468_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
lean_object* v___x_2469_; 
v___x_2469_ = lean_nat_add(v___x_2418_, v_size_2444_);
if (lean_obj_tag(v_r_2443_) == 0)
{
lean_object* v_size_2470_; 
v_size_2470_ = lean_ctor_get(v_r_2443_, 0);
lean_inc(v_size_2470_);
v___y_2454_ = v___x_2468_;
v___y_2455_ = v___x_2469_;
v___y_2456_ = v_size_2470_;
goto v___jp_2453_;
}
else
{
lean_object* v___x_2471_; 
v___x_2471_ = lean_unsigned_to_nat(0u);
v___y_2454_ = v___x_2468_;
v___y_2455_ = v___x_2469_;
v___y_2456_ = v___x_2471_;
goto v___jp_2453_;
}
}
}
}
}
else
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2485_; 
v___x_2481_ = lean_nat_add(v___x_2418_, v_size_2427_);
v___x_2482_ = lean_nat_add(v___x_2481_, v_size_2413_);
lean_dec(v_size_2413_);
v___x_2483_ = lean_nat_add(v___x_2481_, v_size_2439_);
lean_dec(v___x_2481_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 4, v_l_2416_);
lean_ctor_set(v___x_2437_, 3, v_tree_2424_);
lean_ctor_set(v___x_2437_, 2, v_v_2426_);
lean_ctor_set(v___x_2437_, 1, v_k_2425_);
lean_ctor_set(v___x_2437_, 0, v___x_2483_);
v___x_2485_ = v___x_2437_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_k_2425_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v_v_2426_);
lean_ctor_set(v_reuseFailAlloc_2489_, 3, v_tree_2424_);
lean_ctor_set(v_reuseFailAlloc_2489_, 4, v_l_2416_);
v___x_2485_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2487_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v_r_2417_);
lean_ctor_set(v___x_2421_, 3, v___x_2485_);
lean_ctor_set(v___x_2421_, 2, v_v_2415_);
lean_ctor_set(v___x_2421_, 1, v_k_2414_);
lean_ctor_set(v___x_2421_, 0, v___x_2482_);
v___x_2487_ = v___x_2421_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v_k_2414_);
lean_ctor_set(v_reuseFailAlloc_2488_, 2, v_v_2415_);
lean_ctor_set(v_reuseFailAlloc_2488_, 3, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2488_, 4, v_r_2417_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
}
}
else
{
lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2549_; 
lean_inc(v_r_2417_);
lean_inc(v_v_2415_);
lean_inc(v_k_2414_);
lean_inc(v_size_2413_);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_r_2076_);
if (v_isSharedCheck_2549_ == 0)
{
lean_object* v_unused_2550_; lean_object* v_unused_2551_; lean_object* v_unused_2552_; lean_object* v_unused_2553_; lean_object* v_unused_2554_; 
v_unused_2550_ = lean_ctor_get(v_r_2076_, 4);
lean_dec(v_unused_2550_);
v_unused_2551_ = lean_ctor_get(v_r_2076_, 3);
lean_dec(v_unused_2551_);
v_unused_2552_ = lean_ctor_get(v_r_2076_, 2);
lean_dec(v_unused_2552_);
v_unused_2553_ = lean_ctor_get(v_r_2076_, 1);
lean_dec(v_unused_2553_);
v_unused_2554_ = lean_ctor_get(v_r_2076_, 0);
lean_dec(v_unused_2554_);
v___x_2497_ = v_r_2076_;
v_isShared_2498_ = v_isSharedCheck_2549_;
goto v_resetjp_2496_;
}
else
{
lean_dec(v_r_2076_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2549_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
if (lean_obj_tag(v_l_2416_) == 0)
{
if (lean_obj_tag(v_r_2417_) == 0)
{
lean_object* v_k_2499_; lean_object* v_v_2500_; lean_object* v_size_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2505_; 
v_k_2499_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_k_2499_);
v_v_2500_ = lean_ctor_get(v___x_2423_, 1);
lean_inc(v_v_2500_);
lean_dec_ref(v___x_2423_);
v_size_2501_ = lean_ctor_get(v_l_2416_, 0);
v___x_2502_ = lean_nat_add(v___x_2418_, v_size_2413_);
lean_dec(v_size_2413_);
v___x_2503_ = lean_nat_add(v___x_2418_, v_size_2501_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 4, v_l_2416_);
lean_ctor_set(v___x_2497_, 3, v_tree_2424_);
lean_ctor_set(v___x_2497_, 2, v_v_2500_);
lean_ctor_set(v___x_2497_, 1, v_k_2499_);
lean_ctor_set(v___x_2497_, 0, v___x_2503_);
v___x_2505_ = v___x_2497_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2503_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_k_2499_);
lean_ctor_set(v_reuseFailAlloc_2509_, 2, v_v_2500_);
lean_ctor_set(v_reuseFailAlloc_2509_, 3, v_tree_2424_);
lean_ctor_set(v_reuseFailAlloc_2509_, 4, v_l_2416_);
v___x_2505_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2507_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v_r_2417_);
lean_ctor_set(v___x_2421_, 3, v___x_2505_);
lean_ctor_set(v___x_2421_, 2, v_v_2415_);
lean_ctor_set(v___x_2421_, 1, v_k_2414_);
lean_ctor_set(v___x_2421_, 0, v___x_2502_);
v___x_2507_ = v___x_2421_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v_k_2414_);
lean_ctor_set(v_reuseFailAlloc_2508_, 2, v_v_2415_);
lean_ctor_set(v_reuseFailAlloc_2508_, 3, v___x_2505_);
lean_ctor_set(v_reuseFailAlloc_2508_, 4, v_r_2417_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
else
{
lean_object* v_k_2510_; lean_object* v_v_2511_; lean_object* v_k_2512_; lean_object* v_v_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2527_; 
lean_dec(v_size_2413_);
v_k_2510_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_k_2510_);
v_v_2511_ = lean_ctor_get(v___x_2423_, 1);
lean_inc(v_v_2511_);
lean_dec_ref(v___x_2423_);
v_k_2512_ = lean_ctor_get(v_l_2416_, 1);
v_v_2513_ = lean_ctor_get(v_l_2416_, 2);
v_isSharedCheck_2527_ = !lean_is_exclusive(v_l_2416_);
if (v_isSharedCheck_2527_ == 0)
{
lean_object* v_unused_2528_; lean_object* v_unused_2529_; lean_object* v_unused_2530_; 
v_unused_2528_ = lean_ctor_get(v_l_2416_, 4);
lean_dec(v_unused_2528_);
v_unused_2529_ = lean_ctor_get(v_l_2416_, 3);
lean_dec(v_unused_2529_);
v_unused_2530_ = lean_ctor_get(v_l_2416_, 0);
lean_dec(v_unused_2530_);
v___x_2515_ = v_l_2416_;
v_isShared_2516_ = v_isSharedCheck_2527_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_v_2513_);
lean_inc(v_k_2512_);
lean_dec(v_l_2416_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2527_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2517_ = lean_unsigned_to_nat(3u);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 4, v_r_2417_);
lean_ctor_set(v___x_2515_, 3, v_r_2417_);
lean_ctor_set(v___x_2515_, 2, v_v_2511_);
lean_ctor_set(v___x_2515_, 1, v_k_2510_);
lean_ctor_set(v___x_2515_, 0, v___x_2418_);
v___x_2519_ = v___x_2515_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2418_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v_k_2510_);
lean_ctor_set(v_reuseFailAlloc_2526_, 2, v_v_2511_);
lean_ctor_set(v_reuseFailAlloc_2526_, 3, v_r_2417_);
lean_ctor_set(v_reuseFailAlloc_2526_, 4, v_r_2417_);
v___x_2519_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v___x_2521_; 
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 3, v_r_2417_);
lean_ctor_set(v___x_2497_, 0, v___x_2418_);
v___x_2521_ = v___x_2497_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2418_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_k_2414_);
lean_ctor_set(v_reuseFailAlloc_2525_, 2, v_v_2415_);
lean_ctor_set(v_reuseFailAlloc_2525_, 3, v_r_2417_);
lean_ctor_set(v_reuseFailAlloc_2525_, 4, v_r_2417_);
v___x_2521_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2523_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v___x_2521_);
lean_ctor_set(v___x_2421_, 3, v___x_2519_);
lean_ctor_set(v___x_2421_, 2, v_v_2513_);
lean_ctor_set(v___x_2421_, 1, v_k_2512_);
lean_ctor_set(v___x_2421_, 0, v___x_2517_);
v___x_2523_ = v___x_2421_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_k_2512_);
lean_ctor_set(v_reuseFailAlloc_2524_, 2, v_v_2513_);
lean_ctor_set(v_reuseFailAlloc_2524_, 3, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2524_, 4, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2417_) == 0)
{
lean_object* v_k_2531_; lean_object* v_v_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
lean_dec(v_size_2413_);
v_k_2531_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_k_2531_);
v_v_2532_ = lean_ctor_get(v___x_2423_, 1);
lean_inc(v_v_2532_);
lean_dec_ref(v___x_2423_);
v___x_2533_ = lean_unsigned_to_nat(3u);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 4, v_l_2416_);
lean_ctor_set(v___x_2497_, 2, v_v_2532_);
lean_ctor_set(v___x_2497_, 1, v_k_2531_);
lean_ctor_set(v___x_2497_, 0, v___x_2418_);
v___x_2535_ = v___x_2497_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2418_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_k_2531_);
lean_ctor_set(v_reuseFailAlloc_2539_, 2, v_v_2532_);
lean_ctor_set(v_reuseFailAlloc_2539_, 3, v_l_2416_);
lean_ctor_set(v_reuseFailAlloc_2539_, 4, v_l_2416_);
v___x_2535_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2537_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v_r_2417_);
lean_ctor_set(v___x_2421_, 3, v___x_2535_);
lean_ctor_set(v___x_2421_, 2, v_v_2415_);
lean_ctor_set(v___x_2421_, 1, v_k_2414_);
lean_ctor_set(v___x_2421_, 0, v___x_2533_);
v___x_2537_ = v___x_2421_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_k_2414_);
lean_ctor_set(v_reuseFailAlloc_2538_, 2, v_v_2415_);
lean_ctor_set(v_reuseFailAlloc_2538_, 3, v___x_2535_);
lean_ctor_set(v_reuseFailAlloc_2538_, 4, v_r_2417_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
else
{
lean_object* v_k_2540_; lean_object* v_v_2541_; lean_object* v___x_2543_; 
v_k_2540_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_k_2540_);
v_v_2541_ = lean_ctor_get(v___x_2423_, 1);
lean_inc(v_v_2541_);
lean_dec_ref(v___x_2423_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 3, v_r_2417_);
v___x_2543_ = v___x_2497_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_size_2413_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_k_2414_);
lean_ctor_set(v_reuseFailAlloc_2548_, 2, v_v_2415_);
lean_ctor_set(v_reuseFailAlloc_2548_, 3, v_r_2417_);
lean_ctor_set(v_reuseFailAlloc_2548_, 4, v_r_2417_);
v___x_2543_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
lean_object* v___x_2544_; lean_object* v___x_2546_; 
v___x_2544_ = lean_unsigned_to_nat(2u);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v___x_2543_);
lean_ctor_set(v___x_2421_, 3, v_r_2417_);
lean_ctor_set(v___x_2421_, 2, v_v_2541_);
lean_ctor_set(v___x_2421_, 1, v_k_2540_);
lean_ctor_set(v___x_2421_, 0, v___x_2544_);
v___x_2546_ = v___x_2421_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2544_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_k_2540_);
lean_ctor_set(v_reuseFailAlloc_2547_, 2, v_v_2541_);
lean_ctor_set(v_reuseFailAlloc_2547_, 3, v_r_2417_);
lean_ctor_set(v_reuseFailAlloc_2547_, 4, v___x_2543_);
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
}
else
{
lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2713_; 
lean_inc(v_r_2417_);
lean_inc(v_v_2415_);
lean_inc(v_k_2414_);
v_isSharedCheck_2713_ = !lean_is_exclusive(v_r_2076_);
if (v_isSharedCheck_2713_ == 0)
{
lean_object* v_unused_2714_; lean_object* v_unused_2715_; lean_object* v_unused_2716_; lean_object* v_unused_2717_; lean_object* v_unused_2718_; 
v_unused_2714_ = lean_ctor_get(v_r_2076_, 4);
lean_dec(v_unused_2714_);
v_unused_2715_ = lean_ctor_get(v_r_2076_, 3);
lean_dec(v_unused_2715_);
v_unused_2716_ = lean_ctor_get(v_r_2076_, 2);
lean_dec(v_unused_2716_);
v_unused_2717_ = lean_ctor_get(v_r_2076_, 1);
lean_dec(v_unused_2717_);
v_unused_2718_ = lean_ctor_get(v_r_2076_, 0);
lean_dec(v_unused_2718_);
v___x_2562_ = v_r_2076_;
v_isShared_2563_ = v_isSharedCheck_2713_;
goto v_resetjp_2561_;
}
else
{
lean_dec(v_r_2076_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2713_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v_tree_2565_; 
v___x_2564_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2414_, v_v_2415_, v_l_2416_, v_r_2417_);
v_tree_2565_ = lean_ctor_get(v___x_2564_, 2);
lean_inc(v_tree_2565_);
if (lean_obj_tag(v_tree_2565_) == 0)
{
lean_object* v_k_2566_; lean_object* v_v_2567_; lean_object* v_size_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v_k_2566_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_k_2566_);
v_v_2567_ = lean_ctor_get(v___x_2564_, 1);
lean_inc(v_v_2567_);
lean_dec_ref(v___x_2564_);
v_size_2568_ = lean_ctor_get(v_tree_2565_, 0);
v___x_2569_ = lean_unsigned_to_nat(3u);
v___x_2570_ = lean_nat_mul(v___x_2569_, v_size_2568_);
v___x_2571_ = lean_nat_dec_lt(v___x_2570_, v_size_2408_);
lean_dec(v___x_2570_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
lean_dec(v_r_2412_);
v___x_2572_ = lean_nat_add(v___x_2418_, v_size_2408_);
v___x_2573_ = lean_nat_add(v___x_2572_, v_size_2568_);
lean_dec(v___x_2572_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 4, v_tree_2565_);
lean_ctor_set(v___x_2562_, 3, v_l_2075_);
lean_ctor_set(v___x_2562_, 2, v_v_2567_);
lean_ctor_set(v___x_2562_, 1, v_k_2566_);
lean_ctor_set(v___x_2562_, 0, v___x_2573_);
v___x_2575_ = v___x_2562_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2573_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v_k_2566_);
lean_ctor_set(v_reuseFailAlloc_2576_, 2, v_v_2567_);
lean_ctor_set(v_reuseFailAlloc_2576_, 3, v_l_2075_);
lean_ctor_set(v_reuseFailAlloc_2576_, 4, v_tree_2565_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
else
{
lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2642_; 
lean_inc(v_l_2411_);
lean_inc(v_v_2410_);
lean_inc(v_k_2409_);
lean_inc(v_size_2408_);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_l_2075_);
if (v_isSharedCheck_2642_ == 0)
{
lean_object* v_unused_2643_; lean_object* v_unused_2644_; lean_object* v_unused_2645_; lean_object* v_unused_2646_; lean_object* v_unused_2647_; 
v_unused_2643_ = lean_ctor_get(v_l_2075_, 4);
lean_dec(v_unused_2643_);
v_unused_2644_ = lean_ctor_get(v_l_2075_, 3);
lean_dec(v_unused_2644_);
v_unused_2645_ = lean_ctor_get(v_l_2075_, 2);
lean_dec(v_unused_2645_);
v_unused_2646_ = lean_ctor_get(v_l_2075_, 1);
lean_dec(v_unused_2646_);
v_unused_2647_ = lean_ctor_get(v_l_2075_, 0);
lean_dec(v_unused_2647_);
v___x_2578_ = v_l_2075_;
v_isShared_2579_ = v_isSharedCheck_2642_;
goto v_resetjp_2577_;
}
else
{
lean_dec(v_l_2075_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2642_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v_size_2580_; lean_object* v_size_2581_; lean_object* v_k_2582_; lean_object* v_v_2583_; lean_object* v_l_2584_; lean_object* v_r_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; 
v_size_2580_ = lean_ctor_get(v_l_2411_, 0);
v_size_2581_ = lean_ctor_get(v_r_2412_, 0);
v_k_2582_ = lean_ctor_get(v_r_2412_, 1);
v_v_2583_ = lean_ctor_get(v_r_2412_, 2);
v_l_2584_ = lean_ctor_get(v_r_2412_, 3);
v_r_2585_ = lean_ctor_get(v_r_2412_, 4);
v___x_2586_ = lean_unsigned_to_nat(2u);
v___x_2587_ = lean_nat_mul(v___x_2586_, v_size_2580_);
v___x_2588_ = lean_nat_dec_lt(v_size_2581_, v___x_2587_);
lean_dec(v___x_2587_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2626_; 
lean_inc(v_r_2585_);
lean_inc(v_l_2584_);
lean_inc(v_v_2583_);
lean_inc(v_k_2582_);
lean_del_object(v___x_2578_);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_r_2412_);
if (v_isSharedCheck_2626_ == 0)
{
lean_object* v_unused_2627_; lean_object* v_unused_2628_; lean_object* v_unused_2629_; lean_object* v_unused_2630_; lean_object* v_unused_2631_; 
v_unused_2627_ = lean_ctor_get(v_r_2412_, 4);
lean_dec(v_unused_2627_);
v_unused_2628_ = lean_ctor_get(v_r_2412_, 3);
lean_dec(v_unused_2628_);
v_unused_2629_ = lean_ctor_get(v_r_2412_, 2);
lean_dec(v_unused_2629_);
v_unused_2630_ = lean_ctor_get(v_r_2412_, 1);
lean_dec(v_unused_2630_);
v_unused_2631_ = lean_ctor_get(v_r_2412_, 0);
lean_dec(v_unused_2631_);
v___x_2590_ = v_r_2412_;
v_isShared_2591_ = v_isSharedCheck_2626_;
goto v_resetjp_2589_;
}
else
{
lean_dec(v_r_2412_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2626_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___x_2614_; lean_object* v___y_2616_; 
v___x_2592_ = lean_nat_add(v___x_2418_, v_size_2408_);
lean_dec(v_size_2408_);
v___x_2593_ = lean_nat_add(v___x_2592_, v_size_2568_);
lean_dec(v___x_2592_);
v___x_2614_ = lean_nat_add(v___x_2418_, v_size_2580_);
if (lean_obj_tag(v_l_2584_) == 0)
{
lean_object* v_size_2624_; 
v_size_2624_ = lean_ctor_get(v_l_2584_, 0);
lean_inc(v_size_2624_);
v___y_2616_ = v_size_2624_;
goto v___jp_2615_;
}
else
{
lean_object* v___x_2625_; 
v___x_2625_ = lean_unsigned_to_nat(0u);
v___y_2616_ = v___x_2625_;
goto v___jp_2615_;
}
v___jp_2594_:
{
lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2598_ = lean_nat_add(v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec(v___y_2596_);
lean_inc_ref(v_tree_2565_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 4, v_tree_2565_);
lean_ctor_set(v___x_2590_, 3, v_r_2585_);
lean_ctor_set(v___x_2590_, 2, v_v_2567_);
lean_ctor_set(v___x_2590_, 1, v_k_2566_);
lean_ctor_set(v___x_2590_, 0, v___x_2598_);
v___x_2600_ = v___x_2590_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2598_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_k_2566_);
lean_ctor_set(v_reuseFailAlloc_2613_, 2, v_v_2567_);
lean_ctor_set(v_reuseFailAlloc_2613_, 3, v_r_2585_);
lean_ctor_set(v_reuseFailAlloc_2613_, 4, v_tree_2565_);
v___x_2600_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
v_isSharedCheck_2607_ = !lean_is_exclusive(v_tree_2565_);
if (v_isSharedCheck_2607_ == 0)
{
lean_object* v_unused_2608_; lean_object* v_unused_2609_; lean_object* v_unused_2610_; lean_object* v_unused_2611_; lean_object* v_unused_2612_; 
v_unused_2608_ = lean_ctor_get(v_tree_2565_, 4);
lean_dec(v_unused_2608_);
v_unused_2609_ = lean_ctor_get(v_tree_2565_, 3);
lean_dec(v_unused_2609_);
v_unused_2610_ = lean_ctor_get(v_tree_2565_, 2);
lean_dec(v_unused_2610_);
v_unused_2611_ = lean_ctor_get(v_tree_2565_, 1);
lean_dec(v_unused_2611_);
v_unused_2612_ = lean_ctor_get(v_tree_2565_, 0);
lean_dec(v_unused_2612_);
v___x_2602_ = v_tree_2565_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_dec(v_tree_2565_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 4, v___x_2600_);
lean_ctor_set(v___x_2602_, 3, v___y_2595_);
lean_ctor_set(v___x_2602_, 2, v_v_2583_);
lean_ctor_set(v___x_2602_, 1, v_k_2582_);
lean_ctor_set(v___x_2602_, 0, v___x_2593_);
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_k_2582_);
lean_ctor_set(v_reuseFailAlloc_2606_, 2, v_v_2583_);
lean_ctor_set(v_reuseFailAlloc_2606_, 3, v___y_2595_);
lean_ctor_set(v_reuseFailAlloc_2606_, 4, v___x_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
v___jp_2615_:
{
lean_object* v___x_2617_; lean_object* v___x_2619_; 
v___x_2617_ = lean_nat_add(v___x_2614_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec(v___x_2614_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 4, v_l_2584_);
lean_ctor_set(v___x_2562_, 3, v_l_2411_);
lean_ctor_set(v___x_2562_, 2, v_v_2410_);
lean_ctor_set(v___x_2562_, 1, v_k_2409_);
lean_ctor_set(v___x_2562_, 0, v___x_2617_);
v___x_2619_ = v___x_2562_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2617_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_k_2409_);
lean_ctor_set(v_reuseFailAlloc_2623_, 2, v_v_2410_);
lean_ctor_set(v_reuseFailAlloc_2623_, 3, v_l_2411_);
lean_ctor_set(v_reuseFailAlloc_2623_, 4, v_l_2584_);
v___x_2619_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
lean_object* v___x_2620_; 
v___x_2620_ = lean_nat_add(v___x_2418_, v_size_2568_);
if (lean_obj_tag(v_r_2585_) == 0)
{
lean_object* v_size_2621_; 
v_size_2621_ = lean_ctor_get(v_r_2585_, 0);
lean_inc(v_size_2621_);
v___y_2595_ = v___x_2619_;
v___y_2596_ = v___x_2620_;
v___y_2597_ = v_size_2621_;
goto v___jp_2594_;
}
else
{
lean_object* v___x_2622_; 
v___x_2622_ = lean_unsigned_to_nat(0u);
v___y_2595_ = v___x_2619_;
v___y_2596_ = v___x_2620_;
v___y_2597_ = v___x_2622_;
goto v___jp_2594_;
}
}
}
}
}
else
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2637_; 
v___x_2632_ = lean_nat_add(v___x_2418_, v_size_2408_);
lean_dec(v_size_2408_);
v___x_2633_ = lean_nat_add(v___x_2632_, v_size_2568_);
lean_dec(v___x_2632_);
v___x_2634_ = lean_nat_add(v___x_2418_, v_size_2568_);
v___x_2635_ = lean_nat_add(v___x_2634_, v_size_2581_);
lean_dec(v___x_2634_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 4, v_tree_2565_);
lean_ctor_set(v___x_2562_, 3, v_r_2412_);
lean_ctor_set(v___x_2562_, 2, v_v_2567_);
lean_ctor_set(v___x_2562_, 1, v_k_2566_);
lean_ctor_set(v___x_2562_, 0, v___x_2635_);
v___x_2637_ = v___x_2562_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v_k_2566_);
lean_ctor_set(v_reuseFailAlloc_2641_, 2, v_v_2567_);
lean_ctor_set(v_reuseFailAlloc_2641_, 3, v_r_2412_);
lean_ctor_set(v_reuseFailAlloc_2641_, 4, v_tree_2565_);
v___x_2637_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
lean_object* v___x_2639_; 
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 4, v___x_2637_);
lean_ctor_set(v___x_2578_, 0, v___x_2633_);
v___x_2639_ = v___x_2578_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2633_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v_k_2409_);
lean_ctor_set(v_reuseFailAlloc_2640_, 2, v_v_2410_);
lean_ctor_set(v_reuseFailAlloc_2640_, 3, v_l_2411_);
lean_ctor_set(v_reuseFailAlloc_2640_, 4, v___x_2637_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2411_) == 0)
{
lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2671_; 
lean_inc_ref(v_l_2411_);
lean_inc(v_v_2410_);
lean_inc(v_k_2409_);
lean_inc(v_size_2408_);
v_isSharedCheck_2671_ = !lean_is_exclusive(v_l_2075_);
if (v_isSharedCheck_2671_ == 0)
{
lean_object* v_unused_2672_; lean_object* v_unused_2673_; lean_object* v_unused_2674_; lean_object* v_unused_2675_; lean_object* v_unused_2676_; 
v_unused_2672_ = lean_ctor_get(v_l_2075_, 4);
lean_dec(v_unused_2672_);
v_unused_2673_ = lean_ctor_get(v_l_2075_, 3);
lean_dec(v_unused_2673_);
v_unused_2674_ = lean_ctor_get(v_l_2075_, 2);
lean_dec(v_unused_2674_);
v_unused_2675_ = lean_ctor_get(v_l_2075_, 1);
lean_dec(v_unused_2675_);
v_unused_2676_ = lean_ctor_get(v_l_2075_, 0);
lean_dec(v_unused_2676_);
v___x_2649_ = v_l_2075_;
v_isShared_2650_ = v_isSharedCheck_2671_;
goto v_resetjp_2648_;
}
else
{
lean_dec(v_l_2075_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2671_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
if (lean_obj_tag(v_r_2412_) == 0)
{
lean_object* v_k_2651_; lean_object* v_v_2652_; lean_object* v_size_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2657_; 
v_k_2651_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_k_2651_);
v_v_2652_ = lean_ctor_get(v___x_2564_, 1);
lean_inc(v_v_2652_);
lean_dec_ref(v___x_2564_);
v_size_2653_ = lean_ctor_get(v_r_2412_, 0);
v___x_2654_ = lean_nat_add(v___x_2418_, v_size_2408_);
lean_dec(v_size_2408_);
v___x_2655_ = lean_nat_add(v___x_2418_, v_size_2653_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 4, v_tree_2565_);
lean_ctor_set(v___x_2562_, 3, v_r_2412_);
lean_ctor_set(v___x_2562_, 2, v_v_2652_);
lean_ctor_set(v___x_2562_, 1, v_k_2651_);
lean_ctor_set(v___x_2562_, 0, v___x_2655_);
v___x_2657_ = v___x_2562_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2655_);
lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_k_2651_);
lean_ctor_set(v_reuseFailAlloc_2661_, 2, v_v_2652_);
lean_ctor_set(v_reuseFailAlloc_2661_, 3, v_r_2412_);
lean_ctor_set(v_reuseFailAlloc_2661_, 4, v_tree_2565_);
v___x_2657_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
lean_object* v___x_2659_; 
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 4, v___x_2657_);
lean_ctor_set(v___x_2649_, 0, v___x_2654_);
v___x_2659_ = v___x_2649_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2654_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v_k_2409_);
lean_ctor_set(v_reuseFailAlloc_2660_, 2, v_v_2410_);
lean_ctor_set(v_reuseFailAlloc_2660_, 3, v_l_2411_);
lean_ctor_set(v_reuseFailAlloc_2660_, 4, v___x_2657_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
else
{
lean_object* v_k_2662_; lean_object* v_v_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
lean_dec(v_size_2408_);
v_k_2662_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_k_2662_);
v_v_2663_ = lean_ctor_get(v___x_2564_, 1);
lean_inc(v_v_2663_);
lean_dec_ref(v___x_2564_);
v___x_2664_ = lean_unsigned_to_nat(3u);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 4, v_r_2412_);
lean_ctor_set(v___x_2562_, 3, v_r_2412_);
lean_ctor_set(v___x_2562_, 2, v_v_2663_);
lean_ctor_set(v___x_2562_, 1, v_k_2662_);
lean_ctor_set(v___x_2562_, 0, v___x_2418_);
v___x_2666_ = v___x_2562_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2418_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_k_2662_);
lean_ctor_set(v_reuseFailAlloc_2670_, 2, v_v_2663_);
lean_ctor_set(v_reuseFailAlloc_2670_, 3, v_r_2412_);
lean_ctor_set(v_reuseFailAlloc_2670_, 4, v_r_2412_);
v___x_2666_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2668_; 
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 4, v___x_2666_);
lean_ctor_set(v___x_2649_, 0, v___x_2664_);
v___x_2668_ = v___x_2649_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_k_2409_);
lean_ctor_set(v_reuseFailAlloc_2669_, 2, v_v_2410_);
lean_ctor_set(v_reuseFailAlloc_2669_, 3, v_l_2411_);
lean_ctor_set(v_reuseFailAlloc_2669_, 4, v___x_2666_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2412_) == 0)
{
lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2701_; 
lean_inc(v_l_2411_);
lean_inc(v_v_2410_);
lean_inc(v_k_2409_);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_l_2075_);
if (v_isSharedCheck_2701_ == 0)
{
lean_object* v_unused_2702_; lean_object* v_unused_2703_; lean_object* v_unused_2704_; lean_object* v_unused_2705_; lean_object* v_unused_2706_; 
v_unused_2702_ = lean_ctor_get(v_l_2075_, 4);
lean_dec(v_unused_2702_);
v_unused_2703_ = lean_ctor_get(v_l_2075_, 3);
lean_dec(v_unused_2703_);
v_unused_2704_ = lean_ctor_get(v_l_2075_, 2);
lean_dec(v_unused_2704_);
v_unused_2705_ = lean_ctor_get(v_l_2075_, 1);
lean_dec(v_unused_2705_);
v_unused_2706_ = lean_ctor_get(v_l_2075_, 0);
lean_dec(v_unused_2706_);
v___x_2678_ = v_l_2075_;
v_isShared_2679_ = v_isSharedCheck_2701_;
goto v_resetjp_2677_;
}
else
{
lean_dec(v_l_2075_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2701_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v_k_2680_; lean_object* v_v_2681_; lean_object* v_k_2682_; lean_object* v_v_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2697_; 
v_k_2680_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_k_2680_);
v_v_2681_ = lean_ctor_get(v___x_2564_, 1);
lean_inc(v_v_2681_);
lean_dec_ref(v___x_2564_);
v_k_2682_ = lean_ctor_get(v_r_2412_, 1);
v_v_2683_ = lean_ctor_get(v_r_2412_, 2);
v_isSharedCheck_2697_ = !lean_is_exclusive(v_r_2412_);
if (v_isSharedCheck_2697_ == 0)
{
lean_object* v_unused_2698_; lean_object* v_unused_2699_; lean_object* v_unused_2700_; 
v_unused_2698_ = lean_ctor_get(v_r_2412_, 4);
lean_dec(v_unused_2698_);
v_unused_2699_ = lean_ctor_get(v_r_2412_, 3);
lean_dec(v_unused_2699_);
v_unused_2700_ = lean_ctor_get(v_r_2412_, 0);
lean_dec(v_unused_2700_);
v___x_2685_ = v_r_2412_;
v_isShared_2686_ = v_isSharedCheck_2697_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_v_2683_);
lean_inc(v_k_2682_);
lean_dec(v_r_2412_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2697_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2687_ = lean_unsigned_to_nat(3u);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 4, v_l_2411_);
lean_ctor_set(v___x_2685_, 3, v_l_2411_);
lean_ctor_set(v___x_2685_, 2, v_v_2410_);
lean_ctor_set(v___x_2685_, 1, v_k_2409_);
lean_ctor_set(v___x_2685_, 0, v___x_2418_);
v___x_2689_ = v___x_2685_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2418_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_k_2409_);
lean_ctor_set(v_reuseFailAlloc_2696_, 2, v_v_2410_);
lean_ctor_set(v_reuseFailAlloc_2696_, 3, v_l_2411_);
lean_ctor_set(v_reuseFailAlloc_2696_, 4, v_l_2411_);
v___x_2689_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2691_; 
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 4, v_l_2411_);
lean_ctor_set(v___x_2562_, 3, v_l_2411_);
lean_ctor_set(v___x_2562_, 2, v_v_2681_);
lean_ctor_set(v___x_2562_, 1, v_k_2680_);
lean_ctor_set(v___x_2562_, 0, v___x_2418_);
v___x_2691_ = v___x_2562_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2418_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v_k_2680_);
lean_ctor_set(v_reuseFailAlloc_2695_, 2, v_v_2681_);
lean_ctor_set(v_reuseFailAlloc_2695_, 3, v_l_2411_);
lean_ctor_set(v_reuseFailAlloc_2695_, 4, v_l_2411_);
v___x_2691_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2693_; 
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 4, v___x_2691_);
lean_ctor_set(v___x_2678_, 3, v___x_2689_);
lean_ctor_set(v___x_2678_, 2, v_v_2683_);
lean_ctor_set(v___x_2678_, 1, v_k_2682_);
lean_ctor_set(v___x_2678_, 0, v___x_2687_);
v___x_2693_ = v___x_2678_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2687_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v_k_2682_);
lean_ctor_set(v_reuseFailAlloc_2694_, 2, v_v_2683_);
lean_ctor_set(v_reuseFailAlloc_2694_, 3, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2694_, 4, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
}
else
{
lean_object* v_k_2707_; lean_object* v_v_2708_; lean_object* v___x_2709_; lean_object* v___x_2711_; 
v_k_2707_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_k_2707_);
v_v_2708_ = lean_ctor_get(v___x_2564_, 1);
lean_inc(v_v_2708_);
lean_dec_ref(v___x_2564_);
v___x_2709_ = lean_unsigned_to_nat(2u);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 4, v_r_2412_);
lean_ctor_set(v___x_2562_, 3, v_l_2075_);
lean_ctor_set(v___x_2562_, 2, v_v_2708_);
lean_ctor_set(v___x_2562_, 1, v_k_2707_);
lean_ctor_set(v___x_2562_, 0, v___x_2709_);
v___x_2711_ = v___x_2562_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2709_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v_k_2707_);
lean_ctor_set(v_reuseFailAlloc_2712_, 2, v_v_2708_);
lean_ctor_set(v_reuseFailAlloc_2712_, 3, v_l_2075_);
lean_ctor_set(v_reuseFailAlloc_2712_, 4, v_r_2412_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
}
}
}
else
{
return v_l_2075_;
}
}
else
{
return v_r_2076_;
}
}
default: 
{
goto v___jp_2113_;
}
}
}
else
{
goto v___jp_2113_;
}
}
else
{
lean_del_object(v___x_2078_);
goto v___jp_2265_;
}
v___jp_2080_:
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = lean_nat_add(v___y_2084_, v___y_2088_);
lean_dec(v___y_2088_);
lean_dec(v___y_2084_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 4, v___y_2083_);
lean_ctor_set(v___x_2078_, 3, v___y_2087_);
lean_ctor_set(v___x_2078_, 0, v___x_2089_);
v___x_2091_ = v___x_2078_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_k_2073_);
lean_ctor_set(v_reuseFailAlloc_2093_, 2, v_v_2074_);
lean_ctor_set(v_reuseFailAlloc_2093_, 3, v___y_2087_);
lean_ctor_set(v_reuseFailAlloc_2093_, 4, v___y_2083_);
v___x_2091_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2092_; 
v___x_2092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2092_, 0, v___y_2086_);
lean_ctor_set(v___x_2092_, 1, v___y_2081_);
lean_ctor_set(v___x_2092_, 2, v___y_2082_);
lean_ctor_set(v___x_2092_, 3, v___y_2085_);
lean_ctor_set(v___x_2092_, 4, v___x_2091_);
return v___x_2092_;
}
}
v___jp_2094_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2108_ = lean_nat_add(v___y_2103_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec(v___y_2103_);
v___x_2109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set(v___x_2109_, 1, v___y_2099_);
lean_ctor_set(v___x_2109_, 2, v___y_2095_);
lean_ctor_set(v___x_2109_, 3, v___y_2105_);
lean_ctor_set(v___x_2109_, 4, v___y_2097_);
v___x_2110_ = lean_nat_add(v___y_2102_, v___y_2101_);
lean_dec(v___y_2101_);
if (lean_obj_tag(v___y_2106_) == 0)
{
lean_object* v_size_2111_; 
v_size_2111_ = lean_ctor_get(v___y_2106_, 0);
lean_inc(v_size_2111_);
v___y_2081_ = v___y_2096_;
v___y_2082_ = v___y_2098_;
v___y_2083_ = v___y_2100_;
v___y_2084_ = v___x_2110_;
v___y_2085_ = v___x_2109_;
v___y_2086_ = v___y_2104_;
v___y_2087_ = v___y_2106_;
v___y_2088_ = v_size_2111_;
goto v___jp_2080_;
}
else
{
lean_object* v___x_2112_; 
v___x_2112_ = lean_unsigned_to_nat(0u);
v___y_2081_ = v___y_2096_;
v___y_2082_ = v___y_2098_;
v___y_2083_ = v___y_2100_;
v___y_2084_ = v___x_2110_;
v___y_2085_ = v___x_2109_;
v___y_2086_ = v___y_2104_;
v___y_2087_ = v___y_2106_;
v___y_2088_ = v___x_2112_;
goto v___jp_2080_;
}
}
v___jp_2113_:
{
lean_object* v_impl_2114_; lean_object* v___x_2115_; 
v_impl_2114_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v_k_2057_, v_r_2076_);
v___x_2115_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2114_) == 0)
{
if (lean_obj_tag(v_l_2075_) == 0)
{
lean_object* v_size_2116_; lean_object* v_size_2117_; lean_object* v_k_2118_; lean_object* v_v_2119_; lean_object* v_l_2120_; lean_object* v_r_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v_size_2116_ = lean_ctor_get(v_impl_2114_, 0);
lean_inc(v_size_2116_);
v_size_2117_ = lean_ctor_get(v_l_2075_, 0);
v_k_2118_ = lean_ctor_get(v_l_2075_, 1);
v_v_2119_ = lean_ctor_get(v_l_2075_, 2);
v_l_2120_ = lean_ctor_get(v_l_2075_, 3);
v_r_2121_ = lean_ctor_get(v_l_2075_, 4);
v___x_2122_ = lean_unsigned_to_nat(3u);
v___x_2123_ = lean_nat_mul(v___x_2122_, v_size_2116_);
v___x_2124_ = lean_nat_dec_lt(v___x_2123_, v_size_2117_);
lean_dec(v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
lean_del_object(v___x_2078_);
v___x_2125_ = lean_nat_add(v___x_2115_, v_size_2117_);
v___x_2126_ = lean_nat_add(v___x_2125_, v_size_2116_);
lean_dec(v_size_2116_);
lean_dec(v___x_2125_);
v___x_2127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v_k_2073_);
lean_ctor_set(v___x_2127_, 2, v_v_2074_);
lean_ctor_set(v___x_2127_, 3, v_l_2075_);
lean_ctor_set(v___x_2127_, 4, v_impl_2114_);
return v___x_2127_;
}
else
{
lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2164_; 
lean_inc(v_r_2121_);
lean_inc(v_l_2120_);
lean_inc(v_v_2119_);
lean_inc(v_k_2118_);
lean_inc(v_size_2117_);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_l_2075_);
if (v_isSharedCheck_2164_ == 0)
{
lean_object* v_unused_2165_; lean_object* v_unused_2166_; lean_object* v_unused_2167_; lean_object* v_unused_2168_; lean_object* v_unused_2169_; 
v_unused_2165_ = lean_ctor_get(v_l_2075_, 4);
lean_dec(v_unused_2165_);
v_unused_2166_ = lean_ctor_get(v_l_2075_, 3);
lean_dec(v_unused_2166_);
v_unused_2167_ = lean_ctor_get(v_l_2075_, 2);
lean_dec(v_unused_2167_);
v_unused_2168_ = lean_ctor_get(v_l_2075_, 1);
lean_dec(v_unused_2168_);
v_unused_2169_ = lean_ctor_get(v_l_2075_, 0);
lean_dec(v_unused_2169_);
v___x_2129_ = v_l_2075_;
v_isShared_2130_ = v_isSharedCheck_2164_;
goto v_resetjp_2128_;
}
else
{
lean_dec(v_l_2075_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2164_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_size_2131_; lean_object* v_size_2132_; lean_object* v_k_2133_; lean_object* v_v_2134_; lean_object* v_l_2135_; lean_object* v_r_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v_size_2131_ = lean_ctor_get(v_l_2120_, 0);
v_size_2132_ = lean_ctor_get(v_r_2121_, 0);
v_k_2133_ = lean_ctor_get(v_r_2121_, 1);
v_v_2134_ = lean_ctor_get(v_r_2121_, 2);
v_l_2135_ = lean_ctor_get(v_r_2121_, 3);
v_r_2136_ = lean_ctor_get(v_r_2121_, 4);
v___x_2137_ = lean_unsigned_to_nat(2u);
v___x_2138_ = lean_nat_mul(v___x_2137_, v_size_2131_);
v___x_2139_ = lean_nat_dec_lt(v_size_2132_, v___x_2138_);
lean_dec(v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
lean_inc(v_r_2136_);
lean_inc(v_l_2135_);
lean_inc(v_v_2134_);
lean_inc(v_k_2133_);
lean_del_object(v___x_2129_);
lean_dec(v_r_2121_);
v___x_2140_ = lean_nat_add(v___x_2115_, v_size_2117_);
lean_dec(v_size_2117_);
v___x_2141_ = lean_nat_add(v___x_2140_, v_size_2116_);
lean_dec(v___x_2140_);
v___x_2142_ = lean_nat_add(v___x_2115_, v_size_2131_);
if (lean_obj_tag(v_l_2135_) == 0)
{
lean_object* v_size_2143_; 
v_size_2143_ = lean_ctor_get(v_l_2135_, 0);
lean_inc(v_size_2143_);
v___y_2095_ = v_v_2119_;
v___y_2096_ = v_k_2133_;
v___y_2097_ = v_l_2135_;
v___y_2098_ = v_v_2134_;
v___y_2099_ = v_k_2118_;
v___y_2100_ = v_impl_2114_;
v___y_2101_ = v_size_2116_;
v___y_2102_ = v___x_2115_;
v___y_2103_ = v___x_2142_;
v___y_2104_ = v___x_2141_;
v___y_2105_ = v_l_2120_;
v___y_2106_ = v_r_2136_;
v___y_2107_ = v_size_2143_;
goto v___jp_2094_;
}
else
{
lean_object* v___x_2144_; 
v___x_2144_ = lean_unsigned_to_nat(0u);
v___y_2095_ = v_v_2119_;
v___y_2096_ = v_k_2133_;
v___y_2097_ = v_l_2135_;
v___y_2098_ = v_v_2134_;
v___y_2099_ = v_k_2118_;
v___y_2100_ = v_impl_2114_;
v___y_2101_ = v_size_2116_;
v___y_2102_ = v___x_2115_;
v___y_2103_ = v___x_2142_;
v___y_2104_ = v___x_2141_;
v___y_2105_ = v_l_2120_;
v___y_2106_ = v_r_2136_;
v___y_2107_ = v___x_2144_;
goto v___jp_2094_;
}
}
else
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2150_; 
lean_del_object(v___x_2078_);
v___x_2145_ = lean_nat_add(v___x_2115_, v_size_2117_);
lean_dec(v_size_2117_);
v___x_2146_ = lean_nat_add(v___x_2145_, v_size_2116_);
lean_dec(v___x_2145_);
v___x_2147_ = lean_nat_add(v___x_2115_, v_size_2116_);
lean_dec(v_size_2116_);
v___x_2148_ = lean_nat_add(v___x_2147_, v_size_2132_);
lean_dec(v___x_2147_);
lean_inc_ref(v_impl_2114_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 4, v_impl_2114_);
lean_ctor_set(v___x_2129_, 3, v_r_2121_);
lean_ctor_set(v___x_2129_, 2, v_v_2074_);
lean_ctor_set(v___x_2129_, 1, v_k_2073_);
lean_ctor_set(v___x_2129_, 0, v___x_2148_);
v___x_2150_ = v___x_2129_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_k_2073_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_v_2074_);
lean_ctor_set(v_reuseFailAlloc_2163_, 3, v_r_2121_);
lean_ctor_set(v_reuseFailAlloc_2163_, 4, v_impl_2114_);
v___x_2150_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
v_isSharedCheck_2157_ = !lean_is_exclusive(v_impl_2114_);
if (v_isSharedCheck_2157_ == 0)
{
lean_object* v_unused_2158_; lean_object* v_unused_2159_; lean_object* v_unused_2160_; lean_object* v_unused_2161_; lean_object* v_unused_2162_; 
v_unused_2158_ = lean_ctor_get(v_impl_2114_, 4);
lean_dec(v_unused_2158_);
v_unused_2159_ = lean_ctor_get(v_impl_2114_, 3);
lean_dec(v_unused_2159_);
v_unused_2160_ = lean_ctor_get(v_impl_2114_, 2);
lean_dec(v_unused_2160_);
v_unused_2161_ = lean_ctor_get(v_impl_2114_, 1);
lean_dec(v_unused_2161_);
v_unused_2162_ = lean_ctor_get(v_impl_2114_, 0);
lean_dec(v_unused_2162_);
v___x_2152_ = v_impl_2114_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_dec(v_impl_2114_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 4, v___x_2150_);
lean_ctor_set(v___x_2152_, 3, v_l_2120_);
lean_ctor_set(v___x_2152_, 2, v_v_2119_);
lean_ctor_set(v___x_2152_, 1, v_k_2118_);
lean_ctor_set(v___x_2152_, 0, v___x_2146_);
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_k_2118_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v_v_2119_);
lean_ctor_set(v_reuseFailAlloc_2156_, 3, v_l_2120_);
lean_ctor_set(v_reuseFailAlloc_2156_, 4, v___x_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_del_object(v___x_2078_);
v_size_2170_ = lean_ctor_get(v_impl_2114_, 0);
lean_inc(v_size_2170_);
v___x_2171_ = lean_nat_add(v___x_2115_, v_size_2170_);
lean_dec(v_size_2170_);
v___x_2172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
lean_ctor_set(v___x_2172_, 1, v_k_2073_);
lean_ctor_set(v___x_2172_, 2, v_v_2074_);
lean_ctor_set(v___x_2172_, 3, v_l_2075_);
lean_ctor_set(v___x_2172_, 4, v_impl_2114_);
return v___x_2172_;
}
}
else
{
lean_del_object(v___x_2078_);
if (lean_obj_tag(v_l_2075_) == 0)
{
lean_object* v_l_2173_; 
v_l_2173_ = lean_ctor_get(v_l_2075_, 3);
if (lean_obj_tag(v_l_2173_) == 0)
{
lean_object* v_r_2174_; 
lean_inc_ref(v_l_2173_);
v_r_2174_ = lean_ctor_get(v_l_2075_, 4);
lean_inc(v_r_2174_);
if (lean_obj_tag(v_r_2174_) == 0)
{
lean_object* v_size_2175_; lean_object* v_k_2176_; lean_object* v_v_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2199_; 
v_size_2175_ = lean_ctor_get(v_l_2075_, 0);
v_k_2176_ = lean_ctor_get(v_l_2075_, 1);
v_v_2177_ = lean_ctor_get(v_l_2075_, 2);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_l_2075_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; lean_object* v_unused_2201_; 
v_unused_2200_ = lean_ctor_get(v_l_2075_, 4);
lean_dec(v_unused_2200_);
v_unused_2201_ = lean_ctor_get(v_l_2075_, 3);
lean_dec(v_unused_2201_);
v___x_2179_ = v_l_2075_;
v_isShared_2180_ = v_isSharedCheck_2199_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_v_2177_);
lean_inc(v_k_2176_);
lean_inc(v_size_2175_);
lean_dec(v_l_2075_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2199_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v_size_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
v_size_2181_ = lean_ctor_get(v_r_2174_, 0);
v___x_2182_ = lean_nat_add(v___x_2115_, v_size_2175_);
lean_dec(v_size_2175_);
v___x_2183_ = lean_nat_add(v___x_2115_, v_size_2181_);
lean_inc_ref(v_r_2174_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 4, v_impl_2114_);
lean_ctor_set(v___x_2179_, 3, v_r_2174_);
lean_ctor_set(v___x_2179_, 2, v_v_2074_);
lean_ctor_set(v___x_2179_, 1, v_k_2073_);
lean_ctor_set(v___x_2179_, 0, v___x_2183_);
v___x_2185_ = v___x_2179_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_k_2073_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_v_2074_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_r_2174_);
lean_ctor_set(v_reuseFailAlloc_2198_, 4, v_impl_2114_);
v___x_2185_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
v_isSharedCheck_2192_ = !lean_is_exclusive(v_r_2174_);
if (v_isSharedCheck_2192_ == 0)
{
lean_object* v_unused_2193_; lean_object* v_unused_2194_; lean_object* v_unused_2195_; lean_object* v_unused_2196_; lean_object* v_unused_2197_; 
v_unused_2193_ = lean_ctor_get(v_r_2174_, 4);
lean_dec(v_unused_2193_);
v_unused_2194_ = lean_ctor_get(v_r_2174_, 3);
lean_dec(v_unused_2194_);
v_unused_2195_ = lean_ctor_get(v_r_2174_, 2);
lean_dec(v_unused_2195_);
v_unused_2196_ = lean_ctor_get(v_r_2174_, 1);
lean_dec(v_unused_2196_);
v_unused_2197_ = lean_ctor_get(v_r_2174_, 0);
lean_dec(v_unused_2197_);
v___x_2187_ = v_r_2174_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_dec(v_r_2174_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 4, v___x_2185_);
lean_ctor_set(v___x_2187_, 3, v_l_2173_);
lean_ctor_set(v___x_2187_, 2, v_v_2177_);
lean_ctor_set(v___x_2187_, 1, v_k_2176_);
lean_ctor_set(v___x_2187_, 0, v___x_2182_);
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_k_2176_);
lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_v_2177_);
lean_ctor_set(v_reuseFailAlloc_2191_, 3, v_l_2173_);
lean_ctor_set(v_reuseFailAlloc_2191_, 4, v___x_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
else
{
lean_object* v_k_2202_; lean_object* v_v_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2212_; 
v_k_2202_ = lean_ctor_get(v_l_2075_, 1);
v_v_2203_ = lean_ctor_get(v_l_2075_, 2);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_l_2075_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; lean_object* v_unused_2214_; lean_object* v_unused_2215_; 
v_unused_2213_ = lean_ctor_get(v_l_2075_, 4);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v_l_2075_, 3);
lean_dec(v_unused_2214_);
v_unused_2215_ = lean_ctor_get(v_l_2075_, 0);
lean_dec(v_unused_2215_);
v___x_2205_ = v_l_2075_;
v_isShared_2206_ = v_isSharedCheck_2212_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_v_2203_);
lean_inc(v_k_2202_);
lean_dec(v_l_2075_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2212_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2207_ = lean_unsigned_to_nat(3u);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 3, v_r_2174_);
lean_ctor_set(v___x_2205_, 2, v_v_2074_);
lean_ctor_set(v___x_2205_, 1, v_k_2073_);
lean_ctor_set(v___x_2205_, 0, v___x_2115_);
v___x_2209_ = v___x_2205_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_k_2073_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_v_2074_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v_r_2174_);
lean_ctor_set(v_reuseFailAlloc_2211_, 4, v_r_2174_);
v___x_2209_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2210_; 
v___x_2210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2207_);
lean_ctor_set(v___x_2210_, 1, v_k_2202_);
lean_ctor_set(v___x_2210_, 2, v_v_2203_);
lean_ctor_set(v___x_2210_, 3, v_l_2173_);
lean_ctor_set(v___x_2210_, 4, v___x_2209_);
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_r_2216_; 
v_r_2216_ = lean_ctor_get(v_l_2075_, 4);
lean_inc(v_r_2216_);
if (lean_obj_tag(v_r_2216_) == 0)
{
lean_object* v_k_2217_; lean_object* v_v_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2239_; 
lean_inc(v_l_2173_);
v_k_2217_ = lean_ctor_get(v_l_2075_, 1);
v_v_2218_ = lean_ctor_get(v_l_2075_, 2);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_l_2075_);
if (v_isSharedCheck_2239_ == 0)
{
lean_object* v_unused_2240_; lean_object* v_unused_2241_; lean_object* v_unused_2242_; 
v_unused_2240_ = lean_ctor_get(v_l_2075_, 4);
lean_dec(v_unused_2240_);
v_unused_2241_ = lean_ctor_get(v_l_2075_, 3);
lean_dec(v_unused_2241_);
v_unused_2242_ = lean_ctor_get(v_l_2075_, 0);
lean_dec(v_unused_2242_);
v___x_2220_ = v_l_2075_;
v_isShared_2221_ = v_isSharedCheck_2239_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_v_2218_);
lean_inc(v_k_2217_);
lean_dec(v_l_2075_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2239_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v_k_2222_; lean_object* v_v_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2235_; 
v_k_2222_ = lean_ctor_get(v_r_2216_, 1);
v_v_2223_ = lean_ctor_get(v_r_2216_, 2);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_r_2216_);
if (v_isSharedCheck_2235_ == 0)
{
lean_object* v_unused_2236_; lean_object* v_unused_2237_; lean_object* v_unused_2238_; 
v_unused_2236_ = lean_ctor_get(v_r_2216_, 4);
lean_dec(v_unused_2236_);
v_unused_2237_ = lean_ctor_get(v_r_2216_, 3);
lean_dec(v_unused_2237_);
v_unused_2238_ = lean_ctor_get(v_r_2216_, 0);
lean_dec(v_unused_2238_);
v___x_2225_ = v_r_2216_;
v_isShared_2226_ = v_isSharedCheck_2235_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_v_2223_);
lean_inc(v_k_2222_);
lean_dec(v_r_2216_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2235_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2227_ = lean_unsigned_to_nat(3u);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 4, v_l_2173_);
lean_ctor_set(v___x_2225_, 3, v_l_2173_);
lean_ctor_set(v___x_2225_, 2, v_v_2218_);
lean_ctor_set(v___x_2225_, 1, v_k_2217_);
lean_ctor_set(v___x_2225_, 0, v___x_2115_);
v___x_2229_ = v___x_2225_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_k_2217_);
lean_ctor_set(v_reuseFailAlloc_2234_, 2, v_v_2218_);
lean_ctor_set(v_reuseFailAlloc_2234_, 3, v_l_2173_);
lean_ctor_set(v_reuseFailAlloc_2234_, 4, v_l_2173_);
v___x_2229_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
lean_object* v___x_2231_; 
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 4, v_l_2173_);
lean_ctor_set(v___x_2220_, 2, v_v_2074_);
lean_ctor_set(v___x_2220_, 1, v_k_2073_);
lean_ctor_set(v___x_2220_, 0, v___x_2115_);
v___x_2231_ = v___x_2220_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v_k_2073_);
lean_ctor_set(v_reuseFailAlloc_2233_, 2, v_v_2074_);
lean_ctor_set(v_reuseFailAlloc_2233_, 3, v_l_2173_);
lean_ctor_set(v_reuseFailAlloc_2233_, 4, v_l_2173_);
v___x_2231_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2232_; 
v___x_2232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2227_);
lean_ctor_set(v___x_2232_, 1, v_k_2222_);
lean_ctor_set(v___x_2232_, 2, v_v_2223_);
lean_ctor_set(v___x_2232_, 3, v___x_2229_);
lean_ctor_set(v___x_2232_, 4, v___x_2231_);
return v___x_2232_;
}
}
}
}
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2243_ = lean_unsigned_to_nat(2u);
v___x_2244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
lean_ctor_set(v___x_2244_, 1, v_k_2073_);
lean_ctor_set(v___x_2244_, 2, v_v_2074_);
lean_ctor_set(v___x_2244_, 3, v_l_2075_);
lean_ctor_set(v___x_2244_, 4, v_r_2216_);
return v___x_2244_;
}
}
}
else
{
lean_object* v___x_2245_; 
v___x_2245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2115_);
lean_ctor_set(v___x_2245_, 1, v_k_2073_);
lean_ctor_set(v___x_2245_, 2, v_v_2074_);
lean_ctor_set(v___x_2245_, 3, v_l_2075_);
lean_ctor_set(v___x_2245_, 4, v_l_2075_);
return v___x_2245_;
}
}
}
v___jp_2246_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = lean_nat_add(v___y_2251_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec(v___y_2251_);
v___x_2261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
lean_ctor_set(v___x_2261_, 1, v_k_2073_);
lean_ctor_set(v___x_2261_, 2, v_v_2074_);
lean_ctor_set(v___x_2261_, 3, v___y_2248_);
lean_ctor_set(v___x_2261_, 4, v___y_2250_);
v___x_2262_ = lean_nat_add(v___y_2257_, v___y_2247_);
lean_dec(v___y_2247_);
if (lean_obj_tag(v___y_2253_) == 0)
{
lean_object* v_size_2263_; 
v_size_2263_ = lean_ctor_get(v___y_2253_, 0);
lean_inc(v_size_2263_);
v___y_2060_ = v___x_2262_;
v___y_2061_ = v___y_2249_;
v___y_2062_ = v___y_2253_;
v___y_2063_ = v___y_2252_;
v___y_2064_ = v___y_2254_;
v___y_2065_ = v___x_2261_;
v___y_2066_ = v___y_2255_;
v___y_2067_ = v___y_2256_;
v___y_2068_ = v___y_2258_;
v___y_2069_ = v_size_2263_;
goto v___jp_2059_;
}
else
{
lean_object* v___x_2264_; 
v___x_2264_ = lean_unsigned_to_nat(0u);
v___y_2060_ = v___x_2262_;
v___y_2061_ = v___y_2249_;
v___y_2062_ = v___y_2253_;
v___y_2063_ = v___y_2252_;
v___y_2064_ = v___y_2254_;
v___y_2065_ = v___x_2261_;
v___y_2066_ = v___y_2255_;
v___y_2067_ = v___y_2256_;
v___y_2068_ = v___y_2258_;
v___y_2069_ = v___x_2264_;
goto v___jp_2059_;
}
}
v___jp_2265_:
{
lean_object* v_impl_2266_; lean_object* v___x_2267_; 
v_impl_2266_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v_k_2057_, v_l_2075_);
v___x_2267_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2266_) == 0)
{
if (lean_obj_tag(v_r_2076_) == 0)
{
lean_object* v_size_2268_; lean_object* v_size_2269_; lean_object* v_k_2270_; lean_object* v_v_2271_; lean_object* v_l_2272_; lean_object* v_r_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; uint8_t v___x_2276_; 
v_size_2268_ = lean_ctor_get(v_impl_2266_, 0);
lean_inc(v_size_2268_);
v_size_2269_ = lean_ctor_get(v_r_2076_, 0);
v_k_2270_ = lean_ctor_get(v_r_2076_, 1);
v_v_2271_ = lean_ctor_get(v_r_2076_, 2);
v_l_2272_ = lean_ctor_get(v_r_2076_, 3);
v_r_2273_ = lean_ctor_get(v_r_2076_, 4);
v___x_2274_ = lean_unsigned_to_nat(3u);
v___x_2275_ = lean_nat_mul(v___x_2274_, v_size_2268_);
v___x_2276_ = lean_nat_dec_lt(v___x_2275_, v_size_2269_);
lean_dec(v___x_2275_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = lean_nat_add(v___x_2267_, v_size_2268_);
lean_dec(v_size_2268_);
v___x_2278_ = lean_nat_add(v___x_2277_, v_size_2269_);
lean_dec(v___x_2277_);
v___x_2279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
lean_ctor_set(v___x_2279_, 1, v_k_2073_);
lean_ctor_set(v___x_2279_, 2, v_v_2074_);
lean_ctor_set(v___x_2279_, 3, v_impl_2266_);
lean_ctor_set(v___x_2279_, 4, v_r_2076_);
return v___x_2279_;
}
else
{
lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2314_; 
lean_inc(v_r_2273_);
lean_inc(v_l_2272_);
lean_inc(v_v_2271_);
lean_inc(v_k_2270_);
lean_inc(v_size_2269_);
v_isSharedCheck_2314_ = !lean_is_exclusive(v_r_2076_);
if (v_isSharedCheck_2314_ == 0)
{
lean_object* v_unused_2315_; lean_object* v_unused_2316_; lean_object* v_unused_2317_; lean_object* v_unused_2318_; lean_object* v_unused_2319_; 
v_unused_2315_ = lean_ctor_get(v_r_2076_, 4);
lean_dec(v_unused_2315_);
v_unused_2316_ = lean_ctor_get(v_r_2076_, 3);
lean_dec(v_unused_2316_);
v_unused_2317_ = lean_ctor_get(v_r_2076_, 2);
lean_dec(v_unused_2317_);
v_unused_2318_ = lean_ctor_get(v_r_2076_, 1);
lean_dec(v_unused_2318_);
v_unused_2319_ = lean_ctor_get(v_r_2076_, 0);
lean_dec(v_unused_2319_);
v___x_2281_ = v_r_2076_;
v_isShared_2282_ = v_isSharedCheck_2314_;
goto v_resetjp_2280_;
}
else
{
lean_dec(v_r_2076_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2314_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v_size_2283_; lean_object* v_k_2284_; lean_object* v_v_2285_; lean_object* v_l_2286_; lean_object* v_r_2287_; lean_object* v_size_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v_size_2283_ = lean_ctor_get(v_l_2272_, 0);
v_k_2284_ = lean_ctor_get(v_l_2272_, 1);
v_v_2285_ = lean_ctor_get(v_l_2272_, 2);
v_l_2286_ = lean_ctor_get(v_l_2272_, 3);
v_r_2287_ = lean_ctor_get(v_l_2272_, 4);
v_size_2288_ = lean_ctor_get(v_r_2273_, 0);
v___x_2289_ = lean_unsigned_to_nat(2u);
v___x_2290_ = lean_nat_mul(v___x_2289_, v_size_2288_);
v___x_2291_ = lean_nat_dec_lt(v_size_2283_, v___x_2290_);
lean_dec(v___x_2290_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_inc(v_size_2288_);
lean_inc(v_r_2287_);
lean_inc(v_l_2286_);
lean_inc(v_v_2285_);
lean_inc(v_k_2284_);
lean_del_object(v___x_2281_);
lean_dec(v_l_2272_);
v___x_2292_ = lean_nat_add(v___x_2267_, v_size_2268_);
lean_dec(v_size_2268_);
v___x_2293_ = lean_nat_add(v___x_2292_, v_size_2269_);
lean_dec(v_size_2269_);
if (lean_obj_tag(v_l_2286_) == 0)
{
lean_object* v_size_2294_; 
v_size_2294_ = lean_ctor_get(v_l_2286_, 0);
lean_inc(v_size_2294_);
v___y_2247_ = v_size_2288_;
v___y_2248_ = v_impl_2266_;
v___y_2249_ = v___x_2293_;
v___y_2250_ = v_l_2286_;
v___y_2251_ = v___x_2292_;
v___y_2252_ = v_k_2270_;
v___y_2253_ = v_r_2287_;
v___y_2254_ = v_v_2271_;
v___y_2255_ = v_k_2284_;
v___y_2256_ = v_r_2273_;
v___y_2257_ = v___x_2267_;
v___y_2258_ = v_v_2285_;
v___y_2259_ = v_size_2294_;
goto v___jp_2246_;
}
else
{
lean_object* v___x_2295_; 
v___x_2295_ = lean_unsigned_to_nat(0u);
v___y_2247_ = v_size_2288_;
v___y_2248_ = v_impl_2266_;
v___y_2249_ = v___x_2293_;
v___y_2250_ = v_l_2286_;
v___y_2251_ = v___x_2292_;
v___y_2252_ = v_k_2270_;
v___y_2253_ = v_r_2287_;
v___y_2254_ = v_v_2271_;
v___y_2255_ = v_k_2284_;
v___y_2256_ = v_r_2273_;
v___y_2257_ = v___x_2267_;
v___y_2258_ = v_v_2285_;
v___y_2259_ = v___x_2295_;
goto v___jp_2246_;
}
}
else
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2296_ = lean_nat_add(v___x_2267_, v_size_2268_);
lean_dec(v_size_2268_);
v___x_2297_ = lean_nat_add(v___x_2296_, v_size_2269_);
lean_dec(v_size_2269_);
v___x_2298_ = lean_nat_add(v___x_2296_, v_size_2283_);
lean_dec(v___x_2296_);
lean_inc_ref(v_impl_2266_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 4, v_l_2272_);
lean_ctor_set(v___x_2281_, 3, v_impl_2266_);
lean_ctor_set(v___x_2281_, 2, v_v_2074_);
lean_ctor_set(v___x_2281_, 1, v_k_2073_);
lean_ctor_set(v___x_2281_, 0, v___x_2298_);
v___x_2300_ = v___x_2281_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2298_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v_k_2073_);
lean_ctor_set(v_reuseFailAlloc_2313_, 2, v_v_2074_);
lean_ctor_set(v_reuseFailAlloc_2313_, 3, v_impl_2266_);
lean_ctor_set(v_reuseFailAlloc_2313_, 4, v_l_2272_);
v___x_2300_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
v_isSharedCheck_2307_ = !lean_is_exclusive(v_impl_2266_);
if (v_isSharedCheck_2307_ == 0)
{
lean_object* v_unused_2308_; lean_object* v_unused_2309_; lean_object* v_unused_2310_; lean_object* v_unused_2311_; lean_object* v_unused_2312_; 
v_unused_2308_ = lean_ctor_get(v_impl_2266_, 4);
lean_dec(v_unused_2308_);
v_unused_2309_ = lean_ctor_get(v_impl_2266_, 3);
lean_dec(v_unused_2309_);
v_unused_2310_ = lean_ctor_get(v_impl_2266_, 2);
lean_dec(v_unused_2310_);
v_unused_2311_ = lean_ctor_get(v_impl_2266_, 1);
lean_dec(v_unused_2311_);
v_unused_2312_ = lean_ctor_get(v_impl_2266_, 0);
lean_dec(v_unused_2312_);
v___x_2302_ = v_impl_2266_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_dec(v_impl_2266_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 4, v_r_2273_);
lean_ctor_set(v___x_2302_, 3, v___x_2300_);
lean_ctor_set(v___x_2302_, 2, v_v_2271_);
lean_ctor_set(v___x_2302_, 1, v_k_2270_);
lean_ctor_set(v___x_2302_, 0, v___x_2297_);
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2297_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v_k_2270_);
lean_ctor_set(v_reuseFailAlloc_2306_, 2, v_v_2271_);
lean_ctor_set(v_reuseFailAlloc_2306_, 3, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2306_, 4, v_r_2273_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v_size_2320_ = lean_ctor_get(v_impl_2266_, 0);
lean_inc(v_size_2320_);
v___x_2321_ = lean_nat_add(v___x_2267_, v_size_2320_);
lean_dec(v_size_2320_);
v___x_2322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
lean_ctor_set(v___x_2322_, 1, v_k_2073_);
lean_ctor_set(v___x_2322_, 2, v_v_2074_);
lean_ctor_set(v___x_2322_, 3, v_impl_2266_);
lean_ctor_set(v___x_2322_, 4, v_r_2076_);
return v___x_2322_;
}
}
else
{
if (lean_obj_tag(v_r_2076_) == 0)
{
lean_object* v_l_2323_; 
v_l_2323_ = lean_ctor_get(v_r_2076_, 3);
lean_inc(v_l_2323_);
if (lean_obj_tag(v_l_2323_) == 0)
{
lean_object* v_r_2324_; 
v_r_2324_ = lean_ctor_get(v_r_2076_, 4);
lean_inc(v_r_2324_);
if (lean_obj_tag(v_r_2324_) == 0)
{
lean_object* v_size_2325_; lean_object* v_k_2326_; lean_object* v_v_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2338_; 
v_size_2325_ = lean_ctor_get(v_r_2076_, 0);
v_k_2326_ = lean_ctor_get(v_r_2076_, 1);
v_v_2327_ = lean_ctor_get(v_r_2076_, 2);
v_isSharedCheck_2338_ = !lean_is_exclusive(v_r_2076_);
if (v_isSharedCheck_2338_ == 0)
{
lean_object* v_unused_2339_; lean_object* v_unused_2340_; 
v_unused_2339_ = lean_ctor_get(v_r_2076_, 4);
lean_dec(v_unused_2339_);
v_unused_2340_ = lean_ctor_get(v_r_2076_, 3);
lean_dec(v_unused_2340_);
v___x_2329_ = v_r_2076_;
v_isShared_2330_ = v_isSharedCheck_2338_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_v_2327_);
lean_inc(v_k_2326_);
lean_inc(v_size_2325_);
lean_dec(v_r_2076_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2338_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v_size_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
v_size_2331_ = lean_ctor_get(v_l_2323_, 0);
v___x_2332_ = lean_nat_add(v___x_2267_, v_size_2325_);
lean_dec(v_size_2325_);
v___x_2333_ = lean_nat_add(v___x_2267_, v_size_2331_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 4, v_l_2323_);
lean_ctor_set(v___x_2329_, 3, v_impl_2266_);
lean_ctor_set(v___x_2329_, 2, v_v_2074_);
lean_ctor_set(v___x_2329_, 1, v_k_2073_);
lean_ctor_set(v___x_2329_, 0, v___x_2333_);
v___x_2335_ = v___x_2329_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2333_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_k_2073_);
lean_ctor_set(v_reuseFailAlloc_2337_, 2, v_v_2074_);
lean_ctor_set(v_reuseFailAlloc_2337_, 3, v_impl_2266_);
lean_ctor_set(v_reuseFailAlloc_2337_, 4, v_l_2323_);
v___x_2335_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2336_; 
v___x_2336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2332_);
lean_ctor_set(v___x_2336_, 1, v_k_2326_);
lean_ctor_set(v___x_2336_, 2, v_v_2327_);
lean_ctor_set(v___x_2336_, 3, v___x_2335_);
lean_ctor_set(v___x_2336_, 4, v_r_2324_);
return v___x_2336_;
}
}
}
else
{
lean_object* v_k_2341_; lean_object* v_v_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2363_; 
v_k_2341_ = lean_ctor_get(v_r_2076_, 1);
v_v_2342_ = lean_ctor_get(v_r_2076_, 2);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_r_2076_);
if (v_isSharedCheck_2363_ == 0)
{
lean_object* v_unused_2364_; lean_object* v_unused_2365_; lean_object* v_unused_2366_; 
v_unused_2364_ = lean_ctor_get(v_r_2076_, 4);
lean_dec(v_unused_2364_);
v_unused_2365_ = lean_ctor_get(v_r_2076_, 3);
lean_dec(v_unused_2365_);
v_unused_2366_ = lean_ctor_get(v_r_2076_, 0);
lean_dec(v_unused_2366_);
v___x_2344_ = v_r_2076_;
v_isShared_2345_ = v_isSharedCheck_2363_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_v_2342_);
lean_inc(v_k_2341_);
lean_dec(v_r_2076_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2363_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v_k_2346_; lean_object* v_v_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2359_; 
v_k_2346_ = lean_ctor_get(v_l_2323_, 1);
v_v_2347_ = lean_ctor_get(v_l_2323_, 2);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_l_2323_);
if (v_isSharedCheck_2359_ == 0)
{
lean_object* v_unused_2360_; lean_object* v_unused_2361_; lean_object* v_unused_2362_; 
v_unused_2360_ = lean_ctor_get(v_l_2323_, 4);
lean_dec(v_unused_2360_);
v_unused_2361_ = lean_ctor_get(v_l_2323_, 3);
lean_dec(v_unused_2361_);
v_unused_2362_ = lean_ctor_get(v_l_2323_, 0);
lean_dec(v_unused_2362_);
v___x_2349_ = v_l_2323_;
v_isShared_2350_ = v_isSharedCheck_2359_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_v_2347_);
lean_inc(v_k_2346_);
lean_dec(v_l_2323_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2359_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2351_ = lean_unsigned_to_nat(3u);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 4, v_r_2324_);
lean_ctor_set(v___x_2349_, 3, v_r_2324_);
lean_ctor_set(v___x_2349_, 2, v_v_2074_);
lean_ctor_set(v___x_2349_, 1, v_k_2073_);
lean_ctor_set(v___x_2349_, 0, v___x_2267_);
v___x_2353_ = v___x_2349_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2267_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_k_2073_);
lean_ctor_set(v_reuseFailAlloc_2358_, 2, v_v_2074_);
lean_ctor_set(v_reuseFailAlloc_2358_, 3, v_r_2324_);
lean_ctor_set(v_reuseFailAlloc_2358_, 4, v_r_2324_);
v___x_2353_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2355_; 
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 3, v_r_2324_);
lean_ctor_set(v___x_2344_, 0, v___x_2267_);
v___x_2355_ = v___x_2344_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2267_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_k_2341_);
lean_ctor_set(v_reuseFailAlloc_2357_, 2, v_v_2342_);
lean_ctor_set(v_reuseFailAlloc_2357_, 3, v_r_2324_);
lean_ctor_set(v_reuseFailAlloc_2357_, 4, v_r_2324_);
v___x_2355_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2356_; 
v___x_2356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2351_);
lean_ctor_set(v___x_2356_, 1, v_k_2346_);
lean_ctor_set(v___x_2356_, 2, v_v_2347_);
lean_ctor_set(v___x_2356_, 3, v___x_2353_);
lean_ctor_set(v___x_2356_, 4, v___x_2355_);
return v___x_2356_;
}
}
}
}
}
}
else
{
lean_object* v_r_2367_; 
v_r_2367_ = lean_ctor_get(v_r_2076_, 4);
lean_inc(v_r_2367_);
if (lean_obj_tag(v_r_2367_) == 0)
{
lean_object* v_k_2368_; lean_object* v_v_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2378_; 
v_k_2368_ = lean_ctor_get(v_r_2076_, 1);
v_v_2369_ = lean_ctor_get(v_r_2076_, 2);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_r_2076_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; lean_object* v_unused_2380_; lean_object* v_unused_2381_; 
v_unused_2379_ = lean_ctor_get(v_r_2076_, 4);
lean_dec(v_unused_2379_);
v_unused_2380_ = lean_ctor_get(v_r_2076_, 3);
lean_dec(v_unused_2380_);
v_unused_2381_ = lean_ctor_get(v_r_2076_, 0);
lean_dec(v_unused_2381_);
v___x_2371_ = v_r_2076_;
v_isShared_2372_ = v_isSharedCheck_2378_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_v_2369_);
lean_inc(v_k_2368_);
lean_dec(v_r_2076_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2378_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; lean_object* v___x_2375_; 
v___x_2373_ = lean_unsigned_to_nat(3u);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 4, v_l_2323_);
lean_ctor_set(v___x_2371_, 2, v_v_2074_);
lean_ctor_set(v___x_2371_, 1, v_k_2073_);
lean_ctor_set(v___x_2371_, 0, v___x_2267_);
v___x_2375_ = v___x_2371_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2267_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_k_2073_);
lean_ctor_set(v_reuseFailAlloc_2377_, 2, v_v_2074_);
lean_ctor_set(v_reuseFailAlloc_2377_, 3, v_l_2323_);
lean_ctor_set(v_reuseFailAlloc_2377_, 4, v_l_2323_);
v___x_2375_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2376_; 
v___x_2376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2373_);
lean_ctor_set(v___x_2376_, 1, v_k_2368_);
lean_ctor_set(v___x_2376_, 2, v_v_2369_);
lean_ctor_set(v___x_2376_, 3, v___x_2375_);
lean_ctor_set(v___x_2376_, 4, v_r_2367_);
return v___x_2376_;
}
}
}
else
{
lean_object* v_size_2382_; lean_object* v_k_2383_; lean_object* v_v_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2393_; 
v_size_2382_ = lean_ctor_get(v_r_2076_, 0);
v_k_2383_ = lean_ctor_get(v_r_2076_, 1);
v_v_2384_ = lean_ctor_get(v_r_2076_, 2);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_r_2076_);
if (v_isSharedCheck_2393_ == 0)
{
lean_object* v_unused_2394_; lean_object* v_unused_2395_; 
v_unused_2394_ = lean_ctor_get(v_r_2076_, 4);
lean_dec(v_unused_2394_);
v_unused_2395_ = lean_ctor_get(v_r_2076_, 3);
lean_dec(v_unused_2395_);
v___x_2386_ = v_r_2076_;
v_isShared_2387_ = v_isSharedCheck_2393_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_v_2384_);
lean_inc(v_k_2383_);
lean_inc(v_size_2382_);
lean_dec(v_r_2076_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2393_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 3, v_r_2367_);
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_size_2382_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v_k_2383_);
lean_ctor_set(v_reuseFailAlloc_2392_, 2, v_v_2384_);
lean_ctor_set(v_reuseFailAlloc_2392_, 3, v_r_2367_);
lean_ctor_set(v_reuseFailAlloc_2392_, 4, v_r_2367_);
v___x_2389_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_unsigned_to_nat(2u);
v___x_2391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
lean_ctor_set(v___x_2391_, 1, v_k_2073_);
lean_ctor_set(v___x_2391_, 2, v_v_2074_);
lean_ctor_set(v___x_2391_, 3, v_r_2367_);
lean_ctor_set(v___x_2391_, 4, v___x_2389_);
return v___x_2391_;
}
}
}
}
}
else
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2267_);
lean_ctor_set(v___x_2396_, 1, v_k_2073_);
lean_ctor_set(v___x_2396_, 2, v_v_2074_);
lean_ctor_set(v___x_2396_, 3, v_r_2076_);
lean_ctor_set(v___x_2396_, 4, v_r_2076_);
return v___x_2396_;
}
}
}
}
}
else
{
return v_t_2058_;
}
v___jp_2059_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2070_ = lean_nat_add(v___y_2060_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec(v___y_2060_);
v___x_2071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v___y_2063_);
lean_ctor_set(v___x_2071_, 2, v___y_2064_);
lean_ctor_set(v___x_2071_, 3, v___y_2062_);
lean_ctor_set(v___x_2071_, 4, v___y_2067_);
v___x_2072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2072_, 0, v___y_2061_);
lean_ctor_set(v___x_2072_, 1, v___y_2066_);
lean_ctor_set(v___x_2072_, 2, v___y_2068_);
lean_ctor_set(v___x_2072_, 3, v___y_2065_);
lean_ctor_set(v___x_2072_, 4, v___x_2071_);
return v___x_2072_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg___boxed(lean_object* v_k_2721_, lean_object* v_t_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v_k_2721_, v_t_2722_);
lean_dec_ref(v_k_2721_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(lean_object* v_k_2724_, lean_object* v_v_2725_, lean_object* v_t_2726_){
_start:
{
lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v___y_2737_; 
if (lean_obj_tag(v_t_2726_) == 0)
{
lean_object* v_size_2741_; lean_object* v_k_2742_; lean_object* v_v_2743_; lean_object* v_l_2744_; lean_object* v_r_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_3010_; 
v_size_2741_ = lean_ctor_get(v_t_2726_, 0);
v_k_2742_ = lean_ctor_get(v_t_2726_, 1);
v_v_2743_ = lean_ctor_get(v_t_2726_, 2);
v_l_2744_ = lean_ctor_get(v_t_2726_, 3);
v_r_2745_ = lean_ctor_get(v_t_2726_, 4);
v_isSharedCheck_3010_ = !lean_is_exclusive(v_t_2726_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_2747_ = v_t_2726_;
v_isShared_2748_ = v_isSharedCheck_3010_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_r_2745_);
lean_inc(v_l_2744_);
lean_inc(v_v_2743_);
lean_inc(v_k_2742_);
lean_inc(v_size_2741_);
lean_dec(v_t_2726_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_3010_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v_fst_2998_; lean_object* v_snd_2999_; lean_object* v_fst_3000_; lean_object* v_snd_3001_; double v___x_3002_; double v___x_3003_; uint8_t v___x_3004_; 
v_fst_2998_ = lean_ctor_get(v_k_2724_, 0);
v_snd_2999_ = lean_ctor_get(v_k_2724_, 1);
v_fst_3000_ = lean_ctor_get(v_k_2742_, 0);
v_snd_3001_ = lean_ctor_get(v_k_2742_, 1);
v___x_3002_ = lean_unbox_float(v_fst_2998_);
v___x_3003_ = lean_unbox_float(v_fst_3000_);
v___x_3004_ = lean_float_decLt(v___x_3002_, v___x_3003_);
if (v___x_3004_ == 0)
{
double v___x_3005_; double v___x_3006_; uint8_t v___x_3007_; 
v___x_3005_ = lean_unbox_float(v_fst_3000_);
v___x_3006_ = lean_unbox_float(v_fst_2998_);
v___x_3007_ = lean_float_decLt(v___x_3005_, v___x_3006_);
if (v___x_3007_ == 0)
{
uint8_t v___x_3008_; 
v___x_3008_ = l_Lean_Name_cmp(v_snd_2999_, v_snd_3001_);
switch(v___x_3008_)
{
case 0:
{
lean_del_object(v___x_2747_);
lean_dec(v_size_2741_);
goto v___jp_2897_;
}
case 1:
{
lean_object* v___x_3009_; 
lean_del_object(v___x_2747_);
lean_dec(v_v_2743_);
lean_dec(v_k_2742_);
v___x_3009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3009_, 0, v_size_2741_);
lean_ctor_set(v___x_3009_, 1, v_k_2724_);
lean_ctor_set(v___x_3009_, 2, v_v_2725_);
lean_ctor_set(v___x_3009_, 3, v_l_2744_);
lean_ctor_set(v___x_3009_, 4, v_r_2745_);
return v___x_3009_;
}
default: 
{
lean_dec(v_size_2741_);
goto v___jp_2769_;
}
}
}
else
{
lean_dec(v_size_2741_);
goto v___jp_2769_;
}
}
else
{
lean_del_object(v___x_2747_);
lean_dec(v_size_2741_);
goto v___jp_2897_;
}
v___jp_2749_:
{
lean_object* v___x_2762_; lean_object* v___x_2764_; 
v___x_2762_ = lean_nat_add(v___y_2755_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec(v___y_2755_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 4, v___y_2756_);
lean_ctor_set(v___x_2747_, 0, v___x_2762_);
v___x_2764_ = v___x_2747_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2762_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_2768_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_2768_, 3, v_l_2744_);
lean_ctor_set(v_reuseFailAlloc_2768_, 4, v___y_2756_);
v___x_2764_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
lean_object* v___x_2765_; 
v___x_2765_ = lean_nat_add(v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
if (lean_obj_tag(v___y_2753_) == 0)
{
lean_object* v_size_2766_; 
v_size_2766_ = lean_ctor_get(v___y_2753_, 0);
lean_inc(v_size_2766_);
v___y_2728_ = v___y_2750_;
v___y_2729_ = v___y_2751_;
v___y_2730_ = v___y_2752_;
v___y_2731_ = v___x_2765_;
v___y_2732_ = v___y_2753_;
v___y_2733_ = v___x_2764_;
v___y_2734_ = v___y_2754_;
v___y_2735_ = v___y_2758_;
v___y_2736_ = v___y_2757_;
v___y_2737_ = v_size_2766_;
goto v___jp_2727_;
}
else
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_unsigned_to_nat(0u);
v___y_2728_ = v___y_2750_;
v___y_2729_ = v___y_2751_;
v___y_2730_ = v___y_2752_;
v___y_2731_ = v___x_2765_;
v___y_2732_ = v___y_2753_;
v___y_2733_ = v___x_2764_;
v___y_2734_ = v___y_2754_;
v___y_2735_ = v___y_2758_;
v___y_2736_ = v___y_2757_;
v___y_2737_ = v___x_2767_;
goto v___jp_2727_;
}
}
}
v___jp_2769_:
{
lean_object* v_impl_2770_; lean_object* v___x_2771_; 
v_impl_2770_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(v_k_2724_, v_v_2725_, v_r_2745_);
v___x_2771_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2744_) == 0)
{
lean_object* v_size_2772_; lean_object* v_size_2773_; lean_object* v_k_2774_; lean_object* v_v_2775_; lean_object* v_l_2776_; lean_object* v_r_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; uint8_t v___x_2780_; 
v_size_2772_ = lean_ctor_get(v_l_2744_, 0);
v_size_2773_ = lean_ctor_get(v_impl_2770_, 0);
lean_inc(v_size_2773_);
v_k_2774_ = lean_ctor_get(v_impl_2770_, 1);
lean_inc(v_k_2774_);
v_v_2775_ = lean_ctor_get(v_impl_2770_, 2);
lean_inc(v_v_2775_);
v_l_2776_ = lean_ctor_get(v_impl_2770_, 3);
lean_inc(v_l_2776_);
v_r_2777_ = lean_ctor_get(v_impl_2770_, 4);
lean_inc(v_r_2777_);
v___x_2778_ = lean_unsigned_to_nat(3u);
v___x_2779_ = lean_nat_mul(v___x_2778_, v_size_2772_);
v___x_2780_ = lean_nat_dec_lt(v___x_2779_, v_size_2773_);
lean_dec(v___x_2779_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
lean_dec(v_r_2777_);
lean_dec(v_l_2776_);
lean_dec(v_v_2775_);
lean_dec(v_k_2774_);
lean_del_object(v___x_2747_);
v___x_2781_ = lean_nat_add(v___x_2771_, v_size_2772_);
v___x_2782_ = lean_nat_add(v___x_2781_, v_size_2773_);
lean_dec(v_size_2773_);
lean_dec(v___x_2781_);
v___x_2783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
lean_ctor_set(v___x_2783_, 1, v_k_2742_);
lean_ctor_set(v___x_2783_, 2, v_v_2743_);
lean_ctor_set(v___x_2783_, 3, v_l_2744_);
lean_ctor_set(v___x_2783_, 4, v_impl_2770_);
return v___x_2783_;
}
else
{
lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2818_; 
v_isSharedCheck_2818_ = !lean_is_exclusive(v_impl_2770_);
if (v_isSharedCheck_2818_ == 0)
{
lean_object* v_unused_2819_; lean_object* v_unused_2820_; lean_object* v_unused_2821_; lean_object* v_unused_2822_; lean_object* v_unused_2823_; 
v_unused_2819_ = lean_ctor_get(v_impl_2770_, 4);
lean_dec(v_unused_2819_);
v_unused_2820_ = lean_ctor_get(v_impl_2770_, 3);
lean_dec(v_unused_2820_);
v_unused_2821_ = lean_ctor_get(v_impl_2770_, 2);
lean_dec(v_unused_2821_);
v_unused_2822_ = lean_ctor_get(v_impl_2770_, 1);
lean_dec(v_unused_2822_);
v_unused_2823_ = lean_ctor_get(v_impl_2770_, 0);
lean_dec(v_unused_2823_);
v___x_2785_ = v_impl_2770_;
v_isShared_2786_ = v_isSharedCheck_2818_;
goto v_resetjp_2784_;
}
else
{
lean_dec(v_impl_2770_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2818_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v_size_2787_; lean_object* v_k_2788_; lean_object* v_v_2789_; lean_object* v_l_2790_; lean_object* v_r_2791_; lean_object* v_size_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; uint8_t v___x_2795_; 
v_size_2787_ = lean_ctor_get(v_l_2776_, 0);
v_k_2788_ = lean_ctor_get(v_l_2776_, 1);
v_v_2789_ = lean_ctor_get(v_l_2776_, 2);
v_l_2790_ = lean_ctor_get(v_l_2776_, 3);
v_r_2791_ = lean_ctor_get(v_l_2776_, 4);
v_size_2792_ = lean_ctor_get(v_r_2777_, 0);
v___x_2793_ = lean_unsigned_to_nat(2u);
v___x_2794_ = lean_nat_mul(v___x_2793_, v_size_2792_);
v___x_2795_ = lean_nat_dec_lt(v_size_2787_, v___x_2794_);
lean_dec(v___x_2794_);
if (v___x_2795_ == 0)
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
lean_inc(v_size_2792_);
lean_inc(v_r_2791_);
lean_inc(v_l_2790_);
lean_inc(v_v_2789_);
lean_inc(v_k_2788_);
lean_del_object(v___x_2785_);
lean_dec(v_l_2776_);
v___x_2796_ = lean_nat_add(v___x_2771_, v_size_2772_);
v___x_2797_ = lean_nat_add(v___x_2796_, v_size_2773_);
lean_dec(v_size_2773_);
if (lean_obj_tag(v_l_2790_) == 0)
{
lean_object* v_size_2798_; 
v_size_2798_ = lean_ctor_get(v_l_2790_, 0);
lean_inc(v_size_2798_);
v___y_2750_ = v___x_2797_;
v___y_2751_ = v_k_2788_;
v___y_2752_ = v_r_2777_;
v___y_2753_ = v_r_2791_;
v___y_2754_ = v_v_2789_;
v___y_2755_ = v___x_2796_;
v___y_2756_ = v_l_2790_;
v___y_2757_ = v_k_2774_;
v___y_2758_ = v_v_2775_;
v___y_2759_ = v___x_2771_;
v___y_2760_ = v_size_2792_;
v___y_2761_ = v_size_2798_;
goto v___jp_2749_;
}
else
{
lean_object* v___x_2799_; 
v___x_2799_ = lean_unsigned_to_nat(0u);
v___y_2750_ = v___x_2797_;
v___y_2751_ = v_k_2788_;
v___y_2752_ = v_r_2777_;
v___y_2753_ = v_r_2791_;
v___y_2754_ = v_v_2789_;
v___y_2755_ = v___x_2796_;
v___y_2756_ = v_l_2790_;
v___y_2757_ = v_k_2774_;
v___y_2758_ = v_v_2775_;
v___y_2759_ = v___x_2771_;
v___y_2760_ = v_size_2792_;
v___y_2761_ = v___x_2799_;
goto v___jp_2749_;
}
}
else
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2804_; 
lean_del_object(v___x_2747_);
v___x_2800_ = lean_nat_add(v___x_2771_, v_size_2772_);
v___x_2801_ = lean_nat_add(v___x_2800_, v_size_2773_);
lean_dec(v_size_2773_);
v___x_2802_ = lean_nat_add(v___x_2800_, v_size_2787_);
lean_dec(v___x_2800_);
lean_inc_ref(v_l_2744_);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 4, v_l_2776_);
lean_ctor_set(v___x_2785_, 3, v_l_2744_);
lean_ctor_set(v___x_2785_, 2, v_v_2743_);
lean_ctor_set(v___x_2785_, 1, v_k_2742_);
lean_ctor_set(v___x_2785_, 0, v___x_2802_);
v___x_2804_ = v___x_2785_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2802_);
lean_ctor_set(v_reuseFailAlloc_2817_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_2817_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_2817_, 3, v_l_2744_);
lean_ctor_set(v_reuseFailAlloc_2817_, 4, v_l_2776_);
v___x_2804_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
v_isSharedCheck_2811_ = !lean_is_exclusive(v_l_2744_);
if (v_isSharedCheck_2811_ == 0)
{
lean_object* v_unused_2812_; lean_object* v_unused_2813_; lean_object* v_unused_2814_; lean_object* v_unused_2815_; lean_object* v_unused_2816_; 
v_unused_2812_ = lean_ctor_get(v_l_2744_, 4);
lean_dec(v_unused_2812_);
v_unused_2813_ = lean_ctor_get(v_l_2744_, 3);
lean_dec(v_unused_2813_);
v_unused_2814_ = lean_ctor_get(v_l_2744_, 2);
lean_dec(v_unused_2814_);
v_unused_2815_ = lean_ctor_get(v_l_2744_, 1);
lean_dec(v_unused_2815_);
v_unused_2816_ = lean_ctor_get(v_l_2744_, 0);
lean_dec(v_unused_2816_);
v___x_2806_ = v_l_2744_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_dec(v_l_2744_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 4, v_r_2777_);
lean_ctor_set(v___x_2806_, 3, v___x_2804_);
lean_ctor_set(v___x_2806_, 2, v_v_2775_);
lean_ctor_set(v___x_2806_, 1, v_k_2774_);
lean_ctor_set(v___x_2806_, 0, v___x_2801_);
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2801_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v_k_2774_);
lean_ctor_set(v_reuseFailAlloc_2810_, 2, v_v_2775_);
lean_ctor_set(v_reuseFailAlloc_2810_, 3, v___x_2804_);
lean_ctor_set(v_reuseFailAlloc_2810_, 4, v_r_2777_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2824_; 
lean_del_object(v___x_2747_);
v_l_2824_ = lean_ctor_get(v_impl_2770_, 3);
lean_inc(v_l_2824_);
if (lean_obj_tag(v_l_2824_) == 0)
{
lean_object* v_r_2825_; lean_object* v_k_2826_; lean_object* v_v_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2848_; 
v_r_2825_ = lean_ctor_get(v_impl_2770_, 4);
v_k_2826_ = lean_ctor_get(v_impl_2770_, 1);
v_v_2827_ = lean_ctor_get(v_impl_2770_, 2);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_impl_2770_);
if (v_isSharedCheck_2848_ == 0)
{
lean_object* v_unused_2849_; lean_object* v_unused_2850_; 
v_unused_2849_ = lean_ctor_get(v_impl_2770_, 3);
lean_dec(v_unused_2849_);
v_unused_2850_ = lean_ctor_get(v_impl_2770_, 0);
lean_dec(v_unused_2850_);
v___x_2829_ = v_impl_2770_;
v_isShared_2830_ = v_isSharedCheck_2848_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_r_2825_);
lean_inc(v_v_2827_);
lean_inc(v_k_2826_);
lean_dec(v_impl_2770_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2848_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v_k_2831_; lean_object* v_v_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2844_; 
v_k_2831_ = lean_ctor_get(v_l_2824_, 1);
v_v_2832_ = lean_ctor_get(v_l_2824_, 2);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_l_2824_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; lean_object* v_unused_2846_; lean_object* v_unused_2847_; 
v_unused_2845_ = lean_ctor_get(v_l_2824_, 4);
lean_dec(v_unused_2845_);
v_unused_2846_ = lean_ctor_get(v_l_2824_, 3);
lean_dec(v_unused_2846_);
v_unused_2847_ = lean_ctor_get(v_l_2824_, 0);
lean_dec(v_unused_2847_);
v___x_2834_ = v_l_2824_;
v_isShared_2835_ = v_isSharedCheck_2844_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_v_2832_);
lean_inc(v_k_2831_);
lean_dec(v_l_2824_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2844_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2836_; lean_object* v___x_2838_; 
v___x_2836_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2825_, 2);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 4, v_r_2825_);
lean_ctor_set(v___x_2834_, 3, v_r_2825_);
lean_ctor_set(v___x_2834_, 2, v_v_2743_);
lean_ctor_set(v___x_2834_, 1, v_k_2742_);
lean_ctor_set(v___x_2834_, 0, v___x_2771_);
v___x_2838_ = v___x_2834_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_2843_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_2843_, 3, v_r_2825_);
lean_ctor_set(v_reuseFailAlloc_2843_, 4, v_r_2825_);
v___x_2838_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
lean_object* v___x_2840_; 
lean_inc(v_r_2825_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 3, v_r_2825_);
lean_ctor_set(v___x_2829_, 0, v___x_2771_);
v___x_2840_ = v___x_2829_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v_k_2826_);
lean_ctor_set(v_reuseFailAlloc_2842_, 2, v_v_2827_);
lean_ctor_set(v_reuseFailAlloc_2842_, 3, v_r_2825_);
lean_ctor_set(v_reuseFailAlloc_2842_, 4, v_r_2825_);
v___x_2840_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
lean_object* v___x_2841_; 
v___x_2841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2836_);
lean_ctor_set(v___x_2841_, 1, v_k_2831_);
lean_ctor_set(v___x_2841_, 2, v_v_2832_);
lean_ctor_set(v___x_2841_, 3, v___x_2838_);
lean_ctor_set(v___x_2841_, 4, v___x_2840_);
return v___x_2841_;
}
}
}
}
}
else
{
lean_object* v_r_2851_; 
v_r_2851_ = lean_ctor_get(v_impl_2770_, 4);
lean_inc(v_r_2851_);
if (lean_obj_tag(v_r_2851_) == 0)
{
lean_object* v_k_2852_; lean_object* v_v_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2862_; 
v_k_2852_ = lean_ctor_get(v_impl_2770_, 1);
v_v_2853_ = lean_ctor_get(v_impl_2770_, 2);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_impl_2770_);
if (v_isSharedCheck_2862_ == 0)
{
lean_object* v_unused_2863_; lean_object* v_unused_2864_; lean_object* v_unused_2865_; 
v_unused_2863_ = lean_ctor_get(v_impl_2770_, 4);
lean_dec(v_unused_2863_);
v_unused_2864_ = lean_ctor_get(v_impl_2770_, 3);
lean_dec(v_unused_2864_);
v_unused_2865_ = lean_ctor_get(v_impl_2770_, 0);
lean_dec(v_unused_2865_);
v___x_2855_ = v_impl_2770_;
v_isShared_2856_ = v_isSharedCheck_2862_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_v_2853_);
lean_inc(v_k_2852_);
lean_dec(v_impl_2770_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2862_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2857_ = lean_unsigned_to_nat(3u);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 4, v_l_2824_);
lean_ctor_set(v___x_2855_, 2, v_v_2743_);
lean_ctor_set(v___x_2855_, 1, v_k_2742_);
lean_ctor_set(v___x_2855_, 0, v___x_2771_);
v___x_2859_ = v___x_2855_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_2861_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_2861_, 3, v_l_2824_);
lean_ctor_set(v_reuseFailAlloc_2861_, 4, v_l_2824_);
v___x_2859_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2860_; 
v___x_2860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2857_);
lean_ctor_set(v___x_2860_, 1, v_k_2852_);
lean_ctor_set(v___x_2860_, 2, v_v_2853_);
lean_ctor_set(v___x_2860_, 3, v___x_2859_);
lean_ctor_set(v___x_2860_, 4, v_r_2851_);
return v___x_2860_;
}
}
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_unsigned_to_nat(2u);
v___x_2867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
lean_ctor_set(v___x_2867_, 1, v_k_2742_);
lean_ctor_set(v___x_2867_, 2, v_v_2743_);
lean_ctor_set(v___x_2867_, 3, v_r_2851_);
lean_ctor_set(v___x_2867_, 4, v_impl_2770_);
return v___x_2867_;
}
}
}
}
v___jp_2868_:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2876_ = lean_nat_add(v___y_2873_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec(v___y_2873_);
v___x_2877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
lean_ctor_set(v___x_2877_, 1, v_k_2742_);
lean_ctor_set(v___x_2877_, 2, v_v_2743_);
lean_ctor_set(v___x_2877_, 3, v___y_2870_);
lean_ctor_set(v___x_2877_, 4, v_r_2745_);
v___x_2878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2878_, 0, v___y_2872_);
lean_ctor_set(v___x_2878_, 1, v___y_2869_);
lean_ctor_set(v___x_2878_, 2, v___y_2871_);
lean_ctor_set(v___x_2878_, 3, v___y_2874_);
lean_ctor_set(v___x_2878_, 4, v___x_2877_);
return v___x_2878_;
}
v___jp_2879_:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2892_ = lean_nat_add(v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec(v___y_2890_);
v___x_2893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
lean_ctor_set(v___x_2893_, 1, v___y_2882_);
lean_ctor_set(v___x_2893_, 2, v___y_2885_);
lean_ctor_set(v___x_2893_, 3, v___y_2886_);
lean_ctor_set(v___x_2893_, 4, v___y_2881_);
v___x_2894_ = lean_nat_add(v___y_2889_, v___y_2880_);
lean_dec(v___y_2880_);
if (lean_obj_tag(v___y_2883_) == 0)
{
lean_object* v_size_2895_; 
v_size_2895_ = lean_ctor_get(v___y_2883_, 0);
lean_inc(v_size_2895_);
v___y_2869_ = v___y_2884_;
v___y_2870_ = v___y_2883_;
v___y_2871_ = v___y_2888_;
v___y_2872_ = v___y_2887_;
v___y_2873_ = v___x_2894_;
v___y_2874_ = v___x_2893_;
v___y_2875_ = v_size_2895_;
goto v___jp_2868_;
}
else
{
lean_object* v___x_2896_; 
v___x_2896_ = lean_unsigned_to_nat(0u);
v___y_2869_ = v___y_2884_;
v___y_2870_ = v___y_2883_;
v___y_2871_ = v___y_2888_;
v___y_2872_ = v___y_2887_;
v___y_2873_ = v___x_2894_;
v___y_2874_ = v___x_2893_;
v___y_2875_ = v___x_2896_;
goto v___jp_2868_;
}
}
v___jp_2897_:
{
lean_object* v_impl_2898_; lean_object* v___x_2899_; 
v_impl_2898_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(v_k_2724_, v_v_2725_, v_l_2744_);
v___x_2899_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2745_) == 0)
{
lean_object* v_size_2900_; lean_object* v_size_2901_; lean_object* v_k_2902_; lean_object* v_v_2903_; lean_object* v_l_2904_; lean_object* v_r_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; uint8_t v___x_2908_; 
v_size_2900_ = lean_ctor_get(v_r_2745_, 0);
v_size_2901_ = lean_ctor_get(v_impl_2898_, 0);
lean_inc(v_size_2901_);
v_k_2902_ = lean_ctor_get(v_impl_2898_, 1);
lean_inc(v_k_2902_);
v_v_2903_ = lean_ctor_get(v_impl_2898_, 2);
lean_inc(v_v_2903_);
v_l_2904_ = lean_ctor_get(v_impl_2898_, 3);
lean_inc(v_l_2904_);
v_r_2905_ = lean_ctor_get(v_impl_2898_, 4);
lean_inc(v_r_2905_);
v___x_2906_ = lean_unsigned_to_nat(3u);
v___x_2907_ = lean_nat_mul(v___x_2906_, v_size_2900_);
v___x_2908_ = lean_nat_dec_lt(v___x_2907_, v_size_2901_);
lean_dec(v___x_2907_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
lean_dec(v_r_2905_);
lean_dec(v_l_2904_);
lean_dec(v_v_2903_);
lean_dec(v_k_2902_);
v___x_2909_ = lean_nat_add(v___x_2899_, v_size_2901_);
lean_dec(v_size_2901_);
v___x_2910_ = lean_nat_add(v___x_2909_, v_size_2900_);
lean_dec(v___x_2909_);
v___x_2911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
lean_ctor_set(v___x_2911_, 1, v_k_2742_);
lean_ctor_set(v___x_2911_, 2, v_v_2743_);
lean_ctor_set(v___x_2911_, 3, v_impl_2898_);
lean_ctor_set(v___x_2911_, 4, v_r_2745_);
return v___x_2911_;
}
else
{
lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2948_; 
v_isSharedCheck_2948_ = !lean_is_exclusive(v_impl_2898_);
if (v_isSharedCheck_2948_ == 0)
{
lean_object* v_unused_2949_; lean_object* v_unused_2950_; lean_object* v_unused_2951_; lean_object* v_unused_2952_; lean_object* v_unused_2953_; 
v_unused_2949_ = lean_ctor_get(v_impl_2898_, 4);
lean_dec(v_unused_2949_);
v_unused_2950_ = lean_ctor_get(v_impl_2898_, 3);
lean_dec(v_unused_2950_);
v_unused_2951_ = lean_ctor_get(v_impl_2898_, 2);
lean_dec(v_unused_2951_);
v_unused_2952_ = lean_ctor_get(v_impl_2898_, 1);
lean_dec(v_unused_2952_);
v_unused_2953_ = lean_ctor_get(v_impl_2898_, 0);
lean_dec(v_unused_2953_);
v___x_2913_ = v_impl_2898_;
v_isShared_2914_ = v_isSharedCheck_2948_;
goto v_resetjp_2912_;
}
else
{
lean_dec(v_impl_2898_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2948_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v_size_2915_; lean_object* v_size_2916_; lean_object* v_k_2917_; lean_object* v_v_2918_; lean_object* v_l_2919_; lean_object* v_r_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; uint8_t v___x_2923_; 
v_size_2915_ = lean_ctor_get(v_l_2904_, 0);
v_size_2916_ = lean_ctor_get(v_r_2905_, 0);
v_k_2917_ = lean_ctor_get(v_r_2905_, 1);
v_v_2918_ = lean_ctor_get(v_r_2905_, 2);
v_l_2919_ = lean_ctor_get(v_r_2905_, 3);
v_r_2920_ = lean_ctor_get(v_r_2905_, 4);
v___x_2921_ = lean_unsigned_to_nat(2u);
v___x_2922_ = lean_nat_mul(v___x_2921_, v_size_2915_);
v___x_2923_ = lean_nat_dec_lt(v_size_2916_, v___x_2922_);
lean_dec(v___x_2922_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
lean_inc(v_r_2920_);
lean_inc(v_l_2919_);
lean_inc(v_v_2918_);
lean_inc(v_k_2917_);
lean_del_object(v___x_2913_);
lean_dec(v_r_2905_);
v___x_2924_ = lean_nat_add(v___x_2899_, v_size_2901_);
lean_dec(v_size_2901_);
v___x_2925_ = lean_nat_add(v___x_2924_, v_size_2900_);
lean_dec(v___x_2924_);
v___x_2926_ = lean_nat_add(v___x_2899_, v_size_2915_);
if (lean_obj_tag(v_l_2919_) == 0)
{
lean_object* v_size_2927_; 
v_size_2927_ = lean_ctor_get(v_l_2919_, 0);
lean_inc(v_size_2927_);
lean_inc(v_size_2900_);
v___y_2880_ = v_size_2900_;
v___y_2881_ = v_l_2919_;
v___y_2882_ = v_k_2902_;
v___y_2883_ = v_r_2920_;
v___y_2884_ = v_k_2917_;
v___y_2885_ = v_v_2903_;
v___y_2886_ = v_l_2904_;
v___y_2887_ = v___x_2925_;
v___y_2888_ = v_v_2918_;
v___y_2889_ = v___x_2899_;
v___y_2890_ = v___x_2926_;
v___y_2891_ = v_size_2927_;
goto v___jp_2879_;
}
else
{
lean_object* v___x_2928_; 
v___x_2928_ = lean_unsigned_to_nat(0u);
lean_inc(v_size_2900_);
v___y_2880_ = v_size_2900_;
v___y_2881_ = v_l_2919_;
v___y_2882_ = v_k_2902_;
v___y_2883_ = v_r_2920_;
v___y_2884_ = v_k_2917_;
v___y_2885_ = v_v_2903_;
v___y_2886_ = v_l_2904_;
v___y_2887_ = v___x_2925_;
v___y_2888_ = v_v_2918_;
v___y_2889_ = v___x_2899_;
v___y_2890_ = v___x_2926_;
v___y_2891_ = v___x_2928_;
goto v___jp_2879_;
}
}
else
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2934_; 
v___x_2929_ = lean_nat_add(v___x_2899_, v_size_2901_);
lean_dec(v_size_2901_);
v___x_2930_ = lean_nat_add(v___x_2929_, v_size_2900_);
lean_dec(v___x_2929_);
v___x_2931_ = lean_nat_add(v___x_2899_, v_size_2900_);
v___x_2932_ = lean_nat_add(v___x_2931_, v_size_2916_);
lean_dec(v___x_2931_);
lean_inc_ref(v_r_2745_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 4, v_r_2745_);
lean_ctor_set(v___x_2913_, 3, v_r_2905_);
lean_ctor_set(v___x_2913_, 2, v_v_2743_);
lean_ctor_set(v___x_2913_, 1, v_k_2742_);
lean_ctor_set(v___x_2913_, 0, v___x_2932_);
v___x_2934_ = v___x_2913_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_2947_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_2947_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_2947_, 3, v_r_2905_);
lean_ctor_set(v_reuseFailAlloc_2947_, 4, v_r_2745_);
v___x_2934_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
v_isSharedCheck_2941_ = !lean_is_exclusive(v_r_2745_);
if (v_isSharedCheck_2941_ == 0)
{
lean_object* v_unused_2942_; lean_object* v_unused_2943_; lean_object* v_unused_2944_; lean_object* v_unused_2945_; lean_object* v_unused_2946_; 
v_unused_2942_ = lean_ctor_get(v_r_2745_, 4);
lean_dec(v_unused_2942_);
v_unused_2943_ = lean_ctor_get(v_r_2745_, 3);
lean_dec(v_unused_2943_);
v_unused_2944_ = lean_ctor_get(v_r_2745_, 2);
lean_dec(v_unused_2944_);
v_unused_2945_ = lean_ctor_get(v_r_2745_, 1);
lean_dec(v_unused_2945_);
v_unused_2946_ = lean_ctor_get(v_r_2745_, 0);
lean_dec(v_unused_2946_);
v___x_2936_ = v_r_2745_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_dec(v_r_2745_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 4, v___x_2934_);
lean_ctor_set(v___x_2936_, 3, v_l_2904_);
lean_ctor_set(v___x_2936_, 2, v_v_2903_);
lean_ctor_set(v___x_2936_, 1, v_k_2902_);
lean_ctor_set(v___x_2936_, 0, v___x_2930_);
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_k_2902_);
lean_ctor_set(v_reuseFailAlloc_2940_, 2, v_v_2903_);
lean_ctor_set(v_reuseFailAlloc_2940_, 3, v_l_2904_);
lean_ctor_set(v_reuseFailAlloc_2940_, 4, v___x_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2954_; 
v_l_2954_ = lean_ctor_get(v_impl_2898_, 3);
lean_inc(v_l_2954_);
if (lean_obj_tag(v_l_2954_) == 0)
{
lean_object* v_r_2955_; lean_object* v_k_2956_; lean_object* v_v_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2966_; 
v_r_2955_ = lean_ctor_get(v_impl_2898_, 4);
v_k_2956_ = lean_ctor_get(v_impl_2898_, 1);
v_v_2957_ = lean_ctor_get(v_impl_2898_, 2);
v_isSharedCheck_2966_ = !lean_is_exclusive(v_impl_2898_);
if (v_isSharedCheck_2966_ == 0)
{
lean_object* v_unused_2967_; lean_object* v_unused_2968_; 
v_unused_2967_ = lean_ctor_get(v_impl_2898_, 3);
lean_dec(v_unused_2967_);
v_unused_2968_ = lean_ctor_get(v_impl_2898_, 0);
lean_dec(v_unused_2968_);
v___x_2959_ = v_impl_2898_;
v_isShared_2960_ = v_isSharedCheck_2966_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_r_2955_);
lean_inc(v_v_2957_);
lean_inc(v_k_2956_);
lean_dec(v_impl_2898_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2966_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; lean_object* v___x_2963_; 
v___x_2961_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2955_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 3, v_r_2955_);
lean_ctor_set(v___x_2959_, 2, v_v_2743_);
lean_ctor_set(v___x_2959_, 1, v_k_2742_);
lean_ctor_set(v___x_2959_, 0, v___x_2899_);
v___x_2963_ = v___x_2959_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2899_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_2965_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_2965_, 3, v_r_2955_);
lean_ctor_set(v_reuseFailAlloc_2965_, 4, v_r_2955_);
v___x_2963_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2964_; 
v___x_2964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2961_);
lean_ctor_set(v___x_2964_, 1, v_k_2956_);
lean_ctor_set(v___x_2964_, 2, v_v_2957_);
lean_ctor_set(v___x_2964_, 3, v_l_2954_);
lean_ctor_set(v___x_2964_, 4, v___x_2963_);
return v___x_2964_;
}
}
}
else
{
lean_object* v_r_2969_; 
v_r_2969_ = lean_ctor_get(v_impl_2898_, 4);
lean_inc(v_r_2969_);
if (lean_obj_tag(v_r_2969_) == 0)
{
lean_object* v_k_2970_; lean_object* v_v_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2992_; 
v_k_2970_ = lean_ctor_get(v_impl_2898_, 1);
v_v_2971_ = lean_ctor_get(v_impl_2898_, 2);
v_isSharedCheck_2992_ = !lean_is_exclusive(v_impl_2898_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; lean_object* v_unused_2994_; lean_object* v_unused_2995_; 
v_unused_2993_ = lean_ctor_get(v_impl_2898_, 4);
lean_dec(v_unused_2993_);
v_unused_2994_ = lean_ctor_get(v_impl_2898_, 3);
lean_dec(v_unused_2994_);
v_unused_2995_ = lean_ctor_get(v_impl_2898_, 0);
lean_dec(v_unused_2995_);
v___x_2973_ = v_impl_2898_;
v_isShared_2974_ = v_isSharedCheck_2992_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_v_2971_);
lean_inc(v_k_2970_);
lean_dec(v_impl_2898_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2992_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v_k_2975_; lean_object* v_v_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2988_; 
v_k_2975_ = lean_ctor_get(v_r_2969_, 1);
v_v_2976_ = lean_ctor_get(v_r_2969_, 2);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_r_2969_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; lean_object* v_unused_2990_; lean_object* v_unused_2991_; 
v_unused_2989_ = lean_ctor_get(v_r_2969_, 4);
lean_dec(v_unused_2989_);
v_unused_2990_ = lean_ctor_get(v_r_2969_, 3);
lean_dec(v_unused_2990_);
v_unused_2991_ = lean_ctor_get(v_r_2969_, 0);
lean_dec(v_unused_2991_);
v___x_2978_ = v_r_2969_;
v_isShared_2979_ = v_isSharedCheck_2988_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_v_2976_);
lean_inc(v_k_2975_);
lean_dec(v_r_2969_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2988_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; lean_object* v___x_2982_; 
v___x_2980_ = lean_unsigned_to_nat(3u);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 4, v_l_2954_);
lean_ctor_set(v___x_2978_, 3, v_l_2954_);
lean_ctor_set(v___x_2978_, 2, v_v_2971_);
lean_ctor_set(v___x_2978_, 1, v_k_2970_);
lean_ctor_set(v___x_2978_, 0, v___x_2899_);
v___x_2982_ = v___x_2978_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2899_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v_k_2970_);
lean_ctor_set(v_reuseFailAlloc_2987_, 2, v_v_2971_);
lean_ctor_set(v_reuseFailAlloc_2987_, 3, v_l_2954_);
lean_ctor_set(v_reuseFailAlloc_2987_, 4, v_l_2954_);
v___x_2982_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
lean_object* v___x_2984_; 
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 4, v_l_2954_);
lean_ctor_set(v___x_2973_, 2, v_v_2743_);
lean_ctor_set(v___x_2973_, 1, v_k_2742_);
lean_ctor_set(v___x_2973_, 0, v___x_2899_);
v___x_2984_ = v___x_2973_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2899_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_k_2742_);
lean_ctor_set(v_reuseFailAlloc_2986_, 2, v_v_2743_);
lean_ctor_set(v_reuseFailAlloc_2986_, 3, v_l_2954_);
lean_ctor_set(v_reuseFailAlloc_2986_, 4, v_l_2954_);
v___x_2984_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
lean_object* v___x_2985_; 
v___x_2985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2980_);
lean_ctor_set(v___x_2985_, 1, v_k_2975_);
lean_ctor_set(v___x_2985_, 2, v_v_2976_);
lean_ctor_set(v___x_2985_, 3, v___x_2982_);
lean_ctor_set(v___x_2985_, 4, v___x_2984_);
return v___x_2985_;
}
}
}
}
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2996_ = lean_unsigned_to_nat(2u);
v___x_2997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
lean_ctor_set(v___x_2997_, 1, v_k_2742_);
lean_ctor_set(v___x_2997_, 2, v_v_2743_);
lean_ctor_set(v___x_2997_, 3, v_impl_2898_);
lean_ctor_set(v___x_2997_, 4, v_r_2969_);
return v___x_2997_;
}
}
}
}
}
}
else
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = lean_unsigned_to_nat(1u);
v___x_3012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
lean_ctor_set(v___x_3012_, 1, v_k_2724_);
lean_ctor_set(v___x_3012_, 2, v_v_2725_);
lean_ctor_set(v___x_3012_, 3, v_t_2726_);
lean_ctor_set(v___x_3012_, 4, v_t_2726_);
return v___x_3012_;
}
v___jp_2727_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2738_ = lean_nat_add(v___y_2731_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec(v___y_2731_);
v___x_2739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
lean_ctor_set(v___x_2739_, 1, v___y_2736_);
lean_ctor_set(v___x_2739_, 2, v___y_2735_);
lean_ctor_set(v___x_2739_, 3, v___y_2732_);
lean_ctor_set(v___x_2739_, 4, v___y_2730_);
v___x_2740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2740_, 0, v___y_2728_);
lean_ctor_set(v___x_2740_, 1, v___y_2729_);
lean_ctor_set(v___x_2740_, 2, v___y_2734_);
lean_ctor_set(v___x_2740_, 3, v___y_2733_);
lean_ctor_set(v___x_2740_, 4, v___x_2739_);
return v___x_2740_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg(lean_object* v_k_3013_, lean_object* v_t_3014_){
_start:
{
if (lean_obj_tag(v_t_3014_) == 0)
{
lean_object* v_k_3015_; lean_object* v_l_3016_; lean_object* v_r_3017_; lean_object* v_fst_3018_; lean_object* v_snd_3019_; lean_object* v_fst_3020_; lean_object* v_snd_3021_; double v___x_3022_; double v___x_3023_; uint8_t v___x_3024_; 
v_k_3015_ = lean_ctor_get(v_t_3014_, 1);
v_l_3016_ = lean_ctor_get(v_t_3014_, 3);
v_r_3017_ = lean_ctor_get(v_t_3014_, 4);
v_fst_3018_ = lean_ctor_get(v_k_3013_, 0);
v_snd_3019_ = lean_ctor_get(v_k_3013_, 1);
v_fst_3020_ = lean_ctor_get(v_k_3015_, 0);
v_snd_3021_ = lean_ctor_get(v_k_3015_, 1);
v___x_3022_ = lean_unbox_float(v_fst_3018_);
v___x_3023_ = lean_unbox_float(v_fst_3020_);
v___x_3024_ = lean_float_decLt(v___x_3022_, v___x_3023_);
if (v___x_3024_ == 0)
{
double v___x_3025_; double v___x_3026_; uint8_t v___x_3027_; 
v___x_3025_ = lean_unbox_float(v_fst_3020_);
v___x_3026_ = lean_unbox_float(v_fst_3018_);
v___x_3027_ = lean_float_decLt(v___x_3025_, v___x_3026_);
if (v___x_3027_ == 0)
{
uint8_t v___x_3028_; 
v___x_3028_ = l_Lean_Name_cmp(v_snd_3019_, v_snd_3021_);
switch(v___x_3028_)
{
case 0:
{
v_t_3014_ = v_l_3016_;
goto _start;
}
case 1:
{
uint8_t v___x_3030_; 
v___x_3030_ = 1;
return v___x_3030_;
}
default: 
{
v_t_3014_ = v_r_3017_;
goto _start;
}
}
}
else
{
v_t_3014_ = v_r_3017_;
goto _start;
}
}
else
{
v_t_3014_ = v_l_3016_;
goto _start;
}
}
else
{
uint8_t v___x_3034_; 
v___x_3034_ = 0;
return v___x_3034_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg___boxed(lean_object* v_k_3035_, lean_object* v_t_3036_){
_start:
{
uint8_t v_res_3037_; lean_object* v_r_3038_; 
v_res_3037_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg(v_k_3035_, v_t_3036_);
lean_dec(v_t_3036_);
lean_dec_ref(v_k_3035_);
v_r_3038_ = lean_box(v_res_3037_);
return v_r_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg(double v_frequencyWeight_3039_, double v_fst_3040_, double v_depthFactor_3041_, lean_object* v_denyList_3042_, lean_object* v_as_3043_, size_t v_i_3044_, size_t v_stop_3045_, lean_object* v_b_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v_a_3050_; lean_object* v___y_3055_; lean_object* v___y_3056_; uint8_t v___x_3058_; 
v___x_3058_ = lean_usize_dec_eq(v_i_3044_, v_stop_3045_);
if (v___x_3058_ == 0)
{
lean_object* v_fst_3059_; lean_object* v_snd_3060_; lean_object* v___x_3061_; uint8_t v___y_3063_; uint8_t v___x_3091_; 
v_fst_3059_ = lean_ctor_get(v_b_3046_, 0);
v_snd_3060_ = lean_ctor_get(v_b_3046_, 1);
v___x_3061_ = lean_array_uget_borrowed(v_as_3043_, v_i_3044_);
v___x_3091_ = l_Lean_NameSet_contains(v_fst_3059_, v___x_3061_);
if (v___x_3091_ == 0)
{
uint8_t v___x_3092_; 
v___x_3092_ = l_Lean_NameSet_contains(v_denyList_3042_, v___x_3061_);
v___y_3063_ = v___x_3092_;
goto v___jp_3062_;
}
else
{
v___y_3063_ = v___x_3091_;
goto v___jp_3062_;
}
v___jp_3062_:
{
if (v___y_3063_ == 0)
{
lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3088_; 
lean_inc(v_snd_3060_);
lean_inc(v_fst_3059_);
v_isSharedCheck_3088_ = !lean_is_exclusive(v_b_3046_);
if (v_isSharedCheck_3088_ == 0)
{
lean_object* v_unused_3089_; lean_object* v_unused_3090_; 
v_unused_3089_ = lean_ctor_get(v_b_3046_, 1);
lean_dec(v_unused_3089_);
v_unused_3090_ = lean_ctor_get(v_b_3046_, 0);
lean_dec(v_unused_3090_);
v___x_3065_ = v_b_3046_;
v_isShared_3066_ = v_isSharedCheck_3088_;
goto v_resetjp_3064_;
}
else
{
lean_dec(v_b_3046_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3088_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3067_; 
v___x_3067_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg(v___x_3061_, v_frequencyWeight_3039_, v___y_3047_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v___x_3069_; double v___x_3070_; double v___x_3071_; double v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3075_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref(v___x_3067_);
lean_inc_n(v___x_3061_, 2);
v___x_3069_ = l_Lean_NameSet_insert(v_fst_3059_, v___x_3061_);
v___x_3070_ = lean_float_mul(v_fst_3040_, v_depthFactor_3041_);
v___x_3071_ = lean_unbox_float(v_a_3068_);
lean_dec(v_a_3068_);
v___x_3072_ = lean_float_mul(v___x_3070_, v___x_3071_);
v___x_3073_ = lean_box_float(v___x_3072_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 1, v___x_3061_);
lean_ctor_set(v___x_3065_, 0, v___x_3073_);
v___x_3075_ = v___x_3065_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3073_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v___x_3061_);
v___x_3075_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
uint8_t v___x_3076_; 
v___x_3076_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg(v___x_3075_, v_snd_3060_);
if (v___x_3076_ == 0)
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = lean_box(0);
v___x_3078_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(v___x_3075_, v___x_3077_, v_snd_3060_);
v___y_3055_ = v___x_3069_;
v___y_3056_ = v___x_3078_;
goto v___jp_3054_;
}
else
{
lean_dec_ref(v___x_3075_);
v___y_3055_ = v___x_3069_;
v___y_3056_ = v_snd_3060_;
goto v___jp_3054_;
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_del_object(v___x_3065_);
lean_dec(v_snd_3060_);
lean_dec(v_fst_3059_);
v_a_3080_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3067_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3067_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
else
{
v_a_3050_ = v_b_3046_;
goto v___jp_3049_;
}
}
}
else
{
lean_object* v___x_3093_; 
v___x_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3093_, 0, v_b_3046_);
return v___x_3093_;
}
v___jp_3049_:
{
size_t v___x_3051_; size_t v___x_3052_; 
v___x_3051_ = ((size_t)1ULL);
v___x_3052_ = lean_usize_add(v_i_3044_, v___x_3051_);
v_i_3044_ = v___x_3052_;
v_b_3046_ = v_a_3050_;
goto _start;
}
v___jp_3054_:
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___y_3055_);
lean_ctor_set(v___x_3057_, 1, v___y_3056_);
v_a_3050_ = v___x_3057_;
goto v___jp_3049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg___boxed(lean_object* v_frequencyWeight_3094_, lean_object* v_fst_3095_, lean_object* v_depthFactor_3096_, lean_object* v_denyList_3097_, lean_object* v_as_3098_, lean_object* v_i_3099_, lean_object* v_stop_3100_, lean_object* v_b_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
double v_frequencyWeight_boxed_3104_; double v_fst_11342__boxed_3105_; double v_depthFactor_boxed_3106_; size_t v_i_boxed_3107_; size_t v_stop_boxed_3108_; lean_object* v_res_3109_; 
v_frequencyWeight_boxed_3104_ = lean_unbox_float(v_frequencyWeight_3094_);
lean_dec_ref(v_frequencyWeight_3094_);
v_fst_11342__boxed_3105_ = lean_unbox_float(v_fst_3095_);
lean_dec_ref(v_fst_3095_);
v_depthFactor_boxed_3106_ = lean_unbox_float(v_depthFactor_3096_);
lean_dec_ref(v_depthFactor_3096_);
v_i_boxed_3107_ = lean_unbox_usize(v_i_3099_);
lean_dec(v_i_3099_);
v_stop_boxed_3108_ = lean_unbox_usize(v_stop_3100_);
lean_dec(v_stop_3100_);
v_res_3109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg(v_frequencyWeight_boxed_3104_, v_fst_11342__boxed_3105_, v_depthFactor_boxed_3106_, v_denyList_3097_, v_as_3098_, v_i_boxed_3107_, v_stop_boxed_3108_, v_b_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v_as_3098_);
lean_dec(v_denyList_3097_);
return v_res_3109_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10___closed__0(void){
_start:
{
lean_object* v___x_3110_; double v___x_3111_; 
v___x_3110_ = lean_unsigned_to_nat(0u);
v___x_3111_ = lean_float_of_nat(v___x_3110_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10(lean_object* v_cls_3115_, lean_object* v_msg_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
lean_object* v_ref_3122_; lean_object* v___x_3123_; lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3168_; 
v_ref_3122_ = lean_ctor_get(v___y_3119_, 5);
v___x_3123_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9_spec__10(v_msg_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3126_ = v___x_3123_;
v_isShared_3127_ = v_isSharedCheck_3168_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3123_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3168_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3128_; lean_object* v_traceState_3129_; lean_object* v_env_3130_; lean_object* v_nextMacroScope_3131_; lean_object* v_ngen_3132_; lean_object* v_auxDeclNGen_3133_; lean_object* v_cache_3134_; lean_object* v_messages_3135_; lean_object* v_infoState_3136_; lean_object* v_snapshotTasks_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3167_; 
v___x_3128_ = lean_st_ref_take(v___y_3120_);
v_traceState_3129_ = lean_ctor_get(v___x_3128_, 4);
v_env_3130_ = lean_ctor_get(v___x_3128_, 0);
v_nextMacroScope_3131_ = lean_ctor_get(v___x_3128_, 1);
v_ngen_3132_ = lean_ctor_get(v___x_3128_, 2);
v_auxDeclNGen_3133_ = lean_ctor_get(v___x_3128_, 3);
v_cache_3134_ = lean_ctor_get(v___x_3128_, 5);
v_messages_3135_ = lean_ctor_get(v___x_3128_, 6);
v_infoState_3136_ = lean_ctor_get(v___x_3128_, 7);
v_snapshotTasks_3137_ = lean_ctor_get(v___x_3128_, 8);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3139_ = v___x_3128_;
v_isShared_3140_ = v_isSharedCheck_3167_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_snapshotTasks_3137_);
lean_inc(v_infoState_3136_);
lean_inc(v_messages_3135_);
lean_inc(v_cache_3134_);
lean_inc(v_traceState_3129_);
lean_inc(v_auxDeclNGen_3133_);
lean_inc(v_ngen_3132_);
lean_inc(v_nextMacroScope_3131_);
lean_inc(v_env_3130_);
lean_dec(v___x_3128_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3167_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
uint64_t v_tid_3141_; lean_object* v_traces_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3166_; 
v_tid_3141_ = lean_ctor_get_uint64(v_traceState_3129_, sizeof(void*)*1);
v_traces_3142_ = lean_ctor_get(v_traceState_3129_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_traceState_3129_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3144_ = v_traceState_3129_;
v_isShared_3145_ = v_isSharedCheck_3166_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_traces_3142_);
lean_dec(v_traceState_3129_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3166_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; double v___x_3147_; uint8_t v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3156_; 
v___x_3146_ = lean_box(0);
v___x_3147_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10___closed__0, &l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10___closed__0);
v___x_3148_ = 0;
v___x_3149_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10___closed__1));
v___x_3150_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3150_, 0, v_cls_3115_);
lean_ctor_set(v___x_3150_, 1, v___x_3146_);
lean_ctor_set(v___x_3150_, 2, v___x_3149_);
lean_ctor_set_float(v___x_3150_, sizeof(void*)*3, v___x_3147_);
lean_ctor_set_float(v___x_3150_, sizeof(void*)*3 + 8, v___x_3147_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*3 + 16, v___x_3148_);
v___x_3151_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10___closed__2));
v___x_3152_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3150_);
lean_ctor_set(v___x_3152_, 1, v_a_3124_);
lean_ctor_set(v___x_3152_, 2, v___x_3151_);
lean_inc(v_ref_3122_);
v___x_3153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3153_, 0, v_ref_3122_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
v___x_3154_ = l_Lean_PersistentArray_push___redArg(v_traces_3142_, v___x_3153_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3154_);
v___x_3156_ = v___x_3144_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3154_);
lean_ctor_set_uint64(v_reuseFailAlloc_3165_, sizeof(void*)*1, v_tid_3141_);
v___x_3156_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
lean_object* v___x_3158_; 
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 4, v___x_3156_);
v___x_3158_ = v___x_3139_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_env_3130_);
lean_ctor_set(v_reuseFailAlloc_3164_, 1, v_nextMacroScope_3131_);
lean_ctor_set(v_reuseFailAlloc_3164_, 2, v_ngen_3132_);
lean_ctor_set(v_reuseFailAlloc_3164_, 3, v_auxDeclNGen_3133_);
lean_ctor_set(v_reuseFailAlloc_3164_, 4, v___x_3156_);
lean_ctor_set(v_reuseFailAlloc_3164_, 5, v_cache_3134_);
lean_ctor_set(v_reuseFailAlloc_3164_, 6, v_messages_3135_);
lean_ctor_set(v_reuseFailAlloc_3164_, 7, v_infoState_3136_);
lean_ctor_set(v_reuseFailAlloc_3164_, 8, v_snapshotTasks_3137_);
v___x_3158_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3162_; 
v___x_3159_ = lean_st_ref_set(v___y_3120_, v___x_3158_);
v___x_3160_ = lean_box(0);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 0, v___x_3160_);
v___x_3162_ = v___x_3126_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3160_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10___boxed(lean_object* v_cls_3169_, lean_object* v_msg_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10(v_cls_3169_, v_msg_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__8(lean_object* v_init_3177_, lean_object* v_x_3178_){
_start:
{
if (lean_obj_tag(v_x_3178_) == 0)
{
lean_object* v_k_3179_; lean_object* v_l_3180_; lean_object* v_r_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v_k_3179_ = lean_ctor_get(v_x_3178_, 1);
v_l_3180_ = lean_ctor_get(v_x_3178_, 3);
v_r_3181_ = lean_ctor_get(v_x_3178_, 4);
v___x_3182_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__8(v_init_3177_, v_r_3181_);
lean_inc(v_k_3179_);
v___x_3183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3183_, 0, v_k_3179_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v_init_3177_ = v___x_3183_;
v_x_3178_ = v_l_3180_;
goto _start;
}
else
{
return v_init_3177_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__8___boxed(lean_object* v_init_3185_, lean_object* v_x_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__8(v_init_3185_, v_x_3186_);
lean_dec(v_x_3186_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9(lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
if (lean_obj_tag(v_a_3188_) == 0)
{
lean_object* v___x_3190_; 
v___x_3190_ = l_List_reverse___redArg(v_a_3189_);
return v___x_3190_;
}
else
{
lean_object* v_head_3191_; lean_object* v_tail_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3219_; 
v_head_3191_ = lean_ctor_get(v_a_3188_, 0);
v_tail_3192_ = lean_ctor_get(v_a_3188_, 1);
v_isSharedCheck_3219_ = !lean_is_exclusive(v_a_3188_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3194_ = v_a_3188_;
v_isShared_3195_ = v_isSharedCheck_3219_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_tail_3192_);
lean_inc(v_head_3191_);
lean_dec(v_a_3188_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3219_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v_fst_3196_; lean_object* v_snd_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3218_; 
v_fst_3196_ = lean_ctor_get(v_head_3191_, 0);
v_snd_3197_ = lean_ctor_get(v_head_3191_, 1);
v_isSharedCheck_3218_ = !lean_is_exclusive(v_head_3191_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3199_ = v_head_3191_;
v_isShared_3200_ = v_isSharedCheck_3218_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_snd_3197_);
lean_inc(v_fst_3196_);
lean_dec(v_head_3191_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3218_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
double v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3207_; 
v___x_3201_ = lean_unbox_float(v_fst_3196_);
lean_dec(v_fst_3196_);
v___x_3202_ = lean_float_to_string(v___x_3201_);
v___x_3203_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
v___x_3204_ = l_Lean_MessageData_ofFormat(v___x_3203_);
v___x_3205_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__2, &l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__2);
if (v_isShared_3200_ == 0)
{
lean_ctor_set_tag(v___x_3199_, 7);
lean_ctor_set(v___x_3199_, 1, v___x_3205_);
lean_ctor_set(v___x_3199_, 0, v___x_3204_);
v___x_3207_ = v___x_3199_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3204_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v___x_3205_);
v___x_3207_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3208_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__3, &l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5___closed__3);
v___x_3209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3207_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = l_Lean_MessageData_ofName(v_snd_3197_);
v___x_3211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3209_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = l_Lean_MessageData_paren(v___x_3211_);
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 1, v_a_3189_);
lean_ctor_set(v___x_3194_, 0, v___x_3212_);
v___x_3214_ = v___x_3194_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3212_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v_a_3189_);
v___x_3214_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
v_a_3188_ = v_tail_3192_;
v_a_3189_ = v___x_3214_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__4(double v_fst_3220_, lean_object* v_x_3221_, lean_object* v_x_3222_){
_start:
{
if (lean_obj_tag(v_x_3222_) == 0)
{
return v_x_3221_;
}
else
{
lean_object* v_head_3223_; lean_object* v_tail_3224_; lean_object* v_fst_3225_; lean_object* v_snd_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3241_; 
v_head_3223_ = lean_ctor_get(v_x_3222_, 0);
lean_inc(v_head_3223_);
v_tail_3224_ = lean_ctor_get(v_x_3222_, 1);
lean_inc(v_tail_3224_);
lean_dec_ref(v_x_3222_);
v_fst_3225_ = lean_ctor_get(v_head_3223_, 0);
v_snd_3226_ = lean_ctor_get(v_head_3223_, 1);
v_isSharedCheck_3241_ = !lean_is_exclusive(v_head_3223_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3228_ = v_head_3223_;
v_isShared_3229_ = v_isSharedCheck_3241_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_snd_3226_);
lean_inc(v_fst_3225_);
lean_dec(v_head_3223_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3241_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
double v___x_3230_; double v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3234_; 
v___x_3230_ = lean_unbox_float(v_snd_3226_);
lean_dec(v_snd_3226_);
v___x_3231_ = lean_float_mul(v___x_3230_, v_fst_3220_);
v___x_3232_ = lean_box_float(v___x_3231_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 1, v_fst_3225_);
lean_ctor_set(v___x_3228_, 0, v___x_3232_);
v___x_3234_ = v___x_3228_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v_fst_3225_);
v___x_3234_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
uint8_t v___x_3235_; 
v___x_3235_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg(v___x_3234_, v_x_3221_);
if (v___x_3235_ == 0)
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3236_ = lean_box(0);
v___x_3237_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(v___x_3234_, v___x_3236_, v_x_3221_);
v_x_3221_ = v___x_3237_;
v_x_3222_ = v_tail_3224_;
goto _start;
}
else
{
lean_dec_ref(v___x_3234_);
v_x_3222_ = v_tail_3224_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__4___boxed(lean_object* v_fst_3242_, lean_object* v_x_3243_, lean_object* v_x_3244_){
_start:
{
double v_fst_11633__boxed_3245_; lean_object* v_res_3246_; 
v_fst_11633__boxed_3245_ = lean_unbox_float(v_fst_3242_);
lean_dec_ref(v_fst_3242_);
v_res_3246_ = l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__4(v_fst_11633__boxed_3245_, v_x_3243_, v_x_3244_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6(lean_object* v_init_3247_, lean_object* v_x_3248_){
_start:
{
if (lean_obj_tag(v_x_3248_) == 0)
{
lean_object* v_k_3249_; lean_object* v_l_3250_; lean_object* v_r_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v_k_3249_ = lean_ctor_get(v_x_3248_, 1);
v_l_3250_ = lean_ctor_get(v_x_3248_, 3);
v_r_3251_ = lean_ctor_get(v_x_3248_, 4);
v___x_3252_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6(v_init_3247_, v_r_3251_);
lean_inc(v_k_3249_);
v___x_3253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3253_, 0, v_k_3249_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v_init_3247_ = v___x_3253_;
v_x_3248_ = v_l_3250_;
goto _start;
}
else
{
return v_init_3247_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6___boxed(lean_object* v_init_3255_, lean_object* v_x_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6(v_init_3255_, v_x_3256_);
lean_dec(v_x_3256_);
return v_res_3257_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__2(void){
_start:
{
lean_object* v_cls_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v_cls_3261_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_));
v___x_3262_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__1));
v___x_3263_ = l_Lean_Name_append(v___x_3262_, v_cls_3261_);
return v___x_3263_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__4(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3265_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__3));
v___x_3266_ = l_Lean_stringToMessageData(v___x_3265_);
return v___x_3266_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__6(void){
_start:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3268_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__5));
v___x_3269_ = l_Lean_stringToMessageData(v___x_3268_);
return v___x_3269_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__8(void){
_start:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3271_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__7));
v___x_3272_ = l_Lean_stringToMessageData(v___x_3271_);
return v___x_3272_;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__10(void){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__9));
v___x_3275_ = l_Lean_stringToMessageData(v___x_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go(lean_object* v_maxSuggestions_3276_, double v_depthFactor_3277_, double v_frequencyWeight_3278_, lean_object* v_denyList_3279_, lean_object* v_pastTriggers_3280_, lean_object* v_triggerQueue_3281_, lean_object* v_acceptedTheorems_3282_, lean_object* v_queuedTheorems_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v___y_3290_; lean_object* v___y_3291_; double v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v_fst_3297_; lean_object* v_snd_3298_; lean_object* v___y_3305_; lean_object* v___y_3306_; double v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3372_ = lean_array_get_size(v_acceptedTheorems_3282_);
v___x_3373_ = lean_nat_dec_le(v_maxSuggestions_3276_, v___x_3372_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; 
v___x_3374_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_triggerQueue_3281_);
if (lean_obj_tag(v___x_3374_) == 0)
{
v___y_3325_ = v_a_3284_;
v___y_3326_ = v_a_3285_;
v___y_3327_ = v_a_3286_;
v___y_3328_ = v_a_3287_;
goto v___jp_3324_;
}
else
{
lean_object* v_val_3375_; lean_object* v_fst_3376_; lean_object* v_snd_3377_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___x_3437_; 
v_val_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_val_3375_);
lean_dec_ref(v___x_3374_);
v_fst_3376_ = lean_ctor_get(v_val_3375_, 0);
lean_inc(v_fst_3376_);
v_snd_3377_ = lean_ctor_get(v_val_3375_, 1);
v___x_3437_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queuedTheorems_3283_);
if (lean_obj_tag(v___x_3437_) == 0)
{
goto v___jp_3397_;
}
else
{
lean_object* v_val_3438_; lean_object* v_fst_3439_; double v___x_3440_; double v___x_3441_; uint8_t v___x_3442_; 
v_val_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_val_3438_);
lean_dec_ref(v___x_3437_);
v_fst_3439_ = lean_ctor_get(v_val_3438_, 0);
lean_inc(v_fst_3439_);
lean_dec(v_val_3438_);
v___x_3440_ = lean_unbox_float(v_fst_3376_);
v___x_3441_ = lean_unbox_float(v_fst_3439_);
lean_dec(v_fst_3439_);
v___x_3442_ = lean_float_decLt(v___x_3440_, v___x_3441_);
if (v___x_3442_ == 0)
{
lean_dec(v_fst_3376_);
lean_dec(v_val_3375_);
v___y_3325_ = v_a_3284_;
v___y_3326_ = v_a_3285_;
v___y_3327_ = v_a_3286_;
v___y_3328_ = v_a_3287_;
goto v___jp_3324_;
}
else
{
goto v___jp_3397_;
}
}
v___jp_3378_:
{
lean_object* v___x_3383_; 
v___x_3383_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNonTheorems___redArg(v_snd_3377_, v___y_3382_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; lean_object* v___x_3385_; double v___x_3386_; lean_object* v___x_3387_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_a_3384_);
lean_dec_ref(v___x_3383_);
v___x_3385_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v_val_3375_, v_triggerQueue_3281_);
lean_dec(v_val_3375_);
v___x_3386_ = lean_unbox_float(v_fst_3376_);
lean_dec(v_fst_3376_);
v___x_3387_ = l_List_foldl___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__4(v___x_3386_, v_queuedTheorems_3283_, v_a_3384_);
v_triggerQueue_3281_ = v___x_3385_;
v_queuedTheorems_3283_ = v___x_3387_;
v_a_3284_ = v___y_3379_;
v_a_3285_ = v___y_3380_;
v_a_3286_ = v___y_3381_;
v_a_3287_ = v___y_3382_;
goto _start;
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec(v_fst_3376_);
lean_dec(v_val_3375_);
lean_dec(v_queuedTheorems_3283_);
lean_dec_ref(v_acceptedTheorems_3282_);
lean_dec(v_triggerQueue_3281_);
lean_dec(v_pastTriggers_3280_);
v_a_3389_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3383_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3383_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
v___jp_3397_:
{
lean_object* v_options_3398_; uint8_t v_hasTrace_3399_; 
v_options_3398_ = lean_ctor_get(v_a_3286_, 2);
v_hasTrace_3399_ = lean_ctor_get_uint8(v_options_3398_, sizeof(void*)*1);
if (v_hasTrace_3399_ == 0)
{
v___y_3379_ = v_a_3284_;
v___y_3380_ = v_a_3285_;
v___y_3381_ = v_a_3286_;
v___y_3382_ = v_a_3287_;
goto v___jp_3378_;
}
else
{
lean_object* v_inheritedTraceOptions_3400_; lean_object* v_cls_3401_; lean_object* v___x_3402_; uint8_t v___x_3403_; 
v_inheritedTraceOptions_3400_ = lean_ctor_get(v_a_3286_, 13);
v_cls_3401_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_initFn___closed__1_00___x40_Lean_LibrarySuggestions_SineQuaNon_4180265299____hygCtx___hyg_2_));
v___x_3402_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__2, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__2_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__2);
v___x_3403_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3400_, v_options_3398_, v___x_3402_);
if (v___x_3403_ == 0)
{
v___y_3379_ = v_a_3284_;
v___y_3380_ = v_a_3285_;
v___y_3381_ = v_a_3286_;
v___y_3382_ = v_a_3287_;
goto v___jp_3378_;
}
else
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3404_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__4, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__4_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__4);
lean_inc_ref(v_acceptedTheorems_3282_);
v___x_3405_ = lean_array_to_list(v_acceptedTheorems_3282_);
v___x_3406_ = lean_box(0);
v___x_3407_ = l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__5(v___x_3405_, v___x_3406_);
v___x_3408_ = l_Lean_MessageData_ofList(v___x_3407_);
v___x_3409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3404_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___x_3410_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__6, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__6_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__6);
v___x_3411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3409_);
lean_ctor_set(v___x_3411_, 1, v___x_3410_);
v___x_3412_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6(v___x_3406_, v_pastTriggers_3280_);
v___x_3413_ = l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__7(v___x_3412_, v___x_3406_);
v___x_3414_ = l_Lean_MessageData_ofList(v___x_3413_);
v___x_3415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3411_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
v___x_3416_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__8, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__8_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__8);
v___x_3417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3415_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
v___x_3418_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__8(v___x_3406_, v_triggerQueue_3281_);
v___x_3419_ = l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9(v___x_3418_, v___x_3406_);
v___x_3420_ = l_Lean_MessageData_ofList(v___x_3419_);
v___x_3421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3417_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = lean_obj_once(&l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__10, &l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__10_once, _init_l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___closed__10);
v___x_3423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3421_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
v___x_3424_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__8(v___x_3406_, v_queuedTheorems_3283_);
v___x_3425_ = l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__9(v___x_3424_, v___x_3406_);
v___x_3426_ = l_Lean_MessageData_ofList(v___x_3425_);
v___x_3427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3423_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__10(v_cls_3401_, v___x_3427_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_dec_ref(v___x_3428_);
v___y_3379_ = v_a_3284_;
v___y_3380_ = v_a_3285_;
v___y_3381_ = v_a_3286_;
v___y_3382_ = v_a_3287_;
goto v___jp_3378_;
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_dec(v_fst_3376_);
lean_dec(v_val_3375_);
lean_dec(v_queuedTheorems_3283_);
lean_dec_ref(v_acceptedTheorems_3282_);
lean_dec(v_triggerQueue_3281_);
lean_dec(v_pastTriggers_3280_);
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3428_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3428_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
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
lean_object* v___x_3443_; 
lean_dec(v_queuedTheorems_3283_);
lean_dec(v_triggerQueue_3281_);
lean_dec(v_pastTriggers_3280_);
v___x_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3443_, 0, v_acceptedTheorems_3282_);
return v___x_3443_;
}
v___jp_3289_:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3299_ = lean_box_float(v___y_3292_);
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___y_3296_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = lean_array_push(v_acceptedTheorems_3282_, v___x_3300_);
v___x_3302_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v___y_3290_, v_queuedTheorems_3283_);
lean_dec_ref(v___y_3290_);
v_pastTriggers_3280_ = v_fst_3297_;
v_triggerQueue_3281_ = v_snd_3298_;
v_acceptedTheorems_3282_ = v___x_3301_;
v_queuedTheorems_3283_ = v___x_3302_;
v_a_3284_ = v___y_3294_;
v_a_3285_ = v___y_3293_;
v_a_3286_ = v___y_3291_;
v_a_3287_ = v___y_3295_;
goto _start;
}
v___jp_3304_:
{
if (lean_obj_tag(v___y_3312_) == 0)
{
lean_object* v_a_3313_; lean_object* v_fst_3314_; lean_object* v_snd_3315_; 
v_a_3313_ = lean_ctor_get(v___y_3312_, 0);
lean_inc(v_a_3313_);
lean_dec_ref(v___y_3312_);
v_fst_3314_ = lean_ctor_get(v_a_3313_, 0);
lean_inc(v_fst_3314_);
v_snd_3315_ = lean_ctor_get(v_a_3313_, 1);
lean_inc(v_snd_3315_);
lean_dec(v_a_3313_);
v___y_3290_ = v___y_3305_;
v___y_3291_ = v___y_3306_;
v___y_3292_ = v___y_3307_;
v___y_3293_ = v___y_3308_;
v___y_3294_ = v___y_3309_;
v___y_3295_ = v___y_3311_;
v___y_3296_ = v___y_3310_;
v_fst_3297_ = v_fst_3314_;
v_snd_3298_ = v_snd_3315_;
goto v___jp_3289_;
}
else
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3323_; 
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3305_);
lean_dec(v_queuedTheorems_3283_);
lean_dec_ref(v_acceptedTheorems_3282_);
v_a_3316_ = lean_ctor_get(v___y_3312_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___y_3312_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3318_ = v___y_3312_;
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___y_3312_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3316_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
v___jp_3324_:
{
lean_object* v___x_3329_; 
v___x_3329_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queuedTheorems_3283_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v___x_3330_; 
lean_dec(v_queuedTheorems_3283_);
lean_dec(v_triggerQueue_3281_);
lean_dec(v_pastTriggers_3280_);
v___x_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3330_, 0, v_acceptedTheorems_3282_);
return v___x_3330_;
}
else
{
lean_object* v_val_3331_; lean_object* v_fst_3332_; lean_object* v_snd_3333_; lean_object* v___x_3334_; 
v_val_3331_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_val_3331_);
lean_dec_ref(v___x_3329_);
v_fst_3332_ = lean_ctor_get(v_val_3331_, 0);
v_snd_3333_ = lean_ctor_get(v_val_3331_, 1);
lean_inc_n(v_snd_3333_, 2);
v___x_3334_ = l_Lean_getConstInfo___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_prepareTriggers_spec__0(v_snd_3333_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref(v___x_3334_);
v___x_3336_ = l_Lean_ConstantInfo_type(v_a_3335_);
lean_dec(v_a_3335_);
v___x_3337_ = l_Lean_Expr_relevantConstants(v___x_3336_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; uint8_t v___x_3341_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref(v___x_3337_);
v___x_3339_ = lean_unsigned_to_nat(0u);
v___x_3340_ = lean_array_get_size(v_a_3338_);
v___x_3341_ = lean_nat_dec_lt(v___x_3339_, v___x_3340_);
if (v___x_3341_ == 0)
{
double v___x_3342_; 
lean_dec(v_a_3338_);
v___x_3342_ = lean_unbox_float(v_fst_3332_);
v___y_3290_ = v_val_3331_;
v___y_3291_ = v___y_3327_;
v___y_3292_ = v___x_3342_;
v___y_3293_ = v___y_3326_;
v___y_3294_ = v___y_3325_;
v___y_3295_ = v___y_3328_;
v___y_3296_ = v_snd_3333_;
v_fst_3297_ = v_pastTriggers_3280_;
v_snd_3298_ = v_triggerQueue_3281_;
goto v___jp_3289_;
}
else
{
lean_object* v___x_3343_; uint8_t v___x_3344_; 
lean_inc(v_triggerQueue_3281_);
lean_inc(v_pastTriggers_3280_);
v___x_3343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3343_, 0, v_pastTriggers_3280_);
lean_ctor_set(v___x_3343_, 1, v_triggerQueue_3281_);
v___x_3344_ = lean_nat_dec_le(v___x_3340_, v___x_3340_);
if (v___x_3344_ == 0)
{
if (v___x_3341_ == 0)
{
double v___x_3345_; 
lean_dec_ref(v___x_3343_);
lean_dec(v_a_3338_);
v___x_3345_ = lean_unbox_float(v_fst_3332_);
v___y_3290_ = v_val_3331_;
v___y_3291_ = v___y_3327_;
v___y_3292_ = v___x_3345_;
v___y_3293_ = v___y_3326_;
v___y_3294_ = v___y_3325_;
v___y_3295_ = v___y_3328_;
v___y_3296_ = v_snd_3333_;
v_fst_3297_ = v_pastTriggers_3280_;
v_snd_3298_ = v_triggerQueue_3281_;
goto v___jp_3289_;
}
else
{
size_t v___x_3346_; size_t v___x_3347_; double v___x_3348_; lean_object* v___x_3349_; double v___x_3350_; 
lean_dec(v_triggerQueue_3281_);
lean_dec(v_pastTriggers_3280_);
v___x_3346_ = ((size_t)0ULL);
v___x_3347_ = lean_usize_of_nat(v___x_3340_);
v___x_3348_ = lean_unbox_float(v_fst_3332_);
v___x_3349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg(v_frequencyWeight_3278_, v___x_3348_, v_depthFactor_3277_, v_denyList_3279_, v_a_3338_, v___x_3346_, v___x_3347_, v___x_3343_, v___y_3328_);
lean_dec(v_a_3338_);
v___x_3350_ = lean_unbox_float(v_fst_3332_);
v___y_3305_ = v_val_3331_;
v___y_3306_ = v___y_3327_;
v___y_3307_ = v___x_3350_;
v___y_3308_ = v___y_3326_;
v___y_3309_ = v___y_3325_;
v___y_3310_ = v_snd_3333_;
v___y_3311_ = v___y_3328_;
v___y_3312_ = v___x_3349_;
goto v___jp_3304_;
}
}
else
{
size_t v___x_3351_; size_t v___x_3352_; double v___x_3353_; lean_object* v___x_3354_; double v___x_3355_; 
lean_dec(v_triggerQueue_3281_);
lean_dec(v_pastTriggers_3280_);
v___x_3351_ = ((size_t)0ULL);
v___x_3352_ = lean_usize_of_nat(v___x_3340_);
v___x_3353_ = lean_unbox_float(v_fst_3332_);
v___x_3354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg(v_frequencyWeight_3278_, v___x_3353_, v_depthFactor_3277_, v_denyList_3279_, v_a_3338_, v___x_3351_, v___x_3352_, v___x_3343_, v___y_3328_);
lean_dec(v_a_3338_);
v___x_3355_ = lean_unbox_float(v_fst_3332_);
v___y_3305_ = v_val_3331_;
v___y_3306_ = v___y_3327_;
v___y_3307_ = v___x_3355_;
v___y_3308_ = v___y_3326_;
v___y_3309_ = v___y_3325_;
v___y_3310_ = v_snd_3333_;
v___y_3311_ = v___y_3328_;
v___y_3312_ = v___x_3354_;
goto v___jp_3304_;
}
}
}
else
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3363_; 
lean_dec(v_snd_3333_);
lean_dec(v_val_3331_);
lean_dec(v_queuedTheorems_3283_);
lean_dec_ref(v_acceptedTheorems_3282_);
lean_dec(v_triggerQueue_3281_);
lean_dec(v_pastTriggers_3280_);
v_a_3356_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3358_ = v___x_3337_;
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3337_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
else
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3371_; 
lean_dec(v_snd_3333_);
lean_dec(v_val_3331_);
lean_dec(v_queuedTheorems_3283_);
lean_dec_ref(v_acceptedTheorems_3282_);
lean_dec(v_triggerQueue_3281_);
lean_dec(v_pastTriggers_3280_);
v_a_3364_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3366_ = v___x_3334_;
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3334_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go___boxed(lean_object* v_maxSuggestions_3444_, lean_object* v_depthFactor_3445_, lean_object* v_frequencyWeight_3446_, lean_object* v_denyList_3447_, lean_object* v_pastTriggers_3448_, lean_object* v_triggerQueue_3449_, lean_object* v_acceptedTheorems_3450_, lean_object* v_queuedTheorems_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_){
_start:
{
double v_depthFactor_boxed_3457_; double v_frequencyWeight_boxed_3458_; lean_object* v_res_3459_; 
v_depthFactor_boxed_3457_ = lean_unbox_float(v_depthFactor_3445_);
lean_dec_ref(v_depthFactor_3445_);
v_frequencyWeight_boxed_3458_ = lean_unbox_float(v_frequencyWeight_3446_);
lean_dec_ref(v_frequencyWeight_3446_);
v_res_3459_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go(v_maxSuggestions_3444_, v_depthFactor_boxed_3457_, v_frequencyWeight_boxed_3458_, v_denyList_3447_, v_pastTriggers_3448_, v_triggerQueue_3449_, v_acceptedTheorems_3450_, v_queuedTheorems_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_);
lean_dec(v_a_3455_);
lean_dec_ref(v_a_3454_);
lean_dec(v_a_3453_);
lean_dec_ref(v_a_3452_);
lean_dec(v_denyList_3447_);
lean_dec(v_maxSuggestions_3444_);
return v_res_3459_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0(lean_object* v_00_u03b2_3460_, lean_object* v_k_3461_, lean_object* v_t_3462_){
_start:
{
uint8_t v___x_3463_; 
v___x_3463_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___redArg(v_k_3461_, v_t_3462_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0___boxed(lean_object* v_00_u03b2_3464_, lean_object* v_k_3465_, lean_object* v_t_3466_){
_start:
{
uint8_t v_res_3467_; lean_object* v_r_3468_; 
v_res_3467_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__0(v_00_u03b2_3464_, v_k_3465_, v_t_3466_);
lean_dec(v_t_3466_);
lean_dec_ref(v_k_3465_);
v_r_3468_ = lean_box(v_res_3467_);
return v_r_3468_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1(lean_object* v_00_u03b2_3469_, lean_object* v_k_3470_, lean_object* v_v_3471_, lean_object* v_t_3472_, lean_object* v_hl_3473_){
_start:
{
lean_object* v___x_3474_; 
v___x_3474_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__1___redArg(v_k_3470_, v_v_3471_, v_t_3472_);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2(lean_object* v_00_u03b2_3475_, lean_object* v_k_3476_, lean_object* v_t_3477_, lean_object* v_h_3478_){
_start:
{
lean_object* v___x_3479_; 
v___x_3479_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___redArg(v_k_3476_, v_t_3477_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2___boxed(lean_object* v_00_u03b2_3480_, lean_object* v_k_3481_, lean_object* v_t_3482_, lean_object* v_h_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__2(v_00_u03b2_3480_, v_k_3481_, v_t_3482_, v_h_3483_);
lean_dec_ref(v_k_3481_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3(double v_frequencyWeight_3485_, double v_fst_3486_, double v_depthFactor_3487_, lean_object* v_denyList_3488_, lean_object* v_as_3489_, size_t v_i_3490_, size_t v_stop_3491_, lean_object* v_b_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___redArg(v_frequencyWeight_3485_, v_fst_3486_, v_depthFactor_3487_, v_denyList_3488_, v_as_3489_, v_i_3490_, v_stop_3491_, v_b_3492_, v___y_3496_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3___boxed(lean_object* v_frequencyWeight_3499_, lean_object* v_fst_3500_, lean_object* v_depthFactor_3501_, lean_object* v_denyList_3502_, lean_object* v_as_3503_, lean_object* v_i_3504_, lean_object* v_stop_3505_, lean_object* v_b_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
double v_frequencyWeight_boxed_3512_; double v_fst_12066__boxed_3513_; double v_depthFactor_boxed_3514_; size_t v_i_boxed_3515_; size_t v_stop_boxed_3516_; lean_object* v_res_3517_; 
v_frequencyWeight_boxed_3512_ = lean_unbox_float(v_frequencyWeight_3499_);
lean_dec_ref(v_frequencyWeight_3499_);
v_fst_12066__boxed_3513_ = lean_unbox_float(v_fst_3500_);
lean_dec_ref(v_fst_3500_);
v_depthFactor_boxed_3514_ = lean_unbox_float(v_depthFactor_3501_);
lean_dec_ref(v_depthFactor_3501_);
v_i_boxed_3515_ = lean_unbox_usize(v_i_3504_);
lean_dec(v_i_3504_);
v_stop_boxed_3516_ = lean_unbox_usize(v_stop_3505_);
lean_dec(v_stop_3505_);
v_res_3517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__3(v_frequencyWeight_boxed_3512_, v_fst_12066__boxed_3513_, v_depthFactor_boxed_3514_, v_denyList_3502_, v_as_3503_, v_i_boxed_3515_, v_stop_boxed_3516_, v_b_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec_ref(v_as_3503_);
lean_dec(v_denyList_3502_);
return v_res_3517_;
}
}
static double _init_l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3518_; uint8_t v___x_3519_; lean_object* v___x_3520_; double v___x_3521_; 
v___x_3518_ = lean_unsigned_to_nat(2u);
v___x_3519_ = 1;
v___x_3520_ = lean_unsigned_to_nat(1u);
v___x_3521_ = l_Float_ofScientific(v___x_3520_, v___x_3519_, v___x_3518_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg(lean_object* v_x_3522_, lean_object* v_x_3523_, lean_object* v___y_3524_){
_start:
{
if (lean_obj_tag(v_x_3522_) == 0)
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = l_List_reverse___redArg(v_x_3523_);
v___x_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
return v___x_3527_;
}
else
{
lean_object* v_head_3528_; lean_object* v_tail_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3549_; 
v_head_3528_ = lean_ctor_get(v_x_3522_, 0);
v_tail_3529_ = lean_ctor_get(v_x_3522_, 1);
v_isSharedCheck_3549_ = !lean_is_exclusive(v_x_3522_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3531_ = v_x_3522_;
v_isShared_3532_ = v_isSharedCheck_3549_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_tail_3529_);
lean_inc(v_head_3528_);
lean_dec(v_x_3522_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3549_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
double v___x_3533_; lean_object* v___x_3534_; 
v___x_3533_ = lean_float_once(&l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0, &l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0_once, _init_l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0);
v___x_3534_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_frequencyScore___redArg(v_head_3528_, v___x_3533_, v___y_3524_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3536_; lean_object* v___x_3538_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref(v___x_3534_);
v___x_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3536_, 0, v_a_3535_);
lean_ctor_set(v___x_3536_, 1, v_head_3528_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 1, v_x_3523_);
lean_ctor_set(v___x_3531_, 0, v___x_3536_);
v___x_3538_ = v___x_3531_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3536_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v_x_3523_);
v___x_3538_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
v_x_3522_ = v_tail_3529_;
v_x_3523_ = v___x_3538_;
goto _start;
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
lean_del_object(v___x_3531_);
lean_dec(v_tail_3529_);
lean_dec(v_head_3528_);
lean_dec(v_x_3523_);
v_a_3541_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3534_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3534_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___boxed(lean_object* v_x_3550_, lean_object* v_x_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg(v_x_3550_, v_x_3551_, v___y_3552_);
lean_dec(v___y_3552_);
return v_res_3554_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3555_; double v___x_3556_; 
v___x_3555_ = lean_unsigned_to_nat(1u);
v___x_3556_ = lean_float_of_nat(v___x_3555_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3(size_t v_sz_3557_, size_t v_i_3558_, lean_object* v_bs_3559_){
_start:
{
uint8_t v___x_3560_; 
v___x_3560_ = lean_usize_dec_lt(v_i_3558_, v_sz_3557_);
if (v___x_3560_ == 0)
{
return v_bs_3559_;
}
else
{
lean_object* v_v_3561_; lean_object* v_fst_3562_; lean_object* v_snd_3563_; lean_object* v___x_3564_; lean_object* v_bs_x27_3565_; double v___x_3566_; double v___x_3567_; double v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; size_t v___x_3571_; size_t v___x_3572_; lean_object* v___x_3573_; 
v_v_3561_ = lean_array_uget_borrowed(v_bs_3559_, v_i_3558_);
v_fst_3562_ = lean_ctor_get(v_v_3561_, 0);
lean_inc(v_fst_3562_);
v_snd_3563_ = lean_ctor_get(v_v_3561_, 1);
lean_inc(v_snd_3563_);
v___x_3564_ = lean_unsigned_to_nat(0u);
v_bs_x27_3565_ = lean_array_uset(v_bs_3559_, v_i_3558_, v___x_3564_);
v___x_3566_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___closed__0);
v___x_3567_ = lean_unbox_float(v_snd_3563_);
lean_dec(v_snd_3563_);
v___x_3568_ = lean_float_div(v___x_3566_, v___x_3567_);
v___x_3569_ = lean_box(0);
v___x_3570_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3570_, 0, v_fst_3562_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
lean_ctor_set_float(v___x_3570_, sizeof(void*)*2, v___x_3568_);
v___x_3571_ = ((size_t)1ULL);
v___x_3572_ = lean_usize_add(v_i_3558_, v___x_3571_);
v___x_3573_ = lean_array_uset(v_bs_x27_3565_, v_i_3558_, v___x_3570_);
v_i_3558_ = v___x_3572_;
v_bs_3559_ = v___x_3573_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3___boxed(lean_object* v_sz_3575_, lean_object* v_i_3576_, lean_object* v_bs_3577_){
_start:
{
size_t v_sz_boxed_3578_; size_t v_i_boxed_3579_; lean_object* v_res_3580_; 
v_sz_boxed_3578_ = lean_unbox_usize(v_sz_3575_);
lean_dec(v_sz_3575_);
v_i_boxed_3579_ = lean_unbox_usize(v_i_3576_);
lean_dec(v_i_3576_);
v_res_3580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3(v_sz_boxed_3578_, v_i_boxed_3579_, v_bs_3577_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(lean_object* v_k_3581_, lean_object* v_t_3582_){
_start:
{
if (lean_obj_tag(v_t_3582_) == 0)
{
lean_object* v_k_3583_; lean_object* v_v_3584_; lean_object* v_l_3585_; lean_object* v_r_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_4240_; 
v_k_3583_ = lean_ctor_get(v_t_3582_, 1);
v_v_3584_ = lean_ctor_get(v_t_3582_, 2);
v_l_3585_ = lean_ctor_get(v_t_3582_, 3);
v_r_3586_ = lean_ctor_get(v_t_3582_, 4);
v_isSharedCheck_4240_ = !lean_is_exclusive(v_t_3582_);
if (v_isSharedCheck_4240_ == 0)
{
lean_object* v_unused_4241_; 
v_unused_4241_ = lean_ctor_get(v_t_3582_, 0);
lean_dec(v_unused_4241_);
v___x_3588_ = v_t_3582_;
v_isShared_3589_ = v_isSharedCheck_4240_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_r_3586_);
lean_inc(v_l_3585_);
lean_inc(v_v_3584_);
lean_inc(v_k_3583_);
lean_dec(v_t_3582_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_4240_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
uint8_t v___x_3590_; 
v___x_3590_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3581_, v_k_3583_);
switch(v___x_3590_)
{
case 0:
{
lean_object* v_impl_3591_; lean_object* v___x_3592_; 
v_impl_3591_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(v_k_3581_, v_l_3585_);
v___x_3592_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3591_) == 0)
{
if (lean_obj_tag(v_r_3586_) == 0)
{
lean_object* v_size_3593_; lean_object* v_size_3594_; lean_object* v_k_3595_; lean_object* v_v_3596_; lean_object* v_l_3597_; lean_object* v_r_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v_size_3593_ = lean_ctor_get(v_impl_3591_, 0);
lean_inc(v_size_3593_);
v_size_3594_ = lean_ctor_get(v_r_3586_, 0);
v_k_3595_ = lean_ctor_get(v_r_3586_, 1);
v_v_3596_ = lean_ctor_get(v_r_3586_, 2);
v_l_3597_ = lean_ctor_get(v_r_3586_, 3);
lean_inc(v_l_3597_);
v_r_3598_ = lean_ctor_get(v_r_3586_, 4);
v___x_3599_ = lean_unsigned_to_nat(3u);
v___x_3600_ = lean_nat_mul(v___x_3599_, v_size_3593_);
v___x_3601_ = lean_nat_dec_lt(v___x_3600_, v_size_3594_);
lean_dec(v___x_3600_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
lean_dec(v_l_3597_);
v___x_3602_ = lean_nat_add(v___x_3592_, v_size_3593_);
lean_dec(v_size_3593_);
v___x_3603_ = lean_nat_add(v___x_3602_, v_size_3594_);
lean_dec(v___x_3602_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 3, v_impl_3591_);
lean_ctor_set(v___x_3588_, 0, v___x_3603_);
v___x_3605_ = v___x_3588_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3603_);
lean_ctor_set(v_reuseFailAlloc_3606_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_3606_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_3606_, 3, v_impl_3591_);
lean_ctor_set(v_reuseFailAlloc_3606_, 4, v_r_3586_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
else
{
lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3670_; 
lean_inc(v_r_3598_);
lean_inc(v_v_3596_);
lean_inc(v_k_3595_);
lean_inc(v_size_3594_);
v_isSharedCheck_3670_ = !lean_is_exclusive(v_r_3586_);
if (v_isSharedCheck_3670_ == 0)
{
lean_object* v_unused_3671_; lean_object* v_unused_3672_; lean_object* v_unused_3673_; lean_object* v_unused_3674_; lean_object* v_unused_3675_; 
v_unused_3671_ = lean_ctor_get(v_r_3586_, 4);
lean_dec(v_unused_3671_);
v_unused_3672_ = lean_ctor_get(v_r_3586_, 3);
lean_dec(v_unused_3672_);
v_unused_3673_ = lean_ctor_get(v_r_3586_, 2);
lean_dec(v_unused_3673_);
v_unused_3674_ = lean_ctor_get(v_r_3586_, 1);
lean_dec(v_unused_3674_);
v_unused_3675_ = lean_ctor_get(v_r_3586_, 0);
lean_dec(v_unused_3675_);
v___x_3608_ = v_r_3586_;
v_isShared_3609_ = v_isSharedCheck_3670_;
goto v_resetjp_3607_;
}
else
{
lean_dec(v_r_3586_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3670_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v_size_3610_; lean_object* v_k_3611_; lean_object* v_v_3612_; lean_object* v_l_3613_; lean_object* v_r_3614_; lean_object* v_size_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; uint8_t v___x_3618_; 
v_size_3610_ = lean_ctor_get(v_l_3597_, 0);
v_k_3611_ = lean_ctor_get(v_l_3597_, 1);
v_v_3612_ = lean_ctor_get(v_l_3597_, 2);
v_l_3613_ = lean_ctor_get(v_l_3597_, 3);
v_r_3614_ = lean_ctor_get(v_l_3597_, 4);
v_size_3615_ = lean_ctor_get(v_r_3598_, 0);
v___x_3616_ = lean_unsigned_to_nat(2u);
v___x_3617_ = lean_nat_mul(v___x_3616_, v_size_3615_);
v___x_3618_ = lean_nat_dec_lt(v_size_3610_, v___x_3617_);
lean_dec(v___x_3617_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3646_; 
lean_inc(v_r_3614_);
lean_inc(v_l_3613_);
lean_inc(v_v_3612_);
lean_inc(v_k_3611_);
v_isSharedCheck_3646_ = !lean_is_exclusive(v_l_3597_);
if (v_isSharedCheck_3646_ == 0)
{
lean_object* v_unused_3647_; lean_object* v_unused_3648_; lean_object* v_unused_3649_; lean_object* v_unused_3650_; lean_object* v_unused_3651_; 
v_unused_3647_ = lean_ctor_get(v_l_3597_, 4);
lean_dec(v_unused_3647_);
v_unused_3648_ = lean_ctor_get(v_l_3597_, 3);
lean_dec(v_unused_3648_);
v_unused_3649_ = lean_ctor_get(v_l_3597_, 2);
lean_dec(v_unused_3649_);
v_unused_3650_ = lean_ctor_get(v_l_3597_, 1);
lean_dec(v_unused_3650_);
v_unused_3651_ = lean_ctor_get(v_l_3597_, 0);
lean_dec(v_unused_3651_);
v___x_3620_ = v_l_3597_;
v_isShared_3621_ = v_isSharedCheck_3646_;
goto v_resetjp_3619_;
}
else
{
lean_dec(v_l_3597_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3646_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3636_; 
v___x_3622_ = lean_nat_add(v___x_3592_, v_size_3593_);
lean_dec(v_size_3593_);
v___x_3623_ = lean_nat_add(v___x_3622_, v_size_3594_);
lean_dec(v_size_3594_);
if (lean_obj_tag(v_l_3613_) == 0)
{
lean_object* v_size_3644_; 
v_size_3644_ = lean_ctor_get(v_l_3613_, 0);
lean_inc(v_size_3644_);
v___y_3636_ = v_size_3644_;
goto v___jp_3635_;
}
else
{
lean_object* v___x_3645_; 
v___x_3645_ = lean_unsigned_to_nat(0u);
v___y_3636_ = v___x_3645_;
goto v___jp_3635_;
}
v___jp_3624_:
{
lean_object* v___x_3628_; lean_object* v___x_3630_; 
v___x_3628_ = lean_nat_add(v___y_3625_, v___y_3627_);
lean_dec(v___y_3627_);
lean_dec(v___y_3625_);
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 4, v_r_3598_);
lean_ctor_set(v___x_3620_, 3, v_r_3614_);
lean_ctor_set(v___x_3620_, 2, v_v_3596_);
lean_ctor_set(v___x_3620_, 1, v_k_3595_);
lean_ctor_set(v___x_3620_, 0, v___x_3628_);
v___x_3630_ = v___x_3620_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3628_);
lean_ctor_set(v_reuseFailAlloc_3634_, 1, v_k_3595_);
lean_ctor_set(v_reuseFailAlloc_3634_, 2, v_v_3596_);
lean_ctor_set(v_reuseFailAlloc_3634_, 3, v_r_3614_);
lean_ctor_set(v_reuseFailAlloc_3634_, 4, v_r_3598_);
v___x_3630_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
lean_object* v___x_3632_; 
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 4, v___x_3630_);
lean_ctor_set(v___x_3608_, 3, v___y_3626_);
lean_ctor_set(v___x_3608_, 2, v_v_3612_);
lean_ctor_set(v___x_3608_, 1, v_k_3611_);
lean_ctor_set(v___x_3608_, 0, v___x_3623_);
v___x_3632_ = v___x_3608_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3623_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v_k_3611_);
lean_ctor_set(v_reuseFailAlloc_3633_, 2, v_v_3612_);
lean_ctor_set(v_reuseFailAlloc_3633_, 3, v___y_3626_);
lean_ctor_set(v_reuseFailAlloc_3633_, 4, v___x_3630_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
v___jp_3635_:
{
lean_object* v___x_3637_; lean_object* v___x_3639_; 
v___x_3637_ = lean_nat_add(v___x_3622_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec(v___x_3622_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 4, v_l_3613_);
lean_ctor_set(v___x_3588_, 3, v_impl_3591_);
lean_ctor_set(v___x_3588_, 0, v___x_3637_);
v___x_3639_ = v___x_3588_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3637_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_3643_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_3643_, 3, v_impl_3591_);
lean_ctor_set(v_reuseFailAlloc_3643_, 4, v_l_3613_);
v___x_3639_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
lean_object* v___x_3640_; 
v___x_3640_ = lean_nat_add(v___x_3592_, v_size_3615_);
if (lean_obj_tag(v_r_3614_) == 0)
{
lean_object* v_size_3641_; 
v_size_3641_ = lean_ctor_get(v_r_3614_, 0);
lean_inc(v_size_3641_);
v___y_3625_ = v___x_3640_;
v___y_3626_ = v___x_3639_;
v___y_3627_ = v_size_3641_;
goto v___jp_3624_;
}
else
{
lean_object* v___x_3642_; 
v___x_3642_ = lean_unsigned_to_nat(0u);
v___y_3625_ = v___x_3640_;
v___y_3626_ = v___x_3639_;
v___y_3627_ = v___x_3642_;
goto v___jp_3624_;
}
}
}
}
}
else
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3656_; 
lean_del_object(v___x_3588_);
v___x_3652_ = lean_nat_add(v___x_3592_, v_size_3593_);
lean_dec(v_size_3593_);
v___x_3653_ = lean_nat_add(v___x_3652_, v_size_3594_);
lean_dec(v_size_3594_);
v___x_3654_ = lean_nat_add(v___x_3652_, v_size_3610_);
lean_dec(v___x_3652_);
lean_inc_ref(v_impl_3591_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 4, v_l_3597_);
lean_ctor_set(v___x_3608_, 3, v_impl_3591_);
lean_ctor_set(v___x_3608_, 2, v_v_3584_);
lean_ctor_set(v___x_3608_, 1, v_k_3583_);
lean_ctor_set(v___x_3608_, 0, v___x_3654_);
v___x_3656_ = v___x_3608_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3654_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_3669_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_3669_, 3, v_impl_3591_);
lean_ctor_set(v_reuseFailAlloc_3669_, 4, v_l_3597_);
v___x_3656_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
v_isSharedCheck_3663_ = !lean_is_exclusive(v_impl_3591_);
if (v_isSharedCheck_3663_ == 0)
{
lean_object* v_unused_3664_; lean_object* v_unused_3665_; lean_object* v_unused_3666_; lean_object* v_unused_3667_; lean_object* v_unused_3668_; 
v_unused_3664_ = lean_ctor_get(v_impl_3591_, 4);
lean_dec(v_unused_3664_);
v_unused_3665_ = lean_ctor_get(v_impl_3591_, 3);
lean_dec(v_unused_3665_);
v_unused_3666_ = lean_ctor_get(v_impl_3591_, 2);
lean_dec(v_unused_3666_);
v_unused_3667_ = lean_ctor_get(v_impl_3591_, 1);
lean_dec(v_unused_3667_);
v_unused_3668_ = lean_ctor_get(v_impl_3591_, 0);
lean_dec(v_unused_3668_);
v___x_3658_ = v_impl_3591_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_dec(v_impl_3591_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 4, v_r_3598_);
lean_ctor_set(v___x_3658_, 3, v___x_3656_);
lean_ctor_set(v___x_3658_, 2, v_v_3596_);
lean_ctor_set(v___x_3658_, 1, v_k_3595_);
lean_ctor_set(v___x_3658_, 0, v___x_3653_);
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_k_3595_);
lean_ctor_set(v_reuseFailAlloc_3662_, 2, v_v_3596_);
lean_ctor_set(v_reuseFailAlloc_3662_, 3, v___x_3656_);
lean_ctor_set(v_reuseFailAlloc_3662_, 4, v_r_3598_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3676_; lean_object* v___x_3677_; lean_object* v___x_3679_; 
v_size_3676_ = lean_ctor_get(v_impl_3591_, 0);
lean_inc(v_size_3676_);
v___x_3677_ = lean_nat_add(v___x_3592_, v_size_3676_);
lean_dec(v_size_3676_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 3, v_impl_3591_);
lean_ctor_set(v___x_3588_, 0, v___x_3677_);
v___x_3679_ = v___x_3588_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3677_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_3680_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_3680_, 3, v_impl_3591_);
lean_ctor_set(v_reuseFailAlloc_3680_, 4, v_r_3586_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
else
{
if (lean_obj_tag(v_r_3586_) == 0)
{
lean_object* v_l_3681_; 
v_l_3681_ = lean_ctor_get(v_r_3586_, 3);
lean_inc(v_l_3681_);
if (lean_obj_tag(v_l_3681_) == 0)
{
lean_object* v_r_3682_; 
v_r_3682_ = lean_ctor_get(v_r_3586_, 4);
lean_inc(v_r_3682_);
if (lean_obj_tag(v_r_3682_) == 0)
{
lean_object* v_size_3683_; lean_object* v_k_3684_; lean_object* v_v_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3698_; 
v_size_3683_ = lean_ctor_get(v_r_3586_, 0);
v_k_3684_ = lean_ctor_get(v_r_3586_, 1);
v_v_3685_ = lean_ctor_get(v_r_3586_, 2);
v_isSharedCheck_3698_ = !lean_is_exclusive(v_r_3586_);
if (v_isSharedCheck_3698_ == 0)
{
lean_object* v_unused_3699_; lean_object* v_unused_3700_; 
v_unused_3699_ = lean_ctor_get(v_r_3586_, 4);
lean_dec(v_unused_3699_);
v_unused_3700_ = lean_ctor_get(v_r_3586_, 3);
lean_dec(v_unused_3700_);
v___x_3687_ = v_r_3586_;
v_isShared_3688_ = v_isSharedCheck_3698_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_v_3685_);
lean_inc(v_k_3684_);
lean_inc(v_size_3683_);
lean_dec(v_r_3586_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3698_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v_size_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
v_size_3689_ = lean_ctor_get(v_l_3681_, 0);
v___x_3690_ = lean_nat_add(v___x_3592_, v_size_3683_);
lean_dec(v_size_3683_);
v___x_3691_ = lean_nat_add(v___x_3592_, v_size_3689_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 4, v_l_3681_);
lean_ctor_set(v___x_3687_, 3, v_impl_3591_);
lean_ctor_set(v___x_3687_, 2, v_v_3584_);
lean_ctor_set(v___x_3687_, 1, v_k_3583_);
lean_ctor_set(v___x_3687_, 0, v___x_3691_);
v___x_3693_ = v___x_3687_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_3697_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_3697_, 3, v_impl_3591_);
lean_ctor_set(v_reuseFailAlloc_3697_, 4, v_l_3681_);
v___x_3693_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3695_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 4, v_r_3682_);
lean_ctor_set(v___x_3588_, 3, v___x_3693_);
lean_ctor_set(v___x_3588_, 2, v_v_3685_);
lean_ctor_set(v___x_3588_, 1, v_k_3684_);
lean_ctor_set(v___x_3588_, 0, v___x_3690_);
v___x_3695_ = v___x_3588_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3690_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_k_3684_);
lean_ctor_set(v_reuseFailAlloc_3696_, 2, v_v_3685_);
lean_ctor_set(v_reuseFailAlloc_3696_, 3, v___x_3693_);
lean_ctor_set(v_reuseFailAlloc_3696_, 4, v_r_3682_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
else
{
lean_object* v_k_3701_; lean_object* v_v_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3725_; 
v_k_3701_ = lean_ctor_get(v_r_3586_, 1);
v_v_3702_ = lean_ctor_get(v_r_3586_, 2);
v_isSharedCheck_3725_ = !lean_is_exclusive(v_r_3586_);
if (v_isSharedCheck_3725_ == 0)
{
lean_object* v_unused_3726_; lean_object* v_unused_3727_; lean_object* v_unused_3728_; 
v_unused_3726_ = lean_ctor_get(v_r_3586_, 4);
lean_dec(v_unused_3726_);
v_unused_3727_ = lean_ctor_get(v_r_3586_, 3);
lean_dec(v_unused_3727_);
v_unused_3728_ = lean_ctor_get(v_r_3586_, 0);
lean_dec(v_unused_3728_);
v___x_3704_ = v_r_3586_;
v_isShared_3705_ = v_isSharedCheck_3725_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_v_3702_);
lean_inc(v_k_3701_);
lean_dec(v_r_3586_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3725_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v_k_3706_; lean_object* v_v_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3721_; 
v_k_3706_ = lean_ctor_get(v_l_3681_, 1);
v_v_3707_ = lean_ctor_get(v_l_3681_, 2);
v_isSharedCheck_3721_ = !lean_is_exclusive(v_l_3681_);
if (v_isSharedCheck_3721_ == 0)
{
lean_object* v_unused_3722_; lean_object* v_unused_3723_; lean_object* v_unused_3724_; 
v_unused_3722_ = lean_ctor_get(v_l_3681_, 4);
lean_dec(v_unused_3722_);
v_unused_3723_ = lean_ctor_get(v_l_3681_, 3);
lean_dec(v_unused_3723_);
v_unused_3724_ = lean_ctor_get(v_l_3681_, 0);
lean_dec(v_unused_3724_);
v___x_3709_ = v_l_3681_;
v_isShared_3710_ = v_isSharedCheck_3721_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_v_3707_);
lean_inc(v_k_3706_);
lean_dec(v_l_3681_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3721_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3711_; lean_object* v___x_3713_; 
v___x_3711_ = lean_unsigned_to_nat(3u);
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 4, v_r_3682_);
lean_ctor_set(v___x_3709_, 3, v_r_3682_);
lean_ctor_set(v___x_3709_, 2, v_v_3584_);
lean_ctor_set(v___x_3709_, 1, v_k_3583_);
lean_ctor_set(v___x_3709_, 0, v___x_3592_);
v___x_3713_ = v___x_3709_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3720_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_3720_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_3720_, 3, v_r_3682_);
lean_ctor_set(v_reuseFailAlloc_3720_, 4, v_r_3682_);
v___x_3713_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
lean_object* v___x_3715_; 
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 3, v_r_3682_);
lean_ctor_set(v___x_3704_, 0, v___x_3592_);
v___x_3715_ = v___x_3704_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_k_3701_);
lean_ctor_set(v_reuseFailAlloc_3719_, 2, v_v_3702_);
lean_ctor_set(v_reuseFailAlloc_3719_, 3, v_r_3682_);
lean_ctor_set(v_reuseFailAlloc_3719_, 4, v_r_3682_);
v___x_3715_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
lean_object* v___x_3717_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 4, v___x_3715_);
lean_ctor_set(v___x_3588_, 3, v___x_3713_);
lean_ctor_set(v___x_3588_, 2, v_v_3707_);
lean_ctor_set(v___x_3588_, 1, v_k_3706_);
lean_ctor_set(v___x_3588_, 0, v___x_3711_);
v___x_3717_ = v___x_3588_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3711_);
lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_k_3706_);
lean_ctor_set(v_reuseFailAlloc_3718_, 2, v_v_3707_);
lean_ctor_set(v_reuseFailAlloc_3718_, 3, v___x_3713_);
lean_ctor_set(v_reuseFailAlloc_3718_, 4, v___x_3715_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3729_; 
v_r_3729_ = lean_ctor_get(v_r_3586_, 4);
lean_inc(v_r_3729_);
if (lean_obj_tag(v_r_3729_) == 0)
{
lean_object* v_k_3730_; lean_object* v_v_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3742_; 
v_k_3730_ = lean_ctor_get(v_r_3586_, 1);
v_v_3731_ = lean_ctor_get(v_r_3586_, 2);
v_isSharedCheck_3742_ = !lean_is_exclusive(v_r_3586_);
if (v_isSharedCheck_3742_ == 0)
{
lean_object* v_unused_3743_; lean_object* v_unused_3744_; lean_object* v_unused_3745_; 
v_unused_3743_ = lean_ctor_get(v_r_3586_, 4);
lean_dec(v_unused_3743_);
v_unused_3744_ = lean_ctor_get(v_r_3586_, 3);
lean_dec(v_unused_3744_);
v_unused_3745_ = lean_ctor_get(v_r_3586_, 0);
lean_dec(v_unused_3745_);
v___x_3733_ = v_r_3586_;
v_isShared_3734_ = v_isSharedCheck_3742_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_v_3731_);
lean_inc(v_k_3730_);
lean_dec(v_r_3586_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3742_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3735_; lean_object* v___x_3737_; 
v___x_3735_ = lean_unsigned_to_nat(3u);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 4, v_l_3681_);
lean_ctor_set(v___x_3733_, 2, v_v_3584_);
lean_ctor_set(v___x_3733_, 1, v_k_3583_);
lean_ctor_set(v___x_3733_, 0, v___x_3592_);
v___x_3737_ = v___x_3733_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_3741_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_3741_, 3, v_l_3681_);
lean_ctor_set(v_reuseFailAlloc_3741_, 4, v_l_3681_);
v___x_3737_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
lean_object* v___x_3739_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 4, v_r_3729_);
lean_ctor_set(v___x_3588_, 3, v___x_3737_);
lean_ctor_set(v___x_3588_, 2, v_v_3731_);
lean_ctor_set(v___x_3588_, 1, v_k_3730_);
lean_ctor_set(v___x_3588_, 0, v___x_3735_);
v___x_3739_ = v___x_3588_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3735_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v_k_3730_);
lean_ctor_set(v_reuseFailAlloc_3740_, 2, v_v_3731_);
lean_ctor_set(v_reuseFailAlloc_3740_, 3, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3740_, 4, v_r_3729_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
else
{
lean_object* v_size_3746_; lean_object* v_k_3747_; lean_object* v_v_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3759_; 
v_size_3746_ = lean_ctor_get(v_r_3586_, 0);
v_k_3747_ = lean_ctor_get(v_r_3586_, 1);
v_v_3748_ = lean_ctor_get(v_r_3586_, 2);
v_isSharedCheck_3759_ = !lean_is_exclusive(v_r_3586_);
if (v_isSharedCheck_3759_ == 0)
{
lean_object* v_unused_3760_; lean_object* v_unused_3761_; 
v_unused_3760_ = lean_ctor_get(v_r_3586_, 4);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_r_3586_, 3);
lean_dec(v_unused_3761_);
v___x_3750_ = v_r_3586_;
v_isShared_3751_ = v_isSharedCheck_3759_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_v_3748_);
lean_inc(v_k_3747_);
lean_inc(v_size_3746_);
lean_dec(v_r_3586_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3759_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 3, v_r_3729_);
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_size_3746_);
lean_ctor_set(v_reuseFailAlloc_3758_, 1, v_k_3747_);
lean_ctor_set(v_reuseFailAlloc_3758_, 2, v_v_3748_);
lean_ctor_set(v_reuseFailAlloc_3758_, 3, v_r_3729_);
lean_ctor_set(v_reuseFailAlloc_3758_, 4, v_r_3729_);
v___x_3753_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
lean_object* v___x_3754_; lean_object* v___x_3756_; 
v___x_3754_ = lean_unsigned_to_nat(2u);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 4, v___x_3753_);
lean_ctor_set(v___x_3588_, 3, v_r_3729_);
lean_ctor_set(v___x_3588_, 0, v___x_3754_);
v___x_3756_ = v___x_3588_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3754_);
lean_ctor_set(v_reuseFailAlloc_3757_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_3757_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_3757_, 3, v_r_3729_);
lean_ctor_set(v_reuseFailAlloc_3757_, 4, v___x_3753_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
}
}
else
{
lean_object* v___x_3763_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 3, v_r_3586_);
lean_ctor_set(v___x_3588_, 0, v___x_3592_);
v___x_3763_ = v___x_3588_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_3764_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_3764_, 3, v_r_3586_);
lean_ctor_set(v_reuseFailAlloc_3764_, 4, v_r_3586_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3588_);
lean_dec(v_v_3584_);
lean_dec(v_k_3583_);
if (lean_obj_tag(v_l_3585_) == 0)
{
if (lean_obj_tag(v_r_3586_) == 0)
{
lean_object* v_size_3765_; lean_object* v_k_3766_; lean_object* v_v_3767_; lean_object* v_l_3768_; lean_object* v_r_3769_; lean_object* v_size_3770_; lean_object* v_k_3771_; lean_object* v_v_3772_; lean_object* v_l_3773_; lean_object* v_r_3774_; lean_object* v___x_3775_; uint8_t v___x_3776_; 
v_size_3765_ = lean_ctor_get(v_l_3585_, 0);
v_k_3766_ = lean_ctor_get(v_l_3585_, 1);
v_v_3767_ = lean_ctor_get(v_l_3585_, 2);
v_l_3768_ = lean_ctor_get(v_l_3585_, 3);
v_r_3769_ = lean_ctor_get(v_l_3585_, 4);
lean_inc(v_r_3769_);
v_size_3770_ = lean_ctor_get(v_r_3586_, 0);
v_k_3771_ = lean_ctor_get(v_r_3586_, 1);
v_v_3772_ = lean_ctor_get(v_r_3586_, 2);
v_l_3773_ = lean_ctor_get(v_r_3586_, 3);
lean_inc(v_l_3773_);
v_r_3774_ = lean_ctor_get(v_r_3586_, 4);
v___x_3775_ = lean_unsigned_to_nat(1u);
v___x_3776_ = lean_nat_dec_lt(v_size_3765_, v_size_3770_);
if (v___x_3776_ == 0)
{
lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3912_; 
lean_inc(v_l_3768_);
lean_inc(v_v_3767_);
lean_inc(v_k_3766_);
v_isSharedCheck_3912_ = !lean_is_exclusive(v_l_3585_);
if (v_isSharedCheck_3912_ == 0)
{
lean_object* v_unused_3913_; lean_object* v_unused_3914_; lean_object* v_unused_3915_; lean_object* v_unused_3916_; lean_object* v_unused_3917_; 
v_unused_3913_ = lean_ctor_get(v_l_3585_, 4);
lean_dec(v_unused_3913_);
v_unused_3914_ = lean_ctor_get(v_l_3585_, 3);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_l_3585_, 2);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_l_3585_, 1);
lean_dec(v_unused_3916_);
v_unused_3917_ = lean_ctor_get(v_l_3585_, 0);
lean_dec(v_unused_3917_);
v___x_3778_ = v_l_3585_;
v_isShared_3779_ = v_isSharedCheck_3912_;
goto v_resetjp_3777_;
}
else
{
lean_dec(v_l_3585_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3912_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3780_; lean_object* v_tree_3781_; 
v___x_3780_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3766_, v_v_3767_, v_l_3768_, v_r_3769_);
v_tree_3781_ = lean_ctor_get(v___x_3780_, 2);
lean_inc(v_tree_3781_);
if (lean_obj_tag(v_tree_3781_) == 0)
{
lean_object* v_k_3782_; lean_object* v_v_3783_; lean_object* v_size_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; uint8_t v___x_3787_; 
v_k_3782_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_k_3782_);
v_v_3783_ = lean_ctor_get(v___x_3780_, 1);
lean_inc(v_v_3783_);
lean_dec_ref(v___x_3780_);
v_size_3784_ = lean_ctor_get(v_tree_3781_, 0);
v___x_3785_ = lean_unsigned_to_nat(3u);
v___x_3786_ = lean_nat_mul(v___x_3785_, v_size_3784_);
v___x_3787_ = lean_nat_dec_lt(v___x_3786_, v_size_3770_);
lean_dec(v___x_3786_);
if (v___x_3787_ == 0)
{
lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3791_; 
lean_dec(v_l_3773_);
v___x_3788_ = lean_nat_add(v___x_3775_, v_size_3784_);
v___x_3789_ = lean_nat_add(v___x_3788_, v_size_3770_);
lean_dec(v___x_3788_);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v_r_3586_);
lean_ctor_set(v___x_3778_, 3, v_tree_3781_);
lean_ctor_set(v___x_3778_, 2, v_v_3783_);
lean_ctor_set(v___x_3778_, 1, v_k_3782_);
lean_ctor_set(v___x_3778_, 0, v___x_3789_);
v___x_3791_ = v___x_3778_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3789_);
lean_ctor_set(v_reuseFailAlloc_3792_, 1, v_k_3782_);
lean_ctor_set(v_reuseFailAlloc_3792_, 2, v_v_3783_);
lean_ctor_set(v_reuseFailAlloc_3792_, 3, v_tree_3781_);
lean_ctor_set(v_reuseFailAlloc_3792_, 4, v_r_3586_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
else
{
lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3847_; 
lean_inc(v_r_3774_);
lean_inc(v_v_3772_);
lean_inc(v_k_3771_);
lean_inc(v_size_3770_);
v_isSharedCheck_3847_ = !lean_is_exclusive(v_r_3586_);
if (v_isSharedCheck_3847_ == 0)
{
lean_object* v_unused_3848_; lean_object* v_unused_3849_; lean_object* v_unused_3850_; lean_object* v_unused_3851_; lean_object* v_unused_3852_; 
v_unused_3848_ = lean_ctor_get(v_r_3586_, 4);
lean_dec(v_unused_3848_);
v_unused_3849_ = lean_ctor_get(v_r_3586_, 3);
lean_dec(v_unused_3849_);
v_unused_3850_ = lean_ctor_get(v_r_3586_, 2);
lean_dec(v_unused_3850_);
v_unused_3851_ = lean_ctor_get(v_r_3586_, 1);
lean_dec(v_unused_3851_);
v_unused_3852_ = lean_ctor_get(v_r_3586_, 0);
lean_dec(v_unused_3852_);
v___x_3794_ = v_r_3586_;
v_isShared_3795_ = v_isSharedCheck_3847_;
goto v_resetjp_3793_;
}
else
{
lean_dec(v_r_3586_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3847_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v_size_3796_; lean_object* v_k_3797_; lean_object* v_v_3798_; lean_object* v_l_3799_; lean_object* v_r_3800_; lean_object* v_size_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
v_size_3796_ = lean_ctor_get(v_l_3773_, 0);
v_k_3797_ = lean_ctor_get(v_l_3773_, 1);
v_v_3798_ = lean_ctor_get(v_l_3773_, 2);
v_l_3799_ = lean_ctor_get(v_l_3773_, 3);
v_r_3800_ = lean_ctor_get(v_l_3773_, 4);
v_size_3801_ = lean_ctor_get(v_r_3774_, 0);
v___x_3802_ = lean_unsigned_to_nat(2u);
v___x_3803_ = lean_nat_mul(v___x_3802_, v_size_3801_);
v___x_3804_ = lean_nat_dec_lt(v_size_3796_, v___x_3803_);
lean_dec(v___x_3803_);
if (v___x_3804_ == 0)
{
lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3832_; 
lean_inc(v_r_3800_);
lean_inc(v_l_3799_);
lean_inc(v_v_3798_);
lean_inc(v_k_3797_);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_l_3773_);
if (v_isSharedCheck_3832_ == 0)
{
lean_object* v_unused_3833_; lean_object* v_unused_3834_; lean_object* v_unused_3835_; lean_object* v_unused_3836_; lean_object* v_unused_3837_; 
v_unused_3833_ = lean_ctor_get(v_l_3773_, 4);
lean_dec(v_unused_3833_);
v_unused_3834_ = lean_ctor_get(v_l_3773_, 3);
lean_dec(v_unused_3834_);
v_unused_3835_ = lean_ctor_get(v_l_3773_, 2);
lean_dec(v_unused_3835_);
v_unused_3836_ = lean_ctor_get(v_l_3773_, 1);
lean_dec(v_unused_3836_);
v_unused_3837_ = lean_ctor_get(v_l_3773_, 0);
lean_dec(v_unused_3837_);
v___x_3806_ = v_l_3773_;
v_isShared_3807_ = v_isSharedCheck_3832_;
goto v_resetjp_3805_;
}
else
{
lean_dec(v_l_3773_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3832_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3822_; 
v___x_3808_ = lean_nat_add(v___x_3775_, v_size_3784_);
v___x_3809_ = lean_nat_add(v___x_3808_, v_size_3770_);
lean_dec(v_size_3770_);
if (lean_obj_tag(v_l_3799_) == 0)
{
lean_object* v_size_3830_; 
v_size_3830_ = lean_ctor_get(v_l_3799_, 0);
lean_inc(v_size_3830_);
v___y_3822_ = v_size_3830_;
goto v___jp_3821_;
}
else
{
lean_object* v___x_3831_; 
v___x_3831_ = lean_unsigned_to_nat(0u);
v___y_3822_ = v___x_3831_;
goto v___jp_3821_;
}
v___jp_3810_:
{
lean_object* v___x_3814_; lean_object* v___x_3816_; 
v___x_3814_ = lean_nat_add(v___y_3811_, v___y_3813_);
lean_dec(v___y_3813_);
lean_dec(v___y_3811_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 4, v_r_3774_);
lean_ctor_set(v___x_3806_, 3, v_r_3800_);
lean_ctor_set(v___x_3806_, 2, v_v_3772_);
lean_ctor_set(v___x_3806_, 1, v_k_3771_);
lean_ctor_set(v___x_3806_, 0, v___x_3814_);
v___x_3816_ = v___x_3806_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3814_);
lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_k_3771_);
lean_ctor_set(v_reuseFailAlloc_3820_, 2, v_v_3772_);
lean_ctor_set(v_reuseFailAlloc_3820_, 3, v_r_3800_);
lean_ctor_set(v_reuseFailAlloc_3820_, 4, v_r_3774_);
v___x_3816_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
lean_object* v___x_3818_; 
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 4, v___x_3816_);
lean_ctor_set(v___x_3794_, 3, v___y_3812_);
lean_ctor_set(v___x_3794_, 2, v_v_3798_);
lean_ctor_set(v___x_3794_, 1, v_k_3797_);
lean_ctor_set(v___x_3794_, 0, v___x_3809_);
v___x_3818_ = v___x_3794_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3809_);
lean_ctor_set(v_reuseFailAlloc_3819_, 1, v_k_3797_);
lean_ctor_set(v_reuseFailAlloc_3819_, 2, v_v_3798_);
lean_ctor_set(v_reuseFailAlloc_3819_, 3, v___y_3812_);
lean_ctor_set(v_reuseFailAlloc_3819_, 4, v___x_3816_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
v___jp_3821_:
{
lean_object* v___x_3823_; lean_object* v___x_3825_; 
v___x_3823_ = lean_nat_add(v___x_3808_, v___y_3822_);
lean_dec(v___y_3822_);
lean_dec(v___x_3808_);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v_l_3799_);
lean_ctor_set(v___x_3778_, 3, v_tree_3781_);
lean_ctor_set(v___x_3778_, 2, v_v_3783_);
lean_ctor_set(v___x_3778_, 1, v_k_3782_);
lean_ctor_set(v___x_3778_, 0, v___x_3823_);
v___x_3825_ = v___x_3778_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v___x_3823_);
lean_ctor_set(v_reuseFailAlloc_3829_, 1, v_k_3782_);
lean_ctor_set(v_reuseFailAlloc_3829_, 2, v_v_3783_);
lean_ctor_set(v_reuseFailAlloc_3829_, 3, v_tree_3781_);
lean_ctor_set(v_reuseFailAlloc_3829_, 4, v_l_3799_);
v___x_3825_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3826_; 
v___x_3826_ = lean_nat_add(v___x_3775_, v_size_3801_);
if (lean_obj_tag(v_r_3800_) == 0)
{
lean_object* v_size_3827_; 
v_size_3827_ = lean_ctor_get(v_r_3800_, 0);
lean_inc(v_size_3827_);
v___y_3811_ = v___x_3826_;
v___y_3812_ = v___x_3825_;
v___y_3813_ = v_size_3827_;
goto v___jp_3810_;
}
else
{
lean_object* v___x_3828_; 
v___x_3828_ = lean_unsigned_to_nat(0u);
v___y_3811_ = v___x_3826_;
v___y_3812_ = v___x_3825_;
v___y_3813_ = v___x_3828_;
goto v___jp_3810_;
}
}
}
}
}
else
{
lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3842_; 
v___x_3838_ = lean_nat_add(v___x_3775_, v_size_3784_);
v___x_3839_ = lean_nat_add(v___x_3838_, v_size_3770_);
lean_dec(v_size_3770_);
v___x_3840_ = lean_nat_add(v___x_3838_, v_size_3796_);
lean_dec(v___x_3838_);
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 4, v_l_3773_);
lean_ctor_set(v___x_3794_, 3, v_tree_3781_);
lean_ctor_set(v___x_3794_, 2, v_v_3783_);
lean_ctor_set(v___x_3794_, 1, v_k_3782_);
lean_ctor_set(v___x_3794_, 0, v___x_3840_);
v___x_3842_ = v___x_3794_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3840_);
lean_ctor_set(v_reuseFailAlloc_3846_, 1, v_k_3782_);
lean_ctor_set(v_reuseFailAlloc_3846_, 2, v_v_3783_);
lean_ctor_set(v_reuseFailAlloc_3846_, 3, v_tree_3781_);
lean_ctor_set(v_reuseFailAlloc_3846_, 4, v_l_3773_);
v___x_3842_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
lean_object* v___x_3844_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v_r_3774_);
lean_ctor_set(v___x_3778_, 3, v___x_3842_);
lean_ctor_set(v___x_3778_, 2, v_v_3772_);
lean_ctor_set(v___x_3778_, 1, v_k_3771_);
lean_ctor_set(v___x_3778_, 0, v___x_3839_);
v___x_3844_ = v___x_3778_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3839_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v_k_3771_);
lean_ctor_set(v_reuseFailAlloc_3845_, 2, v_v_3772_);
lean_ctor_set(v_reuseFailAlloc_3845_, 3, v___x_3842_);
lean_ctor_set(v_reuseFailAlloc_3845_, 4, v_r_3774_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
}
}
else
{
lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3906_; 
lean_inc(v_r_3774_);
lean_inc(v_v_3772_);
lean_inc(v_k_3771_);
lean_inc(v_size_3770_);
v_isSharedCheck_3906_ = !lean_is_exclusive(v_r_3586_);
if (v_isSharedCheck_3906_ == 0)
{
lean_object* v_unused_3907_; lean_object* v_unused_3908_; lean_object* v_unused_3909_; lean_object* v_unused_3910_; lean_object* v_unused_3911_; 
v_unused_3907_ = lean_ctor_get(v_r_3586_, 4);
lean_dec(v_unused_3907_);
v_unused_3908_ = lean_ctor_get(v_r_3586_, 3);
lean_dec(v_unused_3908_);
v_unused_3909_ = lean_ctor_get(v_r_3586_, 2);
lean_dec(v_unused_3909_);
v_unused_3910_ = lean_ctor_get(v_r_3586_, 1);
lean_dec(v_unused_3910_);
v_unused_3911_ = lean_ctor_get(v_r_3586_, 0);
lean_dec(v_unused_3911_);
v___x_3854_ = v_r_3586_;
v_isShared_3855_ = v_isSharedCheck_3906_;
goto v_resetjp_3853_;
}
else
{
lean_dec(v_r_3586_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3906_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
if (lean_obj_tag(v_l_3773_) == 0)
{
if (lean_obj_tag(v_r_3774_) == 0)
{
lean_object* v_k_3856_; lean_object* v_v_3857_; lean_object* v_size_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3862_; 
v_k_3856_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_k_3856_);
v_v_3857_ = lean_ctor_get(v___x_3780_, 1);
lean_inc(v_v_3857_);
lean_dec_ref(v___x_3780_);
v_size_3858_ = lean_ctor_get(v_l_3773_, 0);
v___x_3859_ = lean_nat_add(v___x_3775_, v_size_3770_);
lean_dec(v_size_3770_);
v___x_3860_ = lean_nat_add(v___x_3775_, v_size_3858_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 4, v_l_3773_);
lean_ctor_set(v___x_3854_, 3, v_tree_3781_);
lean_ctor_set(v___x_3854_, 2, v_v_3857_);
lean_ctor_set(v___x_3854_, 1, v_k_3856_);
lean_ctor_set(v___x_3854_, 0, v___x_3860_);
v___x_3862_ = v___x_3854_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3860_);
lean_ctor_set(v_reuseFailAlloc_3866_, 1, v_k_3856_);
lean_ctor_set(v_reuseFailAlloc_3866_, 2, v_v_3857_);
lean_ctor_set(v_reuseFailAlloc_3866_, 3, v_tree_3781_);
lean_ctor_set(v_reuseFailAlloc_3866_, 4, v_l_3773_);
v___x_3862_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
lean_object* v___x_3864_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v_r_3774_);
lean_ctor_set(v___x_3778_, 3, v___x_3862_);
lean_ctor_set(v___x_3778_, 2, v_v_3772_);
lean_ctor_set(v___x_3778_, 1, v_k_3771_);
lean_ctor_set(v___x_3778_, 0, v___x_3859_);
v___x_3864_ = v___x_3778_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_k_3771_);
lean_ctor_set(v_reuseFailAlloc_3865_, 2, v_v_3772_);
lean_ctor_set(v_reuseFailAlloc_3865_, 3, v___x_3862_);
lean_ctor_set(v_reuseFailAlloc_3865_, 4, v_r_3774_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
else
{
lean_object* v_k_3867_; lean_object* v_v_3868_; lean_object* v_k_3869_; lean_object* v_v_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3884_; 
lean_dec(v_size_3770_);
v_k_3867_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_k_3867_);
v_v_3868_ = lean_ctor_get(v___x_3780_, 1);
lean_inc(v_v_3868_);
lean_dec_ref(v___x_3780_);
v_k_3869_ = lean_ctor_get(v_l_3773_, 1);
v_v_3870_ = lean_ctor_get(v_l_3773_, 2);
v_isSharedCheck_3884_ = !lean_is_exclusive(v_l_3773_);
if (v_isSharedCheck_3884_ == 0)
{
lean_object* v_unused_3885_; lean_object* v_unused_3886_; lean_object* v_unused_3887_; 
v_unused_3885_ = lean_ctor_get(v_l_3773_, 4);
lean_dec(v_unused_3885_);
v_unused_3886_ = lean_ctor_get(v_l_3773_, 3);
lean_dec(v_unused_3886_);
v_unused_3887_ = lean_ctor_get(v_l_3773_, 0);
lean_dec(v_unused_3887_);
v___x_3872_ = v_l_3773_;
v_isShared_3873_ = v_isSharedCheck_3884_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_v_3870_);
lean_inc(v_k_3869_);
lean_dec(v_l_3773_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3884_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3874_; lean_object* v___x_3876_; 
v___x_3874_ = lean_unsigned_to_nat(3u);
if (v_isShared_3873_ == 0)
{
lean_ctor_set(v___x_3872_, 4, v_r_3774_);
lean_ctor_set(v___x_3872_, 3, v_r_3774_);
lean_ctor_set(v___x_3872_, 2, v_v_3868_);
lean_ctor_set(v___x_3872_, 1, v_k_3867_);
lean_ctor_set(v___x_3872_, 0, v___x_3775_);
v___x_3876_ = v___x_3872_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_3883_, 1, v_k_3867_);
lean_ctor_set(v_reuseFailAlloc_3883_, 2, v_v_3868_);
lean_ctor_set(v_reuseFailAlloc_3883_, 3, v_r_3774_);
lean_ctor_set(v_reuseFailAlloc_3883_, 4, v_r_3774_);
v___x_3876_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
lean_object* v___x_3878_; 
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 3, v_r_3774_);
lean_ctor_set(v___x_3854_, 0, v___x_3775_);
v___x_3878_ = v___x_3854_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_3882_, 1, v_k_3771_);
lean_ctor_set(v_reuseFailAlloc_3882_, 2, v_v_3772_);
lean_ctor_set(v_reuseFailAlloc_3882_, 3, v_r_3774_);
lean_ctor_set(v_reuseFailAlloc_3882_, 4, v_r_3774_);
v___x_3878_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
lean_object* v___x_3880_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v___x_3878_);
lean_ctor_set(v___x_3778_, 3, v___x_3876_);
lean_ctor_set(v___x_3778_, 2, v_v_3870_);
lean_ctor_set(v___x_3778_, 1, v_k_3869_);
lean_ctor_set(v___x_3778_, 0, v___x_3874_);
v___x_3880_ = v___x_3778_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v___x_3874_);
lean_ctor_set(v_reuseFailAlloc_3881_, 1, v_k_3869_);
lean_ctor_set(v_reuseFailAlloc_3881_, 2, v_v_3870_);
lean_ctor_set(v_reuseFailAlloc_3881_, 3, v___x_3876_);
lean_ctor_set(v_reuseFailAlloc_3881_, 4, v___x_3878_);
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
if (lean_obj_tag(v_r_3774_) == 0)
{
lean_object* v_k_3888_; lean_object* v_v_3889_; lean_object* v___x_3890_; lean_object* v___x_3892_; 
lean_dec(v_size_3770_);
v_k_3888_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_k_3888_);
v_v_3889_ = lean_ctor_get(v___x_3780_, 1);
lean_inc(v_v_3889_);
lean_dec_ref(v___x_3780_);
v___x_3890_ = lean_unsigned_to_nat(3u);
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 4, v_l_3773_);
lean_ctor_set(v___x_3854_, 2, v_v_3889_);
lean_ctor_set(v___x_3854_, 1, v_k_3888_);
lean_ctor_set(v___x_3854_, 0, v___x_3775_);
v___x_3892_ = v___x_3854_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_3896_, 1, v_k_3888_);
lean_ctor_set(v_reuseFailAlloc_3896_, 2, v_v_3889_);
lean_ctor_set(v_reuseFailAlloc_3896_, 3, v_l_3773_);
lean_ctor_set(v_reuseFailAlloc_3896_, 4, v_l_3773_);
v___x_3892_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
lean_object* v___x_3894_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v_r_3774_);
lean_ctor_set(v___x_3778_, 3, v___x_3892_);
lean_ctor_set(v___x_3778_, 2, v_v_3772_);
lean_ctor_set(v___x_3778_, 1, v_k_3771_);
lean_ctor_set(v___x_3778_, 0, v___x_3890_);
v___x_3894_ = v___x_3778_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3890_);
lean_ctor_set(v_reuseFailAlloc_3895_, 1, v_k_3771_);
lean_ctor_set(v_reuseFailAlloc_3895_, 2, v_v_3772_);
lean_ctor_set(v_reuseFailAlloc_3895_, 3, v___x_3892_);
lean_ctor_set(v_reuseFailAlloc_3895_, 4, v_r_3774_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
else
{
lean_object* v_k_3897_; lean_object* v_v_3898_; lean_object* v___x_3900_; 
v_k_3897_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_k_3897_);
v_v_3898_ = lean_ctor_get(v___x_3780_, 1);
lean_inc(v_v_3898_);
lean_dec_ref(v___x_3780_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 3, v_r_3774_);
v___x_3900_ = v___x_3854_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_size_3770_);
lean_ctor_set(v_reuseFailAlloc_3905_, 1, v_k_3771_);
lean_ctor_set(v_reuseFailAlloc_3905_, 2, v_v_3772_);
lean_ctor_set(v_reuseFailAlloc_3905_, 3, v_r_3774_);
lean_ctor_set(v_reuseFailAlloc_3905_, 4, v_r_3774_);
v___x_3900_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
lean_object* v___x_3901_; lean_object* v___x_3903_; 
v___x_3901_ = lean_unsigned_to_nat(2u);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v___x_3900_);
lean_ctor_set(v___x_3778_, 3, v_r_3774_);
lean_ctor_set(v___x_3778_, 2, v_v_3898_);
lean_ctor_set(v___x_3778_, 1, v_k_3897_);
lean_ctor_set(v___x_3778_, 0, v___x_3901_);
v___x_3903_ = v___x_3778_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3901_);
lean_ctor_set(v_reuseFailAlloc_3904_, 1, v_k_3897_);
lean_ctor_set(v_reuseFailAlloc_3904_, 2, v_v_3898_);
lean_ctor_set(v_reuseFailAlloc_3904_, 3, v_r_3774_);
lean_ctor_set(v_reuseFailAlloc_3904_, 4, v___x_3900_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
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
lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_4070_; 
lean_inc(v_r_3774_);
lean_inc(v_v_3772_);
lean_inc(v_k_3771_);
v_isSharedCheck_4070_ = !lean_is_exclusive(v_r_3586_);
if (v_isSharedCheck_4070_ == 0)
{
lean_object* v_unused_4071_; lean_object* v_unused_4072_; lean_object* v_unused_4073_; lean_object* v_unused_4074_; lean_object* v_unused_4075_; 
v_unused_4071_ = lean_ctor_get(v_r_3586_, 4);
lean_dec(v_unused_4071_);
v_unused_4072_ = lean_ctor_get(v_r_3586_, 3);
lean_dec(v_unused_4072_);
v_unused_4073_ = lean_ctor_get(v_r_3586_, 2);
lean_dec(v_unused_4073_);
v_unused_4074_ = lean_ctor_get(v_r_3586_, 1);
lean_dec(v_unused_4074_);
v_unused_4075_ = lean_ctor_get(v_r_3586_, 0);
lean_dec(v_unused_4075_);
v___x_3919_ = v_r_3586_;
v_isShared_3920_ = v_isSharedCheck_4070_;
goto v_resetjp_3918_;
}
else
{
lean_dec(v_r_3586_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_4070_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3921_; lean_object* v_tree_3922_; 
v___x_3921_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3771_, v_v_3772_, v_l_3773_, v_r_3774_);
v_tree_3922_ = lean_ctor_get(v___x_3921_, 2);
lean_inc(v_tree_3922_);
if (lean_obj_tag(v_tree_3922_) == 0)
{
lean_object* v_k_3923_; lean_object* v_v_3924_; lean_object* v_size_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; uint8_t v___x_3928_; 
v_k_3923_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_k_3923_);
v_v_3924_ = lean_ctor_get(v___x_3921_, 1);
lean_inc(v_v_3924_);
lean_dec_ref(v___x_3921_);
v_size_3925_ = lean_ctor_get(v_tree_3922_, 0);
v___x_3926_ = lean_unsigned_to_nat(3u);
v___x_3927_ = lean_nat_mul(v___x_3926_, v_size_3925_);
v___x_3928_ = lean_nat_dec_lt(v___x_3927_, v_size_3765_);
lean_dec(v___x_3927_);
if (v___x_3928_ == 0)
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3932_; 
lean_dec(v_r_3769_);
v___x_3929_ = lean_nat_add(v___x_3775_, v_size_3765_);
v___x_3930_ = lean_nat_add(v___x_3929_, v_size_3925_);
lean_dec(v___x_3929_);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 4, v_tree_3922_);
lean_ctor_set(v___x_3919_, 3, v_l_3585_);
lean_ctor_set(v___x_3919_, 2, v_v_3924_);
lean_ctor_set(v___x_3919_, 1, v_k_3923_);
lean_ctor_set(v___x_3919_, 0, v___x_3930_);
v___x_3932_ = v___x_3919_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v___x_3930_);
lean_ctor_set(v_reuseFailAlloc_3933_, 1, v_k_3923_);
lean_ctor_set(v_reuseFailAlloc_3933_, 2, v_v_3924_);
lean_ctor_set(v_reuseFailAlloc_3933_, 3, v_l_3585_);
lean_ctor_set(v_reuseFailAlloc_3933_, 4, v_tree_3922_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
else
{
lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3999_; 
lean_inc(v_l_3768_);
lean_inc(v_v_3767_);
lean_inc(v_k_3766_);
lean_inc(v_size_3765_);
v_isSharedCheck_3999_ = !lean_is_exclusive(v_l_3585_);
if (v_isSharedCheck_3999_ == 0)
{
lean_object* v_unused_4000_; lean_object* v_unused_4001_; lean_object* v_unused_4002_; lean_object* v_unused_4003_; lean_object* v_unused_4004_; 
v_unused_4000_ = lean_ctor_get(v_l_3585_, 4);
lean_dec(v_unused_4000_);
v_unused_4001_ = lean_ctor_get(v_l_3585_, 3);
lean_dec(v_unused_4001_);
v_unused_4002_ = lean_ctor_get(v_l_3585_, 2);
lean_dec(v_unused_4002_);
v_unused_4003_ = lean_ctor_get(v_l_3585_, 1);
lean_dec(v_unused_4003_);
v_unused_4004_ = lean_ctor_get(v_l_3585_, 0);
lean_dec(v_unused_4004_);
v___x_3935_ = v_l_3585_;
v_isShared_3936_ = v_isSharedCheck_3999_;
goto v_resetjp_3934_;
}
else
{
lean_dec(v_l_3585_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3999_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v_size_3937_; lean_object* v_size_3938_; lean_object* v_k_3939_; lean_object* v_v_3940_; lean_object* v_l_3941_; lean_object* v_r_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; uint8_t v___x_3945_; 
v_size_3937_ = lean_ctor_get(v_l_3768_, 0);
v_size_3938_ = lean_ctor_get(v_r_3769_, 0);
v_k_3939_ = lean_ctor_get(v_r_3769_, 1);
v_v_3940_ = lean_ctor_get(v_r_3769_, 2);
v_l_3941_ = lean_ctor_get(v_r_3769_, 3);
v_r_3942_ = lean_ctor_get(v_r_3769_, 4);
v___x_3943_ = lean_unsigned_to_nat(2u);
v___x_3944_ = lean_nat_mul(v___x_3943_, v_size_3937_);
v___x_3945_ = lean_nat_dec_lt(v_size_3938_, v___x_3944_);
lean_dec(v___x_3944_);
if (v___x_3945_ == 0)
{
lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3983_; 
lean_inc(v_r_3942_);
lean_inc(v_l_3941_);
lean_inc(v_v_3940_);
lean_inc(v_k_3939_);
lean_del_object(v___x_3935_);
v_isSharedCheck_3983_ = !lean_is_exclusive(v_r_3769_);
if (v_isSharedCheck_3983_ == 0)
{
lean_object* v_unused_3984_; lean_object* v_unused_3985_; lean_object* v_unused_3986_; lean_object* v_unused_3987_; lean_object* v_unused_3988_; 
v_unused_3984_ = lean_ctor_get(v_r_3769_, 4);
lean_dec(v_unused_3984_);
v_unused_3985_ = lean_ctor_get(v_r_3769_, 3);
lean_dec(v_unused_3985_);
v_unused_3986_ = lean_ctor_get(v_r_3769_, 2);
lean_dec(v_unused_3986_);
v_unused_3987_ = lean_ctor_get(v_r_3769_, 1);
lean_dec(v_unused_3987_);
v_unused_3988_ = lean_ctor_get(v_r_3769_, 0);
lean_dec(v_unused_3988_);
v___x_3947_ = v_r_3769_;
v_isShared_3948_ = v_isSharedCheck_3983_;
goto v_resetjp_3946_;
}
else
{
lean_dec(v_r_3769_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3983_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___x_3971_; lean_object* v___y_3973_; 
v___x_3949_ = lean_nat_add(v___x_3775_, v_size_3765_);
lean_dec(v_size_3765_);
v___x_3950_ = lean_nat_add(v___x_3949_, v_size_3925_);
lean_dec(v___x_3949_);
v___x_3971_ = lean_nat_add(v___x_3775_, v_size_3937_);
if (lean_obj_tag(v_l_3941_) == 0)
{
lean_object* v_size_3981_; 
v_size_3981_ = lean_ctor_get(v_l_3941_, 0);
lean_inc(v_size_3981_);
v___y_3973_ = v_size_3981_;
goto v___jp_3972_;
}
else
{
lean_object* v___x_3982_; 
v___x_3982_ = lean_unsigned_to_nat(0u);
v___y_3973_ = v___x_3982_;
goto v___jp_3972_;
}
v___jp_3951_:
{
lean_object* v___x_3955_; lean_object* v___x_3957_; 
v___x_3955_ = lean_nat_add(v___y_3953_, v___y_3954_);
lean_dec(v___y_3954_);
lean_dec(v___y_3953_);
lean_inc_ref(v_tree_3922_);
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 4, v_tree_3922_);
lean_ctor_set(v___x_3947_, 3, v_r_3942_);
lean_ctor_set(v___x_3947_, 2, v_v_3924_);
lean_ctor_set(v___x_3947_, 1, v_k_3923_);
lean_ctor_set(v___x_3947_, 0, v___x_3955_);
v___x_3957_ = v___x_3947_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3955_);
lean_ctor_set(v_reuseFailAlloc_3970_, 1, v_k_3923_);
lean_ctor_set(v_reuseFailAlloc_3970_, 2, v_v_3924_);
lean_ctor_set(v_reuseFailAlloc_3970_, 3, v_r_3942_);
lean_ctor_set(v_reuseFailAlloc_3970_, 4, v_tree_3922_);
v___x_3957_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
v_isSharedCheck_3964_ = !lean_is_exclusive(v_tree_3922_);
if (v_isSharedCheck_3964_ == 0)
{
lean_object* v_unused_3965_; lean_object* v_unused_3966_; lean_object* v_unused_3967_; lean_object* v_unused_3968_; lean_object* v_unused_3969_; 
v_unused_3965_ = lean_ctor_get(v_tree_3922_, 4);
lean_dec(v_unused_3965_);
v_unused_3966_ = lean_ctor_get(v_tree_3922_, 3);
lean_dec(v_unused_3966_);
v_unused_3967_ = lean_ctor_get(v_tree_3922_, 2);
lean_dec(v_unused_3967_);
v_unused_3968_ = lean_ctor_get(v_tree_3922_, 1);
lean_dec(v_unused_3968_);
v_unused_3969_ = lean_ctor_get(v_tree_3922_, 0);
lean_dec(v_unused_3969_);
v___x_3959_ = v_tree_3922_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_dec(v_tree_3922_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 4, v___x_3957_);
lean_ctor_set(v___x_3959_, 3, v___y_3952_);
lean_ctor_set(v___x_3959_, 2, v_v_3940_);
lean_ctor_set(v___x_3959_, 1, v_k_3939_);
lean_ctor_set(v___x_3959_, 0, v___x_3950_);
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v___x_3950_);
lean_ctor_set(v_reuseFailAlloc_3963_, 1, v_k_3939_);
lean_ctor_set(v_reuseFailAlloc_3963_, 2, v_v_3940_);
lean_ctor_set(v_reuseFailAlloc_3963_, 3, v___y_3952_);
lean_ctor_set(v_reuseFailAlloc_3963_, 4, v___x_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
v___jp_3972_:
{
lean_object* v___x_3974_; lean_object* v___x_3976_; 
v___x_3974_ = lean_nat_add(v___x_3971_, v___y_3973_);
lean_dec(v___y_3973_);
lean_dec(v___x_3971_);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 4, v_l_3941_);
lean_ctor_set(v___x_3919_, 3, v_l_3768_);
lean_ctor_set(v___x_3919_, 2, v_v_3767_);
lean_ctor_set(v___x_3919_, 1, v_k_3766_);
lean_ctor_set(v___x_3919_, 0, v___x_3974_);
v___x_3976_ = v___x_3919_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3974_);
lean_ctor_set(v_reuseFailAlloc_3980_, 1, v_k_3766_);
lean_ctor_set(v_reuseFailAlloc_3980_, 2, v_v_3767_);
lean_ctor_set(v_reuseFailAlloc_3980_, 3, v_l_3768_);
lean_ctor_set(v_reuseFailAlloc_3980_, 4, v_l_3941_);
v___x_3976_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
lean_object* v___x_3977_; 
v___x_3977_ = lean_nat_add(v___x_3775_, v_size_3925_);
if (lean_obj_tag(v_r_3942_) == 0)
{
lean_object* v_size_3978_; 
v_size_3978_ = lean_ctor_get(v_r_3942_, 0);
lean_inc(v_size_3978_);
v___y_3952_ = v___x_3976_;
v___y_3953_ = v___x_3977_;
v___y_3954_ = v_size_3978_;
goto v___jp_3951_;
}
else
{
lean_object* v___x_3979_; 
v___x_3979_ = lean_unsigned_to_nat(0u);
v___y_3952_ = v___x_3976_;
v___y_3953_ = v___x_3977_;
v___y_3954_ = v___x_3979_;
goto v___jp_3951_;
}
}
}
}
}
else
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3994_; 
v___x_3989_ = lean_nat_add(v___x_3775_, v_size_3765_);
lean_dec(v_size_3765_);
v___x_3990_ = lean_nat_add(v___x_3989_, v_size_3925_);
lean_dec(v___x_3989_);
v___x_3991_ = lean_nat_add(v___x_3775_, v_size_3925_);
v___x_3992_ = lean_nat_add(v___x_3991_, v_size_3938_);
lean_dec(v___x_3991_);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 4, v_tree_3922_);
lean_ctor_set(v___x_3919_, 3, v_r_3769_);
lean_ctor_set(v___x_3919_, 2, v_v_3924_);
lean_ctor_set(v___x_3919_, 1, v_k_3923_);
lean_ctor_set(v___x_3919_, 0, v___x_3992_);
v___x_3994_ = v___x_3919_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3992_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v_k_3923_);
lean_ctor_set(v_reuseFailAlloc_3998_, 2, v_v_3924_);
lean_ctor_set(v_reuseFailAlloc_3998_, 3, v_r_3769_);
lean_ctor_set(v_reuseFailAlloc_3998_, 4, v_tree_3922_);
v___x_3994_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
lean_object* v___x_3996_; 
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 4, v___x_3994_);
lean_ctor_set(v___x_3935_, 0, v___x_3990_);
v___x_3996_ = v___x_3935_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___x_3990_);
lean_ctor_set(v_reuseFailAlloc_3997_, 1, v_k_3766_);
lean_ctor_set(v_reuseFailAlloc_3997_, 2, v_v_3767_);
lean_ctor_set(v_reuseFailAlloc_3997_, 3, v_l_3768_);
lean_ctor_set(v_reuseFailAlloc_3997_, 4, v___x_3994_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3768_) == 0)
{
lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4028_; 
lean_inc_ref(v_l_3768_);
lean_inc(v_v_3767_);
lean_inc(v_k_3766_);
lean_inc(v_size_3765_);
v_isSharedCheck_4028_ = !lean_is_exclusive(v_l_3585_);
if (v_isSharedCheck_4028_ == 0)
{
lean_object* v_unused_4029_; lean_object* v_unused_4030_; lean_object* v_unused_4031_; lean_object* v_unused_4032_; lean_object* v_unused_4033_; 
v_unused_4029_ = lean_ctor_get(v_l_3585_, 4);
lean_dec(v_unused_4029_);
v_unused_4030_ = lean_ctor_get(v_l_3585_, 3);
lean_dec(v_unused_4030_);
v_unused_4031_ = lean_ctor_get(v_l_3585_, 2);
lean_dec(v_unused_4031_);
v_unused_4032_ = lean_ctor_get(v_l_3585_, 1);
lean_dec(v_unused_4032_);
v_unused_4033_ = lean_ctor_get(v_l_3585_, 0);
lean_dec(v_unused_4033_);
v___x_4006_ = v_l_3585_;
v_isShared_4007_ = v_isSharedCheck_4028_;
goto v_resetjp_4005_;
}
else
{
lean_dec(v_l_3585_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4028_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
if (lean_obj_tag(v_r_3769_) == 0)
{
lean_object* v_k_4008_; lean_object* v_v_4009_; lean_object* v_size_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4014_; 
v_k_4008_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_k_4008_);
v_v_4009_ = lean_ctor_get(v___x_3921_, 1);
lean_inc(v_v_4009_);
lean_dec_ref(v___x_3921_);
v_size_4010_ = lean_ctor_get(v_r_3769_, 0);
v___x_4011_ = lean_nat_add(v___x_3775_, v_size_3765_);
lean_dec(v_size_3765_);
v___x_4012_ = lean_nat_add(v___x_3775_, v_size_4010_);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 4, v_tree_3922_);
lean_ctor_set(v___x_3919_, 3, v_r_3769_);
lean_ctor_set(v___x_3919_, 2, v_v_4009_);
lean_ctor_set(v___x_3919_, 1, v_k_4008_);
lean_ctor_set(v___x_3919_, 0, v___x_4012_);
v___x_4014_ = v___x_3919_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v___x_4012_);
lean_ctor_set(v_reuseFailAlloc_4018_, 1, v_k_4008_);
lean_ctor_set(v_reuseFailAlloc_4018_, 2, v_v_4009_);
lean_ctor_set(v_reuseFailAlloc_4018_, 3, v_r_3769_);
lean_ctor_set(v_reuseFailAlloc_4018_, 4, v_tree_3922_);
v___x_4014_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
lean_object* v___x_4016_; 
if (v_isShared_4007_ == 0)
{
lean_ctor_set(v___x_4006_, 4, v___x_4014_);
lean_ctor_set(v___x_4006_, 0, v___x_4011_);
v___x_4016_ = v___x_4006_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v___x_4011_);
lean_ctor_set(v_reuseFailAlloc_4017_, 1, v_k_3766_);
lean_ctor_set(v_reuseFailAlloc_4017_, 2, v_v_3767_);
lean_ctor_set(v_reuseFailAlloc_4017_, 3, v_l_3768_);
lean_ctor_set(v_reuseFailAlloc_4017_, 4, v___x_4014_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
else
{
lean_object* v_k_4019_; lean_object* v_v_4020_; lean_object* v___x_4021_; lean_object* v___x_4023_; 
lean_dec(v_size_3765_);
v_k_4019_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_k_4019_);
v_v_4020_ = lean_ctor_get(v___x_3921_, 1);
lean_inc(v_v_4020_);
lean_dec_ref(v___x_3921_);
v___x_4021_ = lean_unsigned_to_nat(3u);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 4, v_r_3769_);
lean_ctor_set(v___x_3919_, 3, v_r_3769_);
lean_ctor_set(v___x_3919_, 2, v_v_4020_);
lean_ctor_set(v___x_3919_, 1, v_k_4019_);
lean_ctor_set(v___x_3919_, 0, v___x_3775_);
v___x_4023_ = v___x_3919_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_4027_, 1, v_k_4019_);
lean_ctor_set(v_reuseFailAlloc_4027_, 2, v_v_4020_);
lean_ctor_set(v_reuseFailAlloc_4027_, 3, v_r_3769_);
lean_ctor_set(v_reuseFailAlloc_4027_, 4, v_r_3769_);
v___x_4023_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
lean_object* v___x_4025_; 
if (v_isShared_4007_ == 0)
{
lean_ctor_set(v___x_4006_, 4, v___x_4023_);
lean_ctor_set(v___x_4006_, 0, v___x_4021_);
v___x_4025_ = v___x_4006_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v___x_4021_);
lean_ctor_set(v_reuseFailAlloc_4026_, 1, v_k_3766_);
lean_ctor_set(v_reuseFailAlloc_4026_, 2, v_v_3767_);
lean_ctor_set(v_reuseFailAlloc_4026_, 3, v_l_3768_);
lean_ctor_set(v_reuseFailAlloc_4026_, 4, v___x_4023_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3769_) == 0)
{
lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4058_; 
lean_inc(v_l_3768_);
lean_inc(v_v_3767_);
lean_inc(v_k_3766_);
v_isSharedCheck_4058_ = !lean_is_exclusive(v_l_3585_);
if (v_isSharedCheck_4058_ == 0)
{
lean_object* v_unused_4059_; lean_object* v_unused_4060_; lean_object* v_unused_4061_; lean_object* v_unused_4062_; lean_object* v_unused_4063_; 
v_unused_4059_ = lean_ctor_get(v_l_3585_, 4);
lean_dec(v_unused_4059_);
v_unused_4060_ = lean_ctor_get(v_l_3585_, 3);
lean_dec(v_unused_4060_);
v_unused_4061_ = lean_ctor_get(v_l_3585_, 2);
lean_dec(v_unused_4061_);
v_unused_4062_ = lean_ctor_get(v_l_3585_, 1);
lean_dec(v_unused_4062_);
v_unused_4063_ = lean_ctor_get(v_l_3585_, 0);
lean_dec(v_unused_4063_);
v___x_4035_ = v_l_3585_;
v_isShared_4036_ = v_isSharedCheck_4058_;
goto v_resetjp_4034_;
}
else
{
lean_dec(v_l_3585_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4058_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v_k_4037_; lean_object* v_v_4038_; lean_object* v_k_4039_; lean_object* v_v_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4054_; 
v_k_4037_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_k_4037_);
v_v_4038_ = lean_ctor_get(v___x_3921_, 1);
lean_inc(v_v_4038_);
lean_dec_ref(v___x_3921_);
v_k_4039_ = lean_ctor_get(v_r_3769_, 1);
v_v_4040_ = lean_ctor_get(v_r_3769_, 2);
v_isSharedCheck_4054_ = !lean_is_exclusive(v_r_3769_);
if (v_isSharedCheck_4054_ == 0)
{
lean_object* v_unused_4055_; lean_object* v_unused_4056_; lean_object* v_unused_4057_; 
v_unused_4055_ = lean_ctor_get(v_r_3769_, 4);
lean_dec(v_unused_4055_);
v_unused_4056_ = lean_ctor_get(v_r_3769_, 3);
lean_dec(v_unused_4056_);
v_unused_4057_ = lean_ctor_get(v_r_3769_, 0);
lean_dec(v_unused_4057_);
v___x_4042_ = v_r_3769_;
v_isShared_4043_ = v_isSharedCheck_4054_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_v_4040_);
lean_inc(v_k_4039_);
lean_dec(v_r_3769_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4054_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4044_; lean_object* v___x_4046_; 
v___x_4044_ = lean_unsigned_to_nat(3u);
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 4, v_l_3768_);
lean_ctor_set(v___x_4042_, 3, v_l_3768_);
lean_ctor_set(v___x_4042_, 2, v_v_3767_);
lean_ctor_set(v___x_4042_, 1, v_k_3766_);
lean_ctor_set(v___x_4042_, 0, v___x_3775_);
v___x_4046_ = v___x_4042_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_4053_, 1, v_k_3766_);
lean_ctor_set(v_reuseFailAlloc_4053_, 2, v_v_3767_);
lean_ctor_set(v_reuseFailAlloc_4053_, 3, v_l_3768_);
lean_ctor_set(v_reuseFailAlloc_4053_, 4, v_l_3768_);
v___x_4046_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
lean_object* v___x_4048_; 
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 4, v_l_3768_);
lean_ctor_set(v___x_3919_, 3, v_l_3768_);
lean_ctor_set(v___x_3919_, 2, v_v_4038_);
lean_ctor_set(v___x_3919_, 1, v_k_4037_);
lean_ctor_set(v___x_3919_, 0, v___x_3775_);
v___x_4048_ = v___x_3919_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v_k_4037_);
lean_ctor_set(v_reuseFailAlloc_4052_, 2, v_v_4038_);
lean_ctor_set(v_reuseFailAlloc_4052_, 3, v_l_3768_);
lean_ctor_set(v_reuseFailAlloc_4052_, 4, v_l_3768_);
v___x_4048_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
lean_object* v___x_4050_; 
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 4, v___x_4048_);
lean_ctor_set(v___x_4035_, 3, v___x_4046_);
lean_ctor_set(v___x_4035_, 2, v_v_4040_);
lean_ctor_set(v___x_4035_, 1, v_k_4039_);
lean_ctor_set(v___x_4035_, 0, v___x_4044_);
v___x_4050_ = v___x_4035_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v___x_4044_);
lean_ctor_set(v_reuseFailAlloc_4051_, 1, v_k_4039_);
lean_ctor_set(v_reuseFailAlloc_4051_, 2, v_v_4040_);
lean_ctor_set(v_reuseFailAlloc_4051_, 3, v___x_4046_);
lean_ctor_set(v_reuseFailAlloc_4051_, 4, v___x_4048_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
}
}
else
{
lean_object* v_k_4064_; lean_object* v_v_4065_; lean_object* v___x_4066_; lean_object* v___x_4068_; 
v_k_4064_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_k_4064_);
v_v_4065_ = lean_ctor_get(v___x_3921_, 1);
lean_inc(v_v_4065_);
lean_dec_ref(v___x_3921_);
v___x_4066_ = lean_unsigned_to_nat(2u);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 4, v_r_3769_);
lean_ctor_set(v___x_3919_, 3, v_l_3585_);
lean_ctor_set(v___x_3919_, 2, v_v_4065_);
lean_ctor_set(v___x_3919_, 1, v_k_4064_);
lean_ctor_set(v___x_3919_, 0, v___x_4066_);
v___x_4068_ = v___x_3919_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4066_);
lean_ctor_set(v_reuseFailAlloc_4069_, 1, v_k_4064_);
lean_ctor_set(v_reuseFailAlloc_4069_, 2, v_v_4065_);
lean_ctor_set(v_reuseFailAlloc_4069_, 3, v_l_3585_);
lean_ctor_set(v_reuseFailAlloc_4069_, 4, v_r_3769_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
}
}
}
else
{
return v_l_3585_;
}
}
else
{
return v_r_3586_;
}
}
default: 
{
lean_object* v_impl_4076_; lean_object* v___x_4077_; 
v_impl_4076_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(v_k_3581_, v_r_3586_);
v___x_4077_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_4076_) == 0)
{
if (lean_obj_tag(v_l_3585_) == 0)
{
lean_object* v_size_4078_; lean_object* v_size_4079_; lean_object* v_k_4080_; lean_object* v_v_4081_; lean_object* v_l_4082_; lean_object* v_r_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; uint8_t v___x_4086_; 
v_size_4078_ = lean_ctor_get(v_impl_4076_, 0);
lean_inc(v_size_4078_);
v_size_4079_ = lean_ctor_get(v_l_3585_, 0);
v_k_4080_ = lean_ctor_get(v_l_3585_, 1);
v_v_4081_ = lean_ctor_get(v_l_3585_, 2);
v_l_4082_ = lean_ctor_get(v_l_3585_, 3);
v_r_4083_ = lean_ctor_get(v_l_3585_, 4);
lean_inc(v_r_4083_);
v___x_4084_ = lean_unsigned_to_nat(3u);
v___x_4085_ = lean_nat_mul(v___x_4084_, v_size_4078_);
v___x_4086_ = lean_nat_dec_lt(v___x_4085_, v_size_4079_);
lean_dec(v___x_4085_);
if (v___x_4086_ == 0)
{
lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4090_; 
lean_dec(v_r_4083_);
v___x_4087_ = lean_nat_add(v___x_4077_, v_size_4079_);
v___x_4088_ = lean_nat_add(v___x_4087_, v_size_4078_);
lean_dec(v_size_4078_);
lean_dec(v___x_4087_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 4, v_impl_4076_);
lean_ctor_set(v___x_3588_, 0, v___x_4088_);
v___x_4090_ = v___x_3588_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4088_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_4091_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_4091_, 3, v_l_3585_);
lean_ctor_set(v_reuseFailAlloc_4091_, 4, v_impl_4076_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
else
{
lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4157_; 
lean_inc(v_l_4082_);
lean_inc(v_v_4081_);
lean_inc(v_k_4080_);
lean_inc(v_size_4079_);
v_isSharedCheck_4157_ = !lean_is_exclusive(v_l_3585_);
if (v_isSharedCheck_4157_ == 0)
{
lean_object* v_unused_4158_; lean_object* v_unused_4159_; lean_object* v_unused_4160_; lean_object* v_unused_4161_; lean_object* v_unused_4162_; 
v_unused_4158_ = lean_ctor_get(v_l_3585_, 4);
lean_dec(v_unused_4158_);
v_unused_4159_ = lean_ctor_get(v_l_3585_, 3);
lean_dec(v_unused_4159_);
v_unused_4160_ = lean_ctor_get(v_l_3585_, 2);
lean_dec(v_unused_4160_);
v_unused_4161_ = lean_ctor_get(v_l_3585_, 1);
lean_dec(v_unused_4161_);
v_unused_4162_ = lean_ctor_get(v_l_3585_, 0);
lean_dec(v_unused_4162_);
v___x_4093_ = v_l_3585_;
v_isShared_4094_ = v_isSharedCheck_4157_;
goto v_resetjp_4092_;
}
else
{
lean_dec(v_l_3585_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4157_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v_size_4095_; lean_object* v_size_4096_; lean_object* v_k_4097_; lean_object* v_v_4098_; lean_object* v_l_4099_; lean_object* v_r_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; uint8_t v___x_4103_; 
v_size_4095_ = lean_ctor_get(v_l_4082_, 0);
v_size_4096_ = lean_ctor_get(v_r_4083_, 0);
v_k_4097_ = lean_ctor_get(v_r_4083_, 1);
v_v_4098_ = lean_ctor_get(v_r_4083_, 2);
v_l_4099_ = lean_ctor_get(v_r_4083_, 3);
v_r_4100_ = lean_ctor_get(v_r_4083_, 4);
v___x_4101_ = lean_unsigned_to_nat(2u);
v___x_4102_ = lean_nat_mul(v___x_4101_, v_size_4095_);
v___x_4103_ = lean_nat_dec_lt(v_size_4096_, v___x_4102_);
lean_dec(v___x_4102_);
if (v___x_4103_ == 0)
{
lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4132_; 
lean_inc(v_r_4100_);
lean_inc(v_l_4099_);
lean_inc(v_v_4098_);
lean_inc(v_k_4097_);
v_isSharedCheck_4132_ = !lean_is_exclusive(v_r_4083_);
if (v_isSharedCheck_4132_ == 0)
{
lean_object* v_unused_4133_; lean_object* v_unused_4134_; lean_object* v_unused_4135_; lean_object* v_unused_4136_; lean_object* v_unused_4137_; 
v_unused_4133_ = lean_ctor_get(v_r_4083_, 4);
lean_dec(v_unused_4133_);
v_unused_4134_ = lean_ctor_get(v_r_4083_, 3);
lean_dec(v_unused_4134_);
v_unused_4135_ = lean_ctor_get(v_r_4083_, 2);
lean_dec(v_unused_4135_);
v_unused_4136_ = lean_ctor_get(v_r_4083_, 1);
lean_dec(v_unused_4136_);
v_unused_4137_ = lean_ctor_get(v_r_4083_, 0);
lean_dec(v_unused_4137_);
v___x_4105_ = v_r_4083_;
v_isShared_4106_ = v_isSharedCheck_4132_;
goto v_resetjp_4104_;
}
else
{
lean_dec(v_r_4083_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4132_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___x_4120_; lean_object* v___y_4122_; 
v___x_4107_ = lean_nat_add(v___x_4077_, v_size_4079_);
lean_dec(v_size_4079_);
v___x_4108_ = lean_nat_add(v___x_4107_, v_size_4078_);
lean_dec(v___x_4107_);
v___x_4120_ = lean_nat_add(v___x_4077_, v_size_4095_);
if (lean_obj_tag(v_l_4099_) == 0)
{
lean_object* v_size_4130_; 
v_size_4130_ = lean_ctor_get(v_l_4099_, 0);
lean_inc(v_size_4130_);
v___y_4122_ = v_size_4130_;
goto v___jp_4121_;
}
else
{
lean_object* v___x_4131_; 
v___x_4131_ = lean_unsigned_to_nat(0u);
v___y_4122_ = v___x_4131_;
goto v___jp_4121_;
}
v___jp_4109_:
{
lean_object* v___x_4113_; lean_object* v___x_4115_; 
v___x_4113_ = lean_nat_add(v___y_4111_, v___y_4112_);
lean_dec(v___y_4112_);
lean_dec(v___y_4111_);
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 4, v_impl_4076_);
lean_ctor_set(v___x_4105_, 3, v_r_4100_);
lean_ctor_set(v___x_4105_, 2, v_v_3584_);
lean_ctor_set(v___x_4105_, 1, v_k_3583_);
lean_ctor_set(v___x_4105_, 0, v___x_4113_);
v___x_4115_ = v___x_4105_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v___x_4113_);
lean_ctor_set(v_reuseFailAlloc_4119_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_4119_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_4119_, 3, v_r_4100_);
lean_ctor_set(v_reuseFailAlloc_4119_, 4, v_impl_4076_);
v___x_4115_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
lean_object* v___x_4117_; 
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 4, v___x_4115_);
lean_ctor_set(v___x_4093_, 3, v___y_4110_);
lean_ctor_set(v___x_4093_, 2, v_v_4098_);
lean_ctor_set(v___x_4093_, 1, v_k_4097_);
lean_ctor_set(v___x_4093_, 0, v___x_4108_);
v___x_4117_ = v___x_4093_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4108_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v_k_4097_);
lean_ctor_set(v_reuseFailAlloc_4118_, 2, v_v_4098_);
lean_ctor_set(v_reuseFailAlloc_4118_, 3, v___y_4110_);
lean_ctor_set(v_reuseFailAlloc_4118_, 4, v___x_4115_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
v___jp_4121_:
{
lean_object* v___x_4123_; lean_object* v___x_4125_; 
v___x_4123_ = lean_nat_add(v___x_4120_, v___y_4122_);
lean_dec(v___y_4122_);
lean_dec(v___x_4120_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 4, v_l_4099_);
lean_ctor_set(v___x_3588_, 3, v_l_4082_);
lean_ctor_set(v___x_3588_, 2, v_v_4081_);
lean_ctor_set(v___x_3588_, 1, v_k_4080_);
lean_ctor_set(v___x_3588_, 0, v___x_4123_);
v___x_4125_ = v___x_3588_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v___x_4123_);
lean_ctor_set(v_reuseFailAlloc_4129_, 1, v_k_4080_);
lean_ctor_set(v_reuseFailAlloc_4129_, 2, v_v_4081_);
lean_ctor_set(v_reuseFailAlloc_4129_, 3, v_l_4082_);
lean_ctor_set(v_reuseFailAlloc_4129_, 4, v_l_4099_);
v___x_4125_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
lean_object* v___x_4126_; 
v___x_4126_ = lean_nat_add(v___x_4077_, v_size_4078_);
lean_dec(v_size_4078_);
if (lean_obj_tag(v_r_4100_) == 0)
{
lean_object* v_size_4127_; 
v_size_4127_ = lean_ctor_get(v_r_4100_, 0);
lean_inc(v_size_4127_);
v___y_4110_ = v___x_4125_;
v___y_4111_ = v___x_4126_;
v___y_4112_ = v_size_4127_;
goto v___jp_4109_;
}
else
{
lean_object* v___x_4128_; 
v___x_4128_ = lean_unsigned_to_nat(0u);
v___y_4110_ = v___x_4125_;
v___y_4111_ = v___x_4126_;
v___y_4112_ = v___x_4128_;
goto v___jp_4109_;
}
}
}
}
}
else
{
lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4143_; 
lean_del_object(v___x_3588_);
v___x_4138_ = lean_nat_add(v___x_4077_, v_size_4079_);
lean_dec(v_size_4079_);
v___x_4139_ = lean_nat_add(v___x_4138_, v_size_4078_);
lean_dec(v___x_4138_);
v___x_4140_ = lean_nat_add(v___x_4077_, v_size_4078_);
lean_dec(v_size_4078_);
v___x_4141_ = lean_nat_add(v___x_4140_, v_size_4096_);
lean_dec(v___x_4140_);
lean_inc_ref(v_impl_4076_);
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 4, v_impl_4076_);
lean_ctor_set(v___x_4093_, 3, v_r_4083_);
lean_ctor_set(v___x_4093_, 2, v_v_3584_);
lean_ctor_set(v___x_4093_, 1, v_k_3583_);
lean_ctor_set(v___x_4093_, 0, v___x_4141_);
v___x_4143_ = v___x_4093_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v___x_4141_);
lean_ctor_set(v_reuseFailAlloc_4156_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_4156_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_4156_, 3, v_r_4083_);
lean_ctor_set(v_reuseFailAlloc_4156_, 4, v_impl_4076_);
v___x_4143_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
v_isSharedCheck_4150_ = !lean_is_exclusive(v_impl_4076_);
if (v_isSharedCheck_4150_ == 0)
{
lean_object* v_unused_4151_; lean_object* v_unused_4152_; lean_object* v_unused_4153_; lean_object* v_unused_4154_; lean_object* v_unused_4155_; 
v_unused_4151_ = lean_ctor_get(v_impl_4076_, 4);
lean_dec(v_unused_4151_);
v_unused_4152_ = lean_ctor_get(v_impl_4076_, 3);
lean_dec(v_unused_4152_);
v_unused_4153_ = lean_ctor_get(v_impl_4076_, 2);
lean_dec(v_unused_4153_);
v_unused_4154_ = lean_ctor_get(v_impl_4076_, 1);
lean_dec(v_unused_4154_);
v_unused_4155_ = lean_ctor_get(v_impl_4076_, 0);
lean_dec(v_unused_4155_);
v___x_4145_ = v_impl_4076_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_dec(v_impl_4076_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
lean_ctor_set(v___x_4145_, 4, v___x_4143_);
lean_ctor_set(v___x_4145_, 3, v_l_4082_);
lean_ctor_set(v___x_4145_, 2, v_v_4081_);
lean_ctor_set(v___x_4145_, 1, v_k_4080_);
lean_ctor_set(v___x_4145_, 0, v___x_4139_);
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4139_);
lean_ctor_set(v_reuseFailAlloc_4149_, 1, v_k_4080_);
lean_ctor_set(v_reuseFailAlloc_4149_, 2, v_v_4081_);
lean_ctor_set(v_reuseFailAlloc_4149_, 3, v_l_4082_);
lean_ctor_set(v_reuseFailAlloc_4149_, 4, v___x_4143_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_4163_; lean_object* v___x_4164_; lean_object* v___x_4166_; 
v_size_4163_ = lean_ctor_get(v_impl_4076_, 0);
lean_inc(v_size_4163_);
v___x_4164_ = lean_nat_add(v___x_4077_, v_size_4163_);
lean_dec(v_size_4163_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 4, v_impl_4076_);
lean_ctor_set(v___x_3588_, 0, v___x_4164_);
v___x_4166_ = v___x_3588_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v___x_4164_);
lean_ctor_set(v_reuseFailAlloc_4167_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_4167_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_4167_, 3, v_l_3585_);
lean_ctor_set(v_reuseFailAlloc_4167_, 4, v_impl_4076_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
else
{
if (lean_obj_tag(v_l_3585_) == 0)
{
lean_object* v_l_4168_; 
v_l_4168_ = lean_ctor_get(v_l_3585_, 3);
if (lean_obj_tag(v_l_4168_) == 0)
{
lean_object* v_r_4169_; 
lean_inc_ref(v_l_4168_);
v_r_4169_ = lean_ctor_get(v_l_3585_, 4);
lean_inc(v_r_4169_);
if (lean_obj_tag(v_r_4169_) == 0)
{
lean_object* v_size_4170_; lean_object* v_k_4171_; lean_object* v_v_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4185_; 
v_size_4170_ = lean_ctor_get(v_l_3585_, 0);
v_k_4171_ = lean_ctor_get(v_l_3585_, 1);
v_v_4172_ = lean_ctor_get(v_l_3585_, 2);
v_isSharedCheck_4185_ = !lean_is_exclusive(v_l_3585_);
if (v_isSharedCheck_4185_ == 0)
{
lean_object* v_unused_4186_; lean_object* v_unused_4187_; 
v_unused_4186_ = lean_ctor_get(v_l_3585_, 4);
lean_dec(v_unused_4186_);
v_unused_4187_ = lean_ctor_get(v_l_3585_, 3);
lean_dec(v_unused_4187_);
v___x_4174_ = v_l_3585_;
v_isShared_4175_ = v_isSharedCheck_4185_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_v_4172_);
lean_inc(v_k_4171_);
lean_inc(v_size_4170_);
lean_dec(v_l_3585_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4185_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v_size_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4180_; 
v_size_4176_ = lean_ctor_get(v_r_4169_, 0);
v___x_4177_ = lean_nat_add(v___x_4077_, v_size_4170_);
lean_dec(v_size_4170_);
v___x_4178_ = lean_nat_add(v___x_4077_, v_size_4176_);
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 4, v_impl_4076_);
lean_ctor_set(v___x_4174_, 3, v_r_4169_);
lean_ctor_set(v___x_4174_, 2, v_v_3584_);
lean_ctor_set(v___x_4174_, 1, v_k_3583_);
lean_ctor_set(v___x_4174_, 0, v___x_4178_);
v___x_4180_ = v___x_4174_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4178_);
lean_ctor_set(v_reuseFailAlloc_4184_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_4184_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_4184_, 3, v_r_4169_);
lean_ctor_set(v_reuseFailAlloc_4184_, 4, v_impl_4076_);
v___x_4180_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
lean_object* v___x_4182_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 4, v___x_4180_);
lean_ctor_set(v___x_3588_, 3, v_l_4168_);
lean_ctor_set(v___x_3588_, 2, v_v_4172_);
lean_ctor_set(v___x_3588_, 1, v_k_4171_);
lean_ctor_set(v___x_3588_, 0, v___x_4177_);
v___x_4182_ = v___x_3588_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v___x_4177_);
lean_ctor_set(v_reuseFailAlloc_4183_, 1, v_k_4171_);
lean_ctor_set(v_reuseFailAlloc_4183_, 2, v_v_4172_);
lean_ctor_set(v_reuseFailAlloc_4183_, 3, v_l_4168_);
lean_ctor_set(v_reuseFailAlloc_4183_, 4, v___x_4180_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
else
{
lean_object* v_k_4188_; lean_object* v_v_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4200_; 
v_k_4188_ = lean_ctor_get(v_l_3585_, 1);
v_v_4189_ = lean_ctor_get(v_l_3585_, 2);
v_isSharedCheck_4200_ = !lean_is_exclusive(v_l_3585_);
if (v_isSharedCheck_4200_ == 0)
{
lean_object* v_unused_4201_; lean_object* v_unused_4202_; lean_object* v_unused_4203_; 
v_unused_4201_ = lean_ctor_get(v_l_3585_, 4);
lean_dec(v_unused_4201_);
v_unused_4202_ = lean_ctor_get(v_l_3585_, 3);
lean_dec(v_unused_4202_);
v_unused_4203_ = lean_ctor_get(v_l_3585_, 0);
lean_dec(v_unused_4203_);
v___x_4191_ = v_l_3585_;
v_isShared_4192_ = v_isSharedCheck_4200_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_v_4189_);
lean_inc(v_k_4188_);
lean_dec(v_l_3585_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4200_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4193_; lean_object* v___x_4195_; 
v___x_4193_ = lean_unsigned_to_nat(3u);
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 3, v_r_4169_);
lean_ctor_set(v___x_4191_, 2, v_v_3584_);
lean_ctor_set(v___x_4191_, 1, v_k_3583_);
lean_ctor_set(v___x_4191_, 0, v___x_4077_);
v___x_4195_ = v___x_4191_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v___x_4077_);
lean_ctor_set(v_reuseFailAlloc_4199_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_4199_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_4199_, 3, v_r_4169_);
lean_ctor_set(v_reuseFailAlloc_4199_, 4, v_r_4169_);
v___x_4195_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
lean_object* v___x_4197_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 4, v___x_4195_);
lean_ctor_set(v___x_3588_, 3, v_l_4168_);
lean_ctor_set(v___x_3588_, 2, v_v_4189_);
lean_ctor_set(v___x_3588_, 1, v_k_4188_);
lean_ctor_set(v___x_3588_, 0, v___x_4193_);
v___x_4197_ = v___x_3588_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v___x_4193_);
lean_ctor_set(v_reuseFailAlloc_4198_, 1, v_k_4188_);
lean_ctor_set(v_reuseFailAlloc_4198_, 2, v_v_4189_);
lean_ctor_set(v_reuseFailAlloc_4198_, 3, v_l_4168_);
lean_ctor_set(v_reuseFailAlloc_4198_, 4, v___x_4195_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
}
else
{
lean_object* v_r_4204_; 
v_r_4204_ = lean_ctor_get(v_l_3585_, 4);
lean_inc(v_r_4204_);
if (lean_obj_tag(v_r_4204_) == 0)
{
lean_object* v_k_4205_; lean_object* v_v_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4229_; 
lean_inc(v_l_4168_);
v_k_4205_ = lean_ctor_get(v_l_3585_, 1);
v_v_4206_ = lean_ctor_get(v_l_3585_, 2);
v_isSharedCheck_4229_ = !lean_is_exclusive(v_l_3585_);
if (v_isSharedCheck_4229_ == 0)
{
lean_object* v_unused_4230_; lean_object* v_unused_4231_; lean_object* v_unused_4232_; 
v_unused_4230_ = lean_ctor_get(v_l_3585_, 4);
lean_dec(v_unused_4230_);
v_unused_4231_ = lean_ctor_get(v_l_3585_, 3);
lean_dec(v_unused_4231_);
v_unused_4232_ = lean_ctor_get(v_l_3585_, 0);
lean_dec(v_unused_4232_);
v___x_4208_ = v_l_3585_;
v_isShared_4209_ = v_isSharedCheck_4229_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_v_4206_);
lean_inc(v_k_4205_);
lean_dec(v_l_3585_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4229_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v_k_4210_; lean_object* v_v_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4225_; 
v_k_4210_ = lean_ctor_get(v_r_4204_, 1);
v_v_4211_ = lean_ctor_get(v_r_4204_, 2);
v_isSharedCheck_4225_ = !lean_is_exclusive(v_r_4204_);
if (v_isSharedCheck_4225_ == 0)
{
lean_object* v_unused_4226_; lean_object* v_unused_4227_; lean_object* v_unused_4228_; 
v_unused_4226_ = lean_ctor_get(v_r_4204_, 4);
lean_dec(v_unused_4226_);
v_unused_4227_ = lean_ctor_get(v_r_4204_, 3);
lean_dec(v_unused_4227_);
v_unused_4228_ = lean_ctor_get(v_r_4204_, 0);
lean_dec(v_unused_4228_);
v___x_4213_ = v_r_4204_;
v_isShared_4214_ = v_isSharedCheck_4225_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_v_4211_);
lean_inc(v_k_4210_);
lean_dec(v_r_4204_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4225_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4215_; lean_object* v___x_4217_; 
v___x_4215_ = lean_unsigned_to_nat(3u);
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 4, v_l_4168_);
lean_ctor_set(v___x_4213_, 3, v_l_4168_);
lean_ctor_set(v___x_4213_, 2, v_v_4206_);
lean_ctor_set(v___x_4213_, 1, v_k_4205_);
lean_ctor_set(v___x_4213_, 0, v___x_4077_);
v___x_4217_ = v___x_4213_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4077_);
lean_ctor_set(v_reuseFailAlloc_4224_, 1, v_k_4205_);
lean_ctor_set(v_reuseFailAlloc_4224_, 2, v_v_4206_);
lean_ctor_set(v_reuseFailAlloc_4224_, 3, v_l_4168_);
lean_ctor_set(v_reuseFailAlloc_4224_, 4, v_l_4168_);
v___x_4217_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
lean_object* v___x_4219_; 
if (v_isShared_4209_ == 0)
{
lean_ctor_set(v___x_4208_, 4, v_l_4168_);
lean_ctor_set(v___x_4208_, 2, v_v_3584_);
lean_ctor_set(v___x_4208_, 1, v_k_3583_);
lean_ctor_set(v___x_4208_, 0, v___x_4077_);
v___x_4219_ = v___x_4208_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4077_);
lean_ctor_set(v_reuseFailAlloc_4223_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_4223_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_4223_, 3, v_l_4168_);
lean_ctor_set(v_reuseFailAlloc_4223_, 4, v_l_4168_);
v___x_4219_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
lean_object* v___x_4221_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 4, v___x_4219_);
lean_ctor_set(v___x_3588_, 3, v___x_4217_);
lean_ctor_set(v___x_3588_, 2, v_v_4211_);
lean_ctor_set(v___x_3588_, 1, v_k_4210_);
lean_ctor_set(v___x_3588_, 0, v___x_4215_);
v___x_4221_ = v___x_3588_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v___x_4215_);
lean_ctor_set(v_reuseFailAlloc_4222_, 1, v_k_4210_);
lean_ctor_set(v_reuseFailAlloc_4222_, 2, v_v_4211_);
lean_ctor_set(v_reuseFailAlloc_4222_, 3, v___x_4217_);
lean_ctor_set(v_reuseFailAlloc_4222_, 4, v___x_4219_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
}
}
}
else
{
lean_object* v___x_4233_; lean_object* v___x_4235_; 
v___x_4233_ = lean_unsigned_to_nat(2u);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 4, v_r_4204_);
lean_ctor_set(v___x_3588_, 0, v___x_4233_);
v___x_4235_ = v___x_3588_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___x_4233_);
lean_ctor_set(v_reuseFailAlloc_4236_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_4236_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_4236_, 3, v_l_3585_);
lean_ctor_set(v_reuseFailAlloc_4236_, 4, v_r_4204_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
}
else
{
lean_object* v___x_4238_; 
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 4, v_l_3585_);
lean_ctor_set(v___x_3588_, 0, v___x_4077_);
v___x_4238_ = v___x_3588_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v___x_4077_);
lean_ctor_set(v_reuseFailAlloc_4239_, 1, v_k_3583_);
lean_ctor_set(v_reuseFailAlloc_4239_, 2, v_v_3584_);
lean_ctor_set(v_reuseFailAlloc_4239_, 3, v_l_3585_);
lean_ctor_set(v_reuseFailAlloc_4239_, 4, v_l_3585_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
}
}
}
else
{
return v_t_3582_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg___boxed(lean_object* v_k_4242_, lean_object* v_t_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(v_k_4242_, v_t_4243_);
lean_dec(v_k_4242_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1(lean_object* v_init_4245_, lean_object* v_x_4246_){
_start:
{
if (lean_obj_tag(v_x_4246_) == 0)
{
lean_object* v_k_4247_; lean_object* v_l_4248_; lean_object* v_r_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; 
v_k_4247_ = lean_ctor_get(v_x_4246_, 1);
v_l_4248_ = lean_ctor_get(v_x_4246_, 3);
v_r_4249_ = lean_ctor_get(v_x_4246_, 4);
v___x_4250_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1(v_init_4245_, v_l_4248_);
v___x_4251_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(v_k_4247_, v___x_4250_);
v_init_4245_ = v___x_4251_;
v_x_4246_ = v_r_4249_;
goto _start;
}
else
{
return v_init_4245_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1___boxed(lean_object* v_init_4253_, lean_object* v_x_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1(v_init_4253_, v_x_4254_);
lean_dec(v_x_4254_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNon(lean_object* v_names_4256_, lean_object* v_maxSuggestions_4257_, double v_depthFactor_4258_, double v_frequencyWeight_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_){
_start:
{
lean_object* v___x_4265_; lean_object* v_env_4266_; lean_object* v___x_4267_; lean_object* v_toEnvExtension_4268_; lean_object* v_asyncMode_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v___x_4265_ = lean_st_ref_get(v_a_4263_);
v_env_4266_ = lean_ctor_get(v___x_4265_, 0);
lean_inc_ref(v_env_4266_);
lean_dec(v___x_4265_);
v___x_4267_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerDenyListExt;
v_toEnvExtension_4268_ = lean_ctor_get(v___x_4267_, 0);
v_asyncMode_4269_ = lean_ctor_get(v_toEnvExtension_4268_, 2);
v___x_4270_ = lean_box(1);
v___x_4271_ = lean_box(0);
v___x_4272_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_4270_, v___x_4267_, v_env_4266_, v_asyncMode_4269_, v___x_4271_);
v___x_4273_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1(v_names_4256_, v___x_4272_);
v___x_4274_ = lean_box(0);
v___x_4275_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go_spec__6(v___x_4274_, v___x_4273_);
v___x_4276_ = l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg(v___x_4275_, v___x_4274_, v_a_4263_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_object* v_a_4277_; lean_object* v___f_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v_a_4277_ = lean_ctor_get(v___x_4276_, 0);
lean_inc(v_a_4277_);
lean_dec_ref(v___x_4276_);
v___f_4278_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_instOrdProdFloatName__lean___closed__0));
v___x_4279_ = l_Std_TreeSet_ofList___redArg(v_a_4277_, v___f_4278_);
v___x_4280_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_triggerSymbols_spec__1___closed__0));
v___x_4281_ = l___private_Lean_LibrarySuggestions_SineQuaNon_0__Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_go(v_maxSuggestions_4257_, v_depthFactor_4258_, v_frequencyWeight_4259_, v___x_4272_, v___x_4273_, v___x_4279_, v___x_4280_, v___x_4270_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_);
lean_dec(v___x_4272_);
if (lean_obj_tag(v___x_4281_) == 0)
{
lean_object* v_a_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4292_; 
v_a_4282_ = lean_ctor_get(v___x_4281_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4281_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4284_ = v___x_4281_;
v_isShared_4285_ = v_isSharedCheck_4292_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_a_4282_);
lean_dec(v___x_4281_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4292_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
size_t v_sz_4286_; size_t v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4290_; 
v_sz_4286_ = lean_array_size(v_a_4282_);
v___x_4287_ = ((size_t)0ULL);
v___x_4288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__3(v_sz_4286_, v___x_4287_, v_a_4282_);
if (v_isShared_4285_ == 0)
{
lean_ctor_set(v___x_4284_, 0, v___x_4288_);
v___x_4290_ = v___x_4284_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v___x_4288_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
v_a_4293_ = lean_ctor_get(v___x_4281_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4281_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_4281_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4281_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
if (v_isShared_4296_ == 0)
{
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4293_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
}
else
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4308_; 
lean_dec(v___x_4273_);
lean_dec(v___x_4272_);
v_a_4301_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4303_ = v___x_4276_;
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4276_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4306_; 
if (v_isShared_4304_ == 0)
{
v___x_4306_ = v___x_4303_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4301_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNon___boxed(lean_object* v_names_4309_, lean_object* v_maxSuggestions_4310_, lean_object* v_depthFactor_4311_, lean_object* v_frequencyWeight_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_){
_start:
{
double v_depthFactor_boxed_4318_; double v_frequencyWeight_boxed_4319_; lean_object* v_res_4320_; 
v_depthFactor_boxed_4318_ = lean_unbox_float(v_depthFactor_4311_);
lean_dec_ref(v_depthFactor_4311_);
v_frequencyWeight_boxed_4319_ = lean_unbox_float(v_frequencyWeight_4312_);
lean_dec_ref(v_frequencyWeight_4312_);
v_res_4320_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNon(v_names_4309_, v_maxSuggestions_4310_, v_depthFactor_boxed_4318_, v_frequencyWeight_boxed_4319_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_);
lean_dec(v_a_4316_);
lean_dec_ref(v_a_4315_);
lean_dec(v_a_4314_);
lean_dec_ref(v_a_4313_);
lean_dec(v_maxSuggestions_4310_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0(lean_object* v_00_u03b2_4321_, lean_object* v_k_4322_, lean_object* v_t_4323_, lean_object* v_h_4324_){
_start:
{
lean_object* v___x_4325_; 
v___x_4325_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___redArg(v_k_4322_, v_t_4323_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0___boxed(lean_object* v_00_u03b2_4326_, lean_object* v_k_4327_, lean_object* v_t_4328_, lean_object* v_h_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__0(v_00_u03b2_4326_, v_k_4327_, v_t_4328_, v_h_4329_);
lean_dec(v_k_4327_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1(lean_object* v_init_4331_, lean_object* v_t_4332_){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1_spec__1(v_init_4331_, v_t_4332_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1___boxed(lean_object* v_init_4334_, lean_object* v_t_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__1(v_init_4334_, v_t_4335_);
lean_dec(v_t_4335_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2(lean_object* v_x_4337_, lean_object* v_x_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_){
_start:
{
lean_object* v___x_4344_; 
v___x_4344_ = l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg(v_x_4337_, v_x_4338_, v___y_4342_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___boxed(lean_object* v_x_4345_, lean_object* v_x_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2(v_x_4345_, v_x_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_sineQuaNonSelector(double v_depthFactor_4353_, lean_object* v_g_4354_, lean_object* v_config_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_){
_start:
{
lean_object* v___x_4361_; 
v___x_4361_ = l_Lean_MVarId_getRelevantConstants(v_g_4354_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4362_; lean_object* v_maxSuggestions_4363_; double v___x_4364_; lean_object* v___x_4365_; 
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_a_4362_);
lean_dec_ref(v___x_4361_);
v_maxSuggestions_4363_ = lean_ctor_get(v_config_4355_, 0);
lean_inc(v_maxSuggestions_4363_);
lean_dec_ref(v_config_4355_);
v___x_4364_ = lean_float_once(&l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0, &l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0_once, _init_l_List_mapM_loop___at___00Lean_LibrarySuggestions_SineQuaNon_sineQuaNon_spec__2___redArg___closed__0);
v___x_4365_ = l_Lean_LibrarySuggestions_SineQuaNon_sineQuaNon(v_a_4362_, v_maxSuggestions_4363_, v_depthFactor_4353_, v___x_4364_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4375_; 
v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4368_ = v___x_4365_;
v_isShared_4369_ = v_isSharedCheck_4375_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4365_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4375_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4373_; 
v___x_4370_ = lean_unsigned_to_nat(0u);
v___x_4371_ = l_Array_extract___redArg(v_a_4366_, v___x_4370_, v_maxSuggestions_4363_);
lean_dec(v_a_4366_);
if (v_isShared_4369_ == 0)
{
lean_ctor_set(v___x_4368_, 0, v___x_4371_);
v___x_4373_ = v___x_4368_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v___x_4371_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
else
{
lean_dec(v_maxSuggestions_4363_);
return v___x_4365_;
}
}
else
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4383_; 
lean_dec_ref(v_config_4355_);
v_a_4376_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4378_ = v___x_4361_;
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___x_4361_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4381_; 
if (v_isShared_4379_ == 0)
{
v___x_4381_ = v___x_4378_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4376_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_sineQuaNonSelector___boxed(lean_object* v_depthFactor_4384_, lean_object* v_g_4385_, lean_object* v_config_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_){
_start:
{
double v_depthFactor_boxed_4392_; lean_object* v_res_4393_; 
v_depthFactor_boxed_4392_ = lean_unbox_float(v_depthFactor_4384_);
lean_dec_ref(v_depthFactor_4384_);
v_res_4393_ = l_Lean_LibrarySuggestions_sineQuaNonSelector(v_depthFactor_boxed_4392_, v_g_4385_, v_config_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_);
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
lean_dec(v_a_4388_);
lean_dec_ref(v_a_4387_);
return v_res_4393_;
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
res = l_Lean_LibrarySuggestions_SineQuaNon_initFn_00___x40_Lean_LibrarySuggestions_SineQuaNon_1269941458____hygCtx___hyg_2_();
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
