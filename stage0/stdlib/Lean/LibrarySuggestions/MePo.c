// Lean compiler output
// Module: Lean.LibrarySuggestions.MePo
// Imports: public import Lean.LibrarySuggestions.Basic import Lean.LibrarySuggestions.SymbolFrequency
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
double lean_float_of_nat(lean_object*);
double lean_float_add(double, double);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
lean_object* lean_nat_log2(lean_object*);
double lean_float_div(double, double);
extern lean_object* l_Lean_NameSet_empty;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_float_to_string(double);
lean_object* l_Lean_MessageData_paren(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
uint8_t l_Lean_LibrarySuggestions_isDeniedPremise(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_wasOriginallyTheorem(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Expr_getUsedConstantsAsSet(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
double lean_float_sub(double, double);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_NameSet_append(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_float_decLe(double, double);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_MVarId_getRelevantConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(lean_object*);
static const lean_string_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__0_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mepo"};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__0_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__0_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__1_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__0_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(179, 111, 138, 7, 148, 116, 40, 181)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__1_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__1_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__2_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__2_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__2_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__3_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__2_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__3_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__3_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__4_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__4_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__4_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__5_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__3_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__4_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__5_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__5_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__6_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "LibrarySuggestions"};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__6_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__6_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__7_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__5_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__6_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 41, 69, 6, 132, 216, 128, 143)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__7_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__7_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__8_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "MePo"};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__8_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__8_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__9_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__7_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__8_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(44, 93, 253, 244, 82, 82, 224, 66)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__9_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__9_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__10_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__9_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(173, 144, 138, 243, 34, 175, 73, 217)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__10_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__10_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__11_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__10_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__4_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 51, 218, 59, 117, 164, 44, 203)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__11_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__11_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__12_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__11_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__6_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(191, 98, 30, 100, 123, 141, 193, 113)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__12_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__12_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__13_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__12_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__8_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(206, 200, 158, 91, 84, 11, 45, 165)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__13_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__13_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__14_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__14_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__14_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__15_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__13_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__14_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 120, 229, 253, 111, 58, 55, 73)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__15_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__15_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__16_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__16_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__16_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__17_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__15_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__16_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 70, 240, 65, 73, 172, 232, 127)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__17_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__17_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__18_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__17_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__4_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 42, 1, 245, 170, 112, 202, 199)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__18_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__18_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__19_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__18_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__6_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 33, 101, 235, 243, 23, 74, 128)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__19_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__19_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__20_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__19_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__8_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(97, 33, 249, 189, 249, 89, 115, 169)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__20_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__20_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__21_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__20_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1610293474) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(62, 105, 250, 11, 65, 96, 97, 36)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__21_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__21_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__22_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__22_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__22_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__23_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__21_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__22_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 109, 63, 205, 224, 99, 21, 127)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__23_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__23_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__24_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__24_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__24_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__25_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__23_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__24_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(129, 4, 80, 108, 110, 218, 210, 56)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__25_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__25_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__26_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__25_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(28, 228, 64, 165, 223, 190, 28, 44)}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__26_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__26_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT double l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1_spec__2(lean_object*, double, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0;
LEAN_EXPORT double l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT double l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1(lean_object*, double, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__0;
static lean_once_cell_t l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__1;
LEAN_EXPORT double l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___boxed(lean_object*);
LEAN_EXPORT double l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT double l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0___closed__0;
LEAN_EXPORT double l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___closed__0 = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___closed__0_value;
LEAN_EXPORT double l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__0_value;
static const lean_ctor_object l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__0_value)}};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__1_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__2;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__3;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__2(double, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___closed__0_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Accepted "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__3;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__4_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Current relevant set: "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__6 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__6_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__7;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1(lean_object*, lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__1_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Considering candidates with threshold "};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__1_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg(lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__19___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___closed__0 = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___closed__0_value;
static const lean_array_object l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___closed__1 = (const lean_object*)&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo(lean_object*, lean_object*, lean_object*, lean_object*, double, double, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12(lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_mepoSelector___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_mepoSelector___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_mepoSelector___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_mepoSelector___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_mepoSelector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_mepoSelector___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_mepoSelector___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_mepoSelector(uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_mepoSelector___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_64_; uint8_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_64_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__1_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_));
v___x_65_ = 0;
v___x_66_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__26_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_));
v___x_67_ = l_Lean_registerTraceClass(v___x_64_, v___x_65_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2____boxed(lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_();
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0_spec__0(lean_object* v_candidate_70_, lean_object* v_init_71_, lean_object* v_x_72_){
_start:
{
if (lean_obj_tag(v_x_72_) == 0)
{
lean_object* v_k_73_; lean_object* v_l_74_; lean_object* v_r_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v_k_73_ = lean_ctor_get(v_x_72_, 1);
lean_inc(v_k_73_);
v_l_74_ = lean_ctor_get(v_x_72_, 3);
lean_inc(v_l_74_);
v_r_75_ = lean_ctor_get(v_x_72_, 4);
lean_inc(v_r_75_);
lean_dec_ref_known(v_x_72_, 5);
v___x_76_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0_spec__0(v_candidate_70_, v_init_71_, v_l_74_);
v___x_77_ = l_Lean_NameSet_contains(v_candidate_70_, v_k_73_);
if (v___x_77_ == 0)
{
lean_dec(v_k_73_);
v_init_71_ = v___x_76_;
v_x_72_ = v_r_75_;
goto _start;
}
else
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_NameSet_insert(v___x_76_, v_k_73_);
v_init_71_ = v___x_79_;
v_x_72_ = v_r_75_;
goto _start;
}
}
else
{
return v_init_71_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0_spec__0___boxed(lean_object* v_candidate_81_, lean_object* v_init_82_, lean_object* v_x_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0_spec__0(v_candidate_81_, v_init_82_, v_x_83_);
lean_dec(v_candidate_81_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___redArg(lean_object* v_k_85_, lean_object* v_t_86_){
_start:
{
if (lean_obj_tag(v_t_86_) == 0)
{
lean_object* v_k_87_; lean_object* v_v_88_; lean_object* v_l_89_; lean_object* v_r_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_744_; 
v_k_87_ = lean_ctor_get(v_t_86_, 1);
v_v_88_ = lean_ctor_get(v_t_86_, 2);
v_l_89_ = lean_ctor_get(v_t_86_, 3);
v_r_90_ = lean_ctor_get(v_t_86_, 4);
v_isSharedCheck_744_ = !lean_is_exclusive(v_t_86_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v_t_86_, 0);
lean_dec(v_unused_745_);
v___x_92_ = v_t_86_;
v_isShared_93_ = v_isSharedCheck_744_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_r_90_);
lean_inc(v_l_89_);
lean_inc(v_v_88_);
lean_inc(v_k_87_);
lean_dec(v_t_86_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_744_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
uint8_t v___x_94_; 
v___x_94_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_85_, v_k_87_);
switch(v___x_94_)
{
case 0:
{
lean_object* v_impl_95_; lean_object* v___x_96_; 
v_impl_95_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___redArg(v_k_85_, v_l_89_);
v___x_96_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_95_) == 0)
{
if (lean_obj_tag(v_r_90_) == 0)
{
lean_object* v_size_97_; lean_object* v_size_98_; lean_object* v_k_99_; lean_object* v_v_100_; lean_object* v_l_101_; lean_object* v_r_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_size_97_ = lean_ctor_get(v_impl_95_, 0);
lean_inc(v_size_97_);
v_size_98_ = lean_ctor_get(v_r_90_, 0);
v_k_99_ = lean_ctor_get(v_r_90_, 1);
v_v_100_ = lean_ctor_get(v_r_90_, 2);
v_l_101_ = lean_ctor_get(v_r_90_, 3);
lean_inc(v_l_101_);
v_r_102_ = lean_ctor_get(v_r_90_, 4);
v___x_103_ = lean_unsigned_to_nat(3u);
v___x_104_ = lean_nat_mul(v___x_103_, v_size_97_);
v___x_105_ = lean_nat_dec_lt(v___x_104_, v_size_98_);
lean_dec(v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
lean_dec(v_l_101_);
v___x_106_ = lean_nat_add(v___x_96_, v_size_97_);
lean_dec(v_size_97_);
v___x_107_ = lean_nat_add(v___x_106_, v_size_98_);
lean_dec(v___x_106_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 3, v_impl_95_);
lean_ctor_set(v___x_92_, 0, v___x_107_);
v___x_109_ = v___x_92_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_110_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_110_, 3, v_impl_95_);
lean_ctor_set(v_reuseFailAlloc_110_, 4, v_r_90_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
else
{
lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_174_; 
lean_inc(v_r_102_);
lean_inc(v_v_100_);
lean_inc(v_k_99_);
lean_inc(v_size_98_);
v_isSharedCheck_174_ = !lean_is_exclusive(v_r_90_);
if (v_isSharedCheck_174_ == 0)
{
lean_object* v_unused_175_; lean_object* v_unused_176_; lean_object* v_unused_177_; lean_object* v_unused_178_; lean_object* v_unused_179_; 
v_unused_175_ = lean_ctor_get(v_r_90_, 4);
lean_dec(v_unused_175_);
v_unused_176_ = lean_ctor_get(v_r_90_, 3);
lean_dec(v_unused_176_);
v_unused_177_ = lean_ctor_get(v_r_90_, 2);
lean_dec(v_unused_177_);
v_unused_178_ = lean_ctor_get(v_r_90_, 1);
lean_dec(v_unused_178_);
v_unused_179_ = lean_ctor_get(v_r_90_, 0);
lean_dec(v_unused_179_);
v___x_112_ = v_r_90_;
v_isShared_113_ = v_isSharedCheck_174_;
goto v_resetjp_111_;
}
else
{
lean_dec(v_r_90_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_174_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_size_114_; lean_object* v_k_115_; lean_object* v_v_116_; lean_object* v_l_117_; lean_object* v_r_118_; lean_object* v_size_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v_size_114_ = lean_ctor_get(v_l_101_, 0);
v_k_115_ = lean_ctor_get(v_l_101_, 1);
v_v_116_ = lean_ctor_get(v_l_101_, 2);
v_l_117_ = lean_ctor_get(v_l_101_, 3);
v_r_118_ = lean_ctor_get(v_l_101_, 4);
v_size_119_ = lean_ctor_get(v_r_102_, 0);
v___x_120_ = lean_unsigned_to_nat(2u);
v___x_121_ = lean_nat_mul(v___x_120_, v_size_119_);
v___x_122_ = lean_nat_dec_lt(v_size_114_, v___x_121_);
lean_dec(v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_150_; 
lean_inc(v_r_118_);
lean_inc(v_l_117_);
lean_inc(v_v_116_);
lean_inc(v_k_115_);
v_isSharedCheck_150_ = !lean_is_exclusive(v_l_101_);
if (v_isSharedCheck_150_ == 0)
{
lean_object* v_unused_151_; lean_object* v_unused_152_; lean_object* v_unused_153_; lean_object* v_unused_154_; lean_object* v_unused_155_; 
v_unused_151_ = lean_ctor_get(v_l_101_, 4);
lean_dec(v_unused_151_);
v_unused_152_ = lean_ctor_get(v_l_101_, 3);
lean_dec(v_unused_152_);
v_unused_153_ = lean_ctor_get(v_l_101_, 2);
lean_dec(v_unused_153_);
v_unused_154_ = lean_ctor_get(v_l_101_, 1);
lean_dec(v_unused_154_);
v_unused_155_ = lean_ctor_get(v_l_101_, 0);
lean_dec(v_unused_155_);
v___x_124_ = v_l_101_;
v_isShared_125_ = v_isSharedCheck_150_;
goto v_resetjp_123_;
}
else
{
lean_dec(v_l_101_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_150_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___y_129_; lean_object* v___y_130_; lean_object* v___y_131_; lean_object* v___y_140_; 
v___x_126_ = lean_nat_add(v___x_96_, v_size_97_);
lean_dec(v_size_97_);
v___x_127_ = lean_nat_add(v___x_126_, v_size_98_);
lean_dec(v_size_98_);
if (lean_obj_tag(v_l_117_) == 0)
{
lean_object* v_size_148_; 
v_size_148_ = lean_ctor_get(v_l_117_, 0);
lean_inc(v_size_148_);
v___y_140_ = v_size_148_;
goto v___jp_139_;
}
else
{
lean_object* v___x_149_; 
v___x_149_ = lean_unsigned_to_nat(0u);
v___y_140_ = v___x_149_;
goto v___jp_139_;
}
v___jp_128_:
{
lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_132_ = lean_nat_add(v___y_130_, v___y_131_);
lean_dec(v___y_131_);
lean_dec(v___y_130_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 4, v_r_102_);
lean_ctor_set(v___x_124_, 3, v_r_118_);
lean_ctor_set(v___x_124_, 2, v_v_100_);
lean_ctor_set(v___x_124_, 1, v_k_99_);
lean_ctor_set(v___x_124_, 0, v___x_132_);
v___x_134_ = v___x_124_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_k_99_);
lean_ctor_set(v_reuseFailAlloc_138_, 2, v_v_100_);
lean_ctor_set(v_reuseFailAlloc_138_, 3, v_r_118_);
lean_ctor_set(v_reuseFailAlloc_138_, 4, v_r_102_);
v___x_134_ = v_reuseFailAlloc_138_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_136_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v___x_134_);
lean_ctor_set(v___x_112_, 3, v___y_129_);
lean_ctor_set(v___x_112_, 2, v_v_116_);
lean_ctor_set(v___x_112_, 1, v_k_115_);
lean_ctor_set(v___x_112_, 0, v___x_127_);
v___x_136_ = v___x_112_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_k_115_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v_v_116_);
lean_ctor_set(v_reuseFailAlloc_137_, 3, v___y_129_);
lean_ctor_set(v_reuseFailAlloc_137_, 4, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
v___jp_139_:
{
lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_141_ = lean_nat_add(v___x_126_, v___y_140_);
lean_dec(v___y_140_);
lean_dec(v___x_126_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v_l_117_);
lean_ctor_set(v___x_92_, 3, v_impl_95_);
lean_ctor_set(v___x_92_, 0, v___x_141_);
v___x_143_ = v___x_92_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_147_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_147_, 3, v_impl_95_);
lean_ctor_set(v_reuseFailAlloc_147_, 4, v_l_117_);
v___x_143_ = v_reuseFailAlloc_147_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; 
v___x_144_ = lean_nat_add(v___x_96_, v_size_119_);
if (lean_obj_tag(v_r_118_) == 0)
{
lean_object* v_size_145_; 
v_size_145_ = lean_ctor_get(v_r_118_, 0);
lean_inc(v_size_145_);
v___y_129_ = v___x_143_;
v___y_130_ = v___x_144_;
v___y_131_ = v_size_145_;
goto v___jp_128_;
}
else
{
lean_object* v___x_146_; 
v___x_146_ = lean_unsigned_to_nat(0u);
v___y_129_ = v___x_143_;
v___y_130_ = v___x_144_;
v___y_131_ = v___x_146_;
goto v___jp_128_;
}
}
}
}
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
lean_del_object(v___x_92_);
v___x_156_ = lean_nat_add(v___x_96_, v_size_97_);
lean_dec(v_size_97_);
v___x_157_ = lean_nat_add(v___x_156_, v_size_98_);
lean_dec(v_size_98_);
v___x_158_ = lean_nat_add(v___x_156_, v_size_114_);
lean_dec(v___x_156_);
lean_inc_ref(v_impl_95_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 4, v_l_101_);
lean_ctor_set(v___x_112_, 3, v_impl_95_);
lean_ctor_set(v___x_112_, 2, v_v_88_);
lean_ctor_set(v___x_112_, 1, v_k_87_);
lean_ctor_set(v___x_112_, 0, v___x_158_);
v___x_160_ = v___x_112_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_173_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_173_, 3, v_impl_95_);
lean_ctor_set(v_reuseFailAlloc_173_, 4, v_l_101_);
v___x_160_ = v_reuseFailAlloc_173_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_isSharedCheck_167_ = !lean_is_exclusive(v_impl_95_);
if (v_isSharedCheck_167_ == 0)
{
lean_object* v_unused_168_; lean_object* v_unused_169_; lean_object* v_unused_170_; lean_object* v_unused_171_; lean_object* v_unused_172_; 
v_unused_168_ = lean_ctor_get(v_impl_95_, 4);
lean_dec(v_unused_168_);
v_unused_169_ = lean_ctor_get(v_impl_95_, 3);
lean_dec(v_unused_169_);
v_unused_170_ = lean_ctor_get(v_impl_95_, 2);
lean_dec(v_unused_170_);
v_unused_171_ = lean_ctor_get(v_impl_95_, 1);
lean_dec(v_unused_171_);
v_unused_172_ = lean_ctor_get(v_impl_95_, 0);
lean_dec(v_unused_172_);
v___x_162_ = v_impl_95_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_dec(v_impl_95_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 4, v_r_102_);
lean_ctor_set(v___x_162_, 3, v___x_160_);
lean_ctor_set(v___x_162_, 2, v_v_100_);
lean_ctor_set(v___x_162_, 1, v_k_99_);
lean_ctor_set(v___x_162_, 0, v___x_157_);
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_157_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_k_99_);
lean_ctor_set(v_reuseFailAlloc_166_, 2, v_v_100_);
lean_ctor_set(v_reuseFailAlloc_166_, 3, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_166_, 4, v_r_102_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v_size_180_ = lean_ctor_get(v_impl_95_, 0);
lean_inc(v_size_180_);
v___x_181_ = lean_nat_add(v___x_96_, v_size_180_);
lean_dec(v_size_180_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 3, v_impl_95_);
lean_ctor_set(v___x_92_, 0, v___x_181_);
v___x_183_ = v___x_92_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_184_, 3, v_impl_95_);
lean_ctor_set(v_reuseFailAlloc_184_, 4, v_r_90_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
else
{
if (lean_obj_tag(v_r_90_) == 0)
{
lean_object* v_l_185_; 
v_l_185_ = lean_ctor_get(v_r_90_, 3);
lean_inc(v_l_185_);
if (lean_obj_tag(v_l_185_) == 0)
{
lean_object* v_r_186_; 
v_r_186_ = lean_ctor_get(v_r_90_, 4);
lean_inc(v_r_186_);
if (lean_obj_tag(v_r_186_) == 0)
{
lean_object* v_size_187_; lean_object* v_k_188_; lean_object* v_v_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_202_; 
v_size_187_ = lean_ctor_get(v_r_90_, 0);
v_k_188_ = lean_ctor_get(v_r_90_, 1);
v_v_189_ = lean_ctor_get(v_r_90_, 2);
v_isSharedCheck_202_ = !lean_is_exclusive(v_r_90_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; lean_object* v_unused_204_; 
v_unused_203_ = lean_ctor_get(v_r_90_, 4);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_r_90_, 3);
lean_dec(v_unused_204_);
v___x_191_ = v_r_90_;
v_isShared_192_ = v_isSharedCheck_202_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_v_189_);
lean_inc(v_k_188_);
lean_inc(v_size_187_);
lean_dec(v_r_90_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_202_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v_size_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v_size_193_ = lean_ctor_get(v_l_185_, 0);
v___x_194_ = lean_nat_add(v___x_96_, v_size_187_);
lean_dec(v_size_187_);
v___x_195_ = lean_nat_add(v___x_96_, v_size_193_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 4, v_l_185_);
lean_ctor_set(v___x_191_, 3, v_impl_95_);
lean_ctor_set(v___x_191_, 2, v_v_88_);
lean_ctor_set(v___x_191_, 1, v_k_87_);
lean_ctor_set(v___x_191_, 0, v___x_195_);
v___x_197_ = v___x_191_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_201_, 3, v_impl_95_);
lean_ctor_set(v_reuseFailAlloc_201_, 4, v_l_185_);
v___x_197_ = v_reuseFailAlloc_201_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_199_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v_r_186_);
lean_ctor_set(v___x_92_, 3, v___x_197_);
lean_ctor_set(v___x_92_, 2, v_v_189_);
lean_ctor_set(v___x_92_, 1, v_k_188_);
lean_ctor_set(v___x_92_, 0, v___x_194_);
v___x_199_ = v___x_92_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_k_188_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_v_189_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_200_, 4, v_r_186_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
else
{
lean_object* v_k_205_; lean_object* v_v_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_229_; 
v_k_205_ = lean_ctor_get(v_r_90_, 1);
v_v_206_ = lean_ctor_get(v_r_90_, 2);
v_isSharedCheck_229_ = !lean_is_exclusive(v_r_90_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; lean_object* v_unused_231_; lean_object* v_unused_232_; 
v_unused_230_ = lean_ctor_get(v_r_90_, 4);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_r_90_, 3);
lean_dec(v_unused_231_);
v_unused_232_ = lean_ctor_get(v_r_90_, 0);
lean_dec(v_unused_232_);
v___x_208_ = v_r_90_;
v_isShared_209_ = v_isSharedCheck_229_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_v_206_);
lean_inc(v_k_205_);
lean_dec(v_r_90_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_229_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v_k_210_; lean_object* v_v_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_225_; 
v_k_210_ = lean_ctor_get(v_l_185_, 1);
v_v_211_ = lean_ctor_get(v_l_185_, 2);
v_isSharedCheck_225_ = !lean_is_exclusive(v_l_185_);
if (v_isSharedCheck_225_ == 0)
{
lean_object* v_unused_226_; lean_object* v_unused_227_; lean_object* v_unused_228_; 
v_unused_226_ = lean_ctor_get(v_l_185_, 4);
lean_dec(v_unused_226_);
v_unused_227_ = lean_ctor_get(v_l_185_, 3);
lean_dec(v_unused_227_);
v_unused_228_ = lean_ctor_get(v_l_185_, 0);
lean_dec(v_unused_228_);
v___x_213_ = v_l_185_;
v_isShared_214_ = v_isSharedCheck_225_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_v_211_);
lean_inc(v_k_210_);
lean_dec(v_l_185_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_225_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_215_ = lean_unsigned_to_nat(3u);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 4, v_r_186_);
lean_ctor_set(v___x_213_, 3, v_r_186_);
lean_ctor_set(v___x_213_, 2, v_v_88_);
lean_ctor_set(v___x_213_, 1, v_k_87_);
lean_ctor_set(v___x_213_, 0, v___x_96_);
v___x_217_ = v___x_213_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_224_, 3, v_r_186_);
lean_ctor_set(v_reuseFailAlloc_224_, 4, v_r_186_);
v___x_217_ = v_reuseFailAlloc_224_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_219_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 3, v_r_186_);
lean_ctor_set(v___x_208_, 0, v___x_96_);
v___x_219_ = v___x_208_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_k_205_);
lean_ctor_set(v_reuseFailAlloc_223_, 2, v_v_206_);
lean_ctor_set(v_reuseFailAlloc_223_, 3, v_r_186_);
lean_ctor_set(v_reuseFailAlloc_223_, 4, v_r_186_);
v___x_219_ = v_reuseFailAlloc_223_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_221_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v___x_219_);
lean_ctor_set(v___x_92_, 3, v___x_217_);
lean_ctor_set(v___x_92_, 2, v_v_211_);
lean_ctor_set(v___x_92_, 1, v_k_210_);
lean_ctor_set(v___x_92_, 0, v___x_215_);
v___x_221_ = v___x_92_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_215_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_k_210_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v_v_211_);
lean_ctor_set(v_reuseFailAlloc_222_, 3, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_222_, 4, v___x_219_);
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
}
}
}
else
{
lean_object* v_r_233_; 
v_r_233_ = lean_ctor_get(v_r_90_, 4);
lean_inc(v_r_233_);
if (lean_obj_tag(v_r_233_) == 0)
{
lean_object* v_k_234_; lean_object* v_v_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_246_; 
v_k_234_ = lean_ctor_get(v_r_90_, 1);
v_v_235_ = lean_ctor_get(v_r_90_, 2);
v_isSharedCheck_246_ = !lean_is_exclusive(v_r_90_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; lean_object* v_unused_248_; lean_object* v_unused_249_; 
v_unused_247_ = lean_ctor_get(v_r_90_, 4);
lean_dec(v_unused_247_);
v_unused_248_ = lean_ctor_get(v_r_90_, 3);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_r_90_, 0);
lean_dec(v_unused_249_);
v___x_237_ = v_r_90_;
v_isShared_238_ = v_isSharedCheck_246_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_v_235_);
lean_inc(v_k_234_);
lean_dec(v_r_90_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_246_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = lean_unsigned_to_nat(3u);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 4, v_l_185_);
lean_ctor_set(v___x_237_, 2, v_v_88_);
lean_ctor_set(v___x_237_, 1, v_k_87_);
lean_ctor_set(v___x_237_, 0, v___x_96_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_245_, 3, v_l_185_);
lean_ctor_set(v_reuseFailAlloc_245_, 4, v_l_185_);
v___x_241_ = v_reuseFailAlloc_245_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_243_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v_r_233_);
lean_ctor_set(v___x_92_, 3, v___x_241_);
lean_ctor_set(v___x_92_, 2, v_v_235_);
lean_ctor_set(v___x_92_, 1, v_k_234_);
lean_ctor_set(v___x_92_, 0, v___x_239_);
v___x_243_ = v___x_92_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_k_234_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v_v_235_);
lean_ctor_set(v_reuseFailAlloc_244_, 3, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_244_, 4, v_r_233_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
else
{
lean_object* v_size_250_; lean_object* v_k_251_; lean_object* v_v_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_263_; 
v_size_250_ = lean_ctor_get(v_r_90_, 0);
v_k_251_ = lean_ctor_get(v_r_90_, 1);
v_v_252_ = lean_ctor_get(v_r_90_, 2);
v_isSharedCheck_263_ = !lean_is_exclusive(v_r_90_);
if (v_isSharedCheck_263_ == 0)
{
lean_object* v_unused_264_; lean_object* v_unused_265_; 
v_unused_264_ = lean_ctor_get(v_r_90_, 4);
lean_dec(v_unused_264_);
v_unused_265_ = lean_ctor_get(v_r_90_, 3);
lean_dec(v_unused_265_);
v___x_254_ = v_r_90_;
v_isShared_255_ = v_isSharedCheck_263_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_v_252_);
lean_inc(v_k_251_);
lean_inc(v_size_250_);
lean_dec(v_r_90_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_263_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 3, v_r_233_);
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_size_250_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_k_251_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_v_252_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v_r_233_);
lean_ctor_set(v_reuseFailAlloc_262_, 4, v_r_233_);
v___x_257_ = v_reuseFailAlloc_262_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_258_ = lean_unsigned_to_nat(2u);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v___x_257_);
lean_ctor_set(v___x_92_, 3, v_r_233_);
lean_ctor_set(v___x_92_, 0, v___x_258_);
v___x_260_ = v___x_92_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v_r_233_);
lean_ctor_set(v_reuseFailAlloc_261_, 4, v___x_257_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
}
else
{
lean_object* v___x_267_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 3, v_r_90_);
lean_ctor_set(v___x_92_, 0, v___x_96_);
v___x_267_ = v___x_92_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_268_, 3, v_r_90_);
lean_ctor_set(v_reuseFailAlloc_268_, 4, v_r_90_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
case 1:
{
lean_del_object(v___x_92_);
lean_dec(v_v_88_);
lean_dec(v_k_87_);
if (lean_obj_tag(v_l_89_) == 0)
{
if (lean_obj_tag(v_r_90_) == 0)
{
lean_object* v_size_269_; lean_object* v_k_270_; lean_object* v_v_271_; lean_object* v_l_272_; lean_object* v_r_273_; lean_object* v_size_274_; lean_object* v_k_275_; lean_object* v_v_276_; lean_object* v_l_277_; lean_object* v_r_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v_size_269_ = lean_ctor_get(v_l_89_, 0);
v_k_270_ = lean_ctor_get(v_l_89_, 1);
v_v_271_ = lean_ctor_get(v_l_89_, 2);
v_l_272_ = lean_ctor_get(v_l_89_, 3);
v_r_273_ = lean_ctor_get(v_l_89_, 4);
lean_inc(v_r_273_);
v_size_274_ = lean_ctor_get(v_r_90_, 0);
v_k_275_ = lean_ctor_get(v_r_90_, 1);
v_v_276_ = lean_ctor_get(v_r_90_, 2);
v_l_277_ = lean_ctor_get(v_r_90_, 3);
lean_inc(v_l_277_);
v_r_278_ = lean_ctor_get(v_r_90_, 4);
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = lean_nat_dec_lt(v_size_269_, v_size_274_);
if (v___x_280_ == 0)
{
lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_416_; 
lean_inc(v_l_272_);
lean_inc(v_v_271_);
lean_inc(v_k_270_);
v_isSharedCheck_416_ = !lean_is_exclusive(v_l_89_);
if (v_isSharedCheck_416_ == 0)
{
lean_object* v_unused_417_; lean_object* v_unused_418_; lean_object* v_unused_419_; lean_object* v_unused_420_; lean_object* v_unused_421_; 
v_unused_417_ = lean_ctor_get(v_l_89_, 4);
lean_dec(v_unused_417_);
v_unused_418_ = lean_ctor_get(v_l_89_, 3);
lean_dec(v_unused_418_);
v_unused_419_ = lean_ctor_get(v_l_89_, 2);
lean_dec(v_unused_419_);
v_unused_420_ = lean_ctor_get(v_l_89_, 1);
lean_dec(v_unused_420_);
v_unused_421_ = lean_ctor_get(v_l_89_, 0);
lean_dec(v_unused_421_);
v___x_282_ = v_l_89_;
v_isShared_283_ = v_isSharedCheck_416_;
goto v_resetjp_281_;
}
else
{
lean_dec(v_l_89_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_416_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v_tree_285_; 
v___x_284_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_270_, v_v_271_, v_l_272_, v_r_273_);
v_tree_285_ = lean_ctor_get(v___x_284_, 2);
lean_inc(v_tree_285_);
if (lean_obj_tag(v_tree_285_) == 0)
{
lean_object* v_k_286_; lean_object* v_v_287_; lean_object* v_size_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_k_286_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_k_286_);
v_v_287_ = lean_ctor_get(v___x_284_, 1);
lean_inc(v_v_287_);
lean_dec_ref(v___x_284_);
v_size_288_ = lean_ctor_get(v_tree_285_, 0);
v___x_289_ = lean_unsigned_to_nat(3u);
v___x_290_ = lean_nat_mul(v___x_289_, v_size_288_);
v___x_291_ = lean_nat_dec_lt(v___x_290_, v_size_274_);
lean_dec(v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
lean_dec(v_l_277_);
v___x_292_ = lean_nat_add(v___x_279_, v_size_288_);
v___x_293_ = lean_nat_add(v___x_292_, v_size_274_);
lean_dec(v___x_292_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 4, v_r_90_);
lean_ctor_set(v___x_282_, 3, v_tree_285_);
lean_ctor_set(v___x_282_, 2, v_v_287_);
lean_ctor_set(v___x_282_, 1, v_k_286_);
lean_ctor_set(v___x_282_, 0, v___x_293_);
v___x_295_ = v___x_282_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_k_286_);
lean_ctor_set(v_reuseFailAlloc_296_, 2, v_v_287_);
lean_ctor_set(v_reuseFailAlloc_296_, 3, v_tree_285_);
lean_ctor_set(v_reuseFailAlloc_296_, 4, v_r_90_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
else
{
lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_351_; 
lean_inc(v_r_278_);
lean_inc(v_v_276_);
lean_inc(v_k_275_);
lean_inc(v_size_274_);
v_isSharedCheck_351_ = !lean_is_exclusive(v_r_90_);
if (v_isSharedCheck_351_ == 0)
{
lean_object* v_unused_352_; lean_object* v_unused_353_; lean_object* v_unused_354_; lean_object* v_unused_355_; lean_object* v_unused_356_; 
v_unused_352_ = lean_ctor_get(v_r_90_, 4);
lean_dec(v_unused_352_);
v_unused_353_ = lean_ctor_get(v_r_90_, 3);
lean_dec(v_unused_353_);
v_unused_354_ = lean_ctor_get(v_r_90_, 2);
lean_dec(v_unused_354_);
v_unused_355_ = lean_ctor_get(v_r_90_, 1);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_r_90_, 0);
lean_dec(v_unused_356_);
v___x_298_ = v_r_90_;
v_isShared_299_ = v_isSharedCheck_351_;
goto v_resetjp_297_;
}
else
{
lean_dec(v_r_90_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_351_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v_size_300_; lean_object* v_k_301_; lean_object* v_v_302_; lean_object* v_l_303_; lean_object* v_r_304_; lean_object* v_size_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_size_300_ = lean_ctor_get(v_l_277_, 0);
v_k_301_ = lean_ctor_get(v_l_277_, 1);
v_v_302_ = lean_ctor_get(v_l_277_, 2);
v_l_303_ = lean_ctor_get(v_l_277_, 3);
v_r_304_ = lean_ctor_get(v_l_277_, 4);
v_size_305_ = lean_ctor_get(v_r_278_, 0);
v___x_306_ = lean_unsigned_to_nat(2u);
v___x_307_ = lean_nat_mul(v___x_306_, v_size_305_);
v___x_308_ = lean_nat_dec_lt(v_size_300_, v___x_307_);
lean_dec(v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_336_; 
lean_inc(v_r_304_);
lean_inc(v_l_303_);
lean_inc(v_v_302_);
lean_inc(v_k_301_);
v_isSharedCheck_336_ = !lean_is_exclusive(v_l_277_);
if (v_isSharedCheck_336_ == 0)
{
lean_object* v_unused_337_; lean_object* v_unused_338_; lean_object* v_unused_339_; lean_object* v_unused_340_; lean_object* v_unused_341_; 
v_unused_337_ = lean_ctor_get(v_l_277_, 4);
lean_dec(v_unused_337_);
v_unused_338_ = lean_ctor_get(v_l_277_, 3);
lean_dec(v_unused_338_);
v_unused_339_ = lean_ctor_get(v_l_277_, 2);
lean_dec(v_unused_339_);
v_unused_340_ = lean_ctor_get(v_l_277_, 1);
lean_dec(v_unused_340_);
v_unused_341_ = lean_ctor_get(v_l_277_, 0);
lean_dec(v_unused_341_);
v___x_310_ = v_l_277_;
v_isShared_311_ = v_isSharedCheck_336_;
goto v_resetjp_309_;
}
else
{
lean_dec(v_l_277_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_336_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_326_; 
v___x_312_ = lean_nat_add(v___x_279_, v_size_288_);
v___x_313_ = lean_nat_add(v___x_312_, v_size_274_);
lean_dec(v_size_274_);
if (lean_obj_tag(v_l_303_) == 0)
{
lean_object* v_size_334_; 
v_size_334_ = lean_ctor_get(v_l_303_, 0);
lean_inc(v_size_334_);
v___y_326_ = v_size_334_;
goto v___jp_325_;
}
else
{
lean_object* v___x_335_; 
v___x_335_ = lean_unsigned_to_nat(0u);
v___y_326_ = v___x_335_;
goto v___jp_325_;
}
v___jp_314_:
{
lean_object* v___x_318_; lean_object* v___x_320_; 
v___x_318_ = lean_nat_add(v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec(v___y_316_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 4, v_r_278_);
lean_ctor_set(v___x_310_, 3, v_r_304_);
lean_ctor_set(v___x_310_, 2, v_v_276_);
lean_ctor_set(v___x_310_, 1, v_k_275_);
lean_ctor_set(v___x_310_, 0, v___x_318_);
v___x_320_ = v___x_310_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_k_275_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v_v_276_);
lean_ctor_set(v_reuseFailAlloc_324_, 3, v_r_304_);
lean_ctor_set(v_reuseFailAlloc_324_, 4, v_r_278_);
v___x_320_ = v_reuseFailAlloc_324_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_322_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 4, v___x_320_);
lean_ctor_set(v___x_298_, 3, v___y_315_);
lean_ctor_set(v___x_298_, 2, v_v_302_);
lean_ctor_set(v___x_298_, 1, v_k_301_);
lean_ctor_set(v___x_298_, 0, v___x_313_);
v___x_322_ = v___x_298_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_k_301_);
lean_ctor_set(v_reuseFailAlloc_323_, 2, v_v_302_);
lean_ctor_set(v_reuseFailAlloc_323_, 3, v___y_315_);
lean_ctor_set(v_reuseFailAlloc_323_, 4, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
v___jp_325_:
{
lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_327_ = lean_nat_add(v___x_312_, v___y_326_);
lean_dec(v___y_326_);
lean_dec(v___x_312_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 4, v_l_303_);
lean_ctor_set(v___x_282_, 3, v_tree_285_);
lean_ctor_set(v___x_282_, 2, v_v_287_);
lean_ctor_set(v___x_282_, 1, v_k_286_);
lean_ctor_set(v___x_282_, 0, v___x_327_);
v___x_329_ = v___x_282_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_k_286_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_v_287_);
lean_ctor_set(v_reuseFailAlloc_333_, 3, v_tree_285_);
lean_ctor_set(v_reuseFailAlloc_333_, 4, v_l_303_);
v___x_329_ = v_reuseFailAlloc_333_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; 
v___x_330_ = lean_nat_add(v___x_279_, v_size_305_);
if (lean_obj_tag(v_r_304_) == 0)
{
lean_object* v_size_331_; 
v_size_331_ = lean_ctor_get(v_r_304_, 0);
lean_inc(v_size_331_);
v___y_315_ = v___x_329_;
v___y_316_ = v___x_330_;
v___y_317_ = v_size_331_;
goto v___jp_314_;
}
else
{
lean_object* v___x_332_; 
v___x_332_ = lean_unsigned_to_nat(0u);
v___y_315_ = v___x_329_;
v___y_316_ = v___x_330_;
v___y_317_ = v___x_332_;
goto v___jp_314_;
}
}
}
}
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_342_ = lean_nat_add(v___x_279_, v_size_288_);
v___x_343_ = lean_nat_add(v___x_342_, v_size_274_);
lean_dec(v_size_274_);
v___x_344_ = lean_nat_add(v___x_342_, v_size_300_);
lean_dec(v___x_342_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 4, v_l_277_);
lean_ctor_set(v___x_298_, 3, v_tree_285_);
lean_ctor_set(v___x_298_, 2, v_v_287_);
lean_ctor_set(v___x_298_, 1, v_k_286_);
lean_ctor_set(v___x_298_, 0, v___x_344_);
v___x_346_ = v___x_298_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_k_286_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_v_287_);
lean_ctor_set(v_reuseFailAlloc_350_, 3, v_tree_285_);
lean_ctor_set(v_reuseFailAlloc_350_, 4, v_l_277_);
v___x_346_ = v_reuseFailAlloc_350_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_348_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 4, v_r_278_);
lean_ctor_set(v___x_282_, 3, v___x_346_);
lean_ctor_set(v___x_282_, 2, v_v_276_);
lean_ctor_set(v___x_282_, 1, v_k_275_);
lean_ctor_set(v___x_282_, 0, v___x_343_);
v___x_348_ = v___x_282_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_343_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_k_275_);
lean_ctor_set(v_reuseFailAlloc_349_, 2, v_v_276_);
lean_ctor_set(v_reuseFailAlloc_349_, 3, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_349_, 4, v_r_278_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
}
else
{
lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_410_; 
lean_inc(v_r_278_);
lean_inc(v_v_276_);
lean_inc(v_k_275_);
lean_inc(v_size_274_);
v_isSharedCheck_410_ = !lean_is_exclusive(v_r_90_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; lean_object* v_unused_412_; lean_object* v_unused_413_; lean_object* v_unused_414_; lean_object* v_unused_415_; 
v_unused_411_ = lean_ctor_get(v_r_90_, 4);
lean_dec(v_unused_411_);
v_unused_412_ = lean_ctor_get(v_r_90_, 3);
lean_dec(v_unused_412_);
v_unused_413_ = lean_ctor_get(v_r_90_, 2);
lean_dec(v_unused_413_);
v_unused_414_ = lean_ctor_get(v_r_90_, 1);
lean_dec(v_unused_414_);
v_unused_415_ = lean_ctor_get(v_r_90_, 0);
lean_dec(v_unused_415_);
v___x_358_ = v_r_90_;
v_isShared_359_ = v_isSharedCheck_410_;
goto v_resetjp_357_;
}
else
{
lean_dec(v_r_90_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_410_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
if (lean_obj_tag(v_l_277_) == 0)
{
if (lean_obj_tag(v_r_278_) == 0)
{
lean_object* v_k_360_; lean_object* v_v_361_; lean_object* v_size_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v_k_360_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_k_360_);
v_v_361_ = lean_ctor_get(v___x_284_, 1);
lean_inc(v_v_361_);
lean_dec_ref(v___x_284_);
v_size_362_ = lean_ctor_get(v_l_277_, 0);
v___x_363_ = lean_nat_add(v___x_279_, v_size_274_);
lean_dec(v_size_274_);
v___x_364_ = lean_nat_add(v___x_279_, v_size_362_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 4, v_l_277_);
lean_ctor_set(v___x_358_, 3, v_tree_285_);
lean_ctor_set(v___x_358_, 2, v_v_361_);
lean_ctor_set(v___x_358_, 1, v_k_360_);
lean_ctor_set(v___x_358_, 0, v___x_364_);
v___x_366_ = v___x_358_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_370_, 3, v_tree_285_);
lean_ctor_set(v_reuseFailAlloc_370_, 4, v_l_277_);
v___x_366_ = v_reuseFailAlloc_370_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_368_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 4, v_r_278_);
lean_ctor_set(v___x_282_, 3, v___x_366_);
lean_ctor_set(v___x_282_, 2, v_v_276_);
lean_ctor_set(v___x_282_, 1, v_k_275_);
lean_ctor_set(v___x_282_, 0, v___x_363_);
v___x_368_ = v___x_282_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_k_275_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_v_276_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_369_, 4, v_r_278_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v_k_371_; lean_object* v_v_372_; lean_object* v_k_373_; lean_object* v_v_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_388_; 
lean_dec(v_size_274_);
v_k_371_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_k_371_);
v_v_372_ = lean_ctor_get(v___x_284_, 1);
lean_inc(v_v_372_);
lean_dec_ref(v___x_284_);
v_k_373_ = lean_ctor_get(v_l_277_, 1);
v_v_374_ = lean_ctor_get(v_l_277_, 2);
v_isSharedCheck_388_ = !lean_is_exclusive(v_l_277_);
if (v_isSharedCheck_388_ == 0)
{
lean_object* v_unused_389_; lean_object* v_unused_390_; lean_object* v_unused_391_; 
v_unused_389_ = lean_ctor_get(v_l_277_, 4);
lean_dec(v_unused_389_);
v_unused_390_ = lean_ctor_get(v_l_277_, 3);
lean_dec(v_unused_390_);
v_unused_391_ = lean_ctor_get(v_l_277_, 0);
lean_dec(v_unused_391_);
v___x_376_ = v_l_277_;
v_isShared_377_ = v_isSharedCheck_388_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_v_374_);
lean_inc(v_k_373_);
lean_dec(v_l_277_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_388_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_378_ = lean_unsigned_to_nat(3u);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 4, v_r_278_);
lean_ctor_set(v___x_376_, 3, v_r_278_);
lean_ctor_set(v___x_376_, 2, v_v_372_);
lean_ctor_set(v___x_376_, 1, v_k_371_);
lean_ctor_set(v___x_376_, 0, v___x_279_);
v___x_380_ = v___x_376_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_k_371_);
lean_ctor_set(v_reuseFailAlloc_387_, 2, v_v_372_);
lean_ctor_set(v_reuseFailAlloc_387_, 3, v_r_278_);
lean_ctor_set(v_reuseFailAlloc_387_, 4, v_r_278_);
v___x_380_ = v_reuseFailAlloc_387_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_382_; 
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 3, v_r_278_);
lean_ctor_set(v___x_358_, 0, v___x_279_);
v___x_382_ = v___x_358_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_k_275_);
lean_ctor_set(v_reuseFailAlloc_386_, 2, v_v_276_);
lean_ctor_set(v_reuseFailAlloc_386_, 3, v_r_278_);
lean_ctor_set(v_reuseFailAlloc_386_, 4, v_r_278_);
v___x_382_ = v_reuseFailAlloc_386_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_384_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 4, v___x_382_);
lean_ctor_set(v___x_282_, 3, v___x_380_);
lean_ctor_set(v___x_282_, 2, v_v_374_);
lean_ctor_set(v___x_282_, 1, v_k_373_);
lean_ctor_set(v___x_282_, 0, v___x_378_);
v___x_384_ = v___x_282_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_k_373_);
lean_ctor_set(v_reuseFailAlloc_385_, 2, v_v_374_);
lean_ctor_set(v_reuseFailAlloc_385_, 3, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_385_, 4, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_278_) == 0)
{
lean_object* v_k_392_; lean_object* v_v_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
lean_dec(v_size_274_);
v_k_392_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_k_392_);
v_v_393_ = lean_ctor_get(v___x_284_, 1);
lean_inc(v_v_393_);
lean_dec_ref(v___x_284_);
v___x_394_ = lean_unsigned_to_nat(3u);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 4, v_l_277_);
lean_ctor_set(v___x_358_, 2, v_v_393_);
lean_ctor_set(v___x_358_, 1, v_k_392_);
lean_ctor_set(v___x_358_, 0, v___x_279_);
v___x_396_ = v___x_358_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_k_392_);
lean_ctor_set(v_reuseFailAlloc_400_, 2, v_v_393_);
lean_ctor_set(v_reuseFailAlloc_400_, 3, v_l_277_);
lean_ctor_set(v_reuseFailAlloc_400_, 4, v_l_277_);
v___x_396_ = v_reuseFailAlloc_400_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_398_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 4, v_r_278_);
lean_ctor_set(v___x_282_, 3, v___x_396_);
lean_ctor_set(v___x_282_, 2, v_v_276_);
lean_ctor_set(v___x_282_, 1, v_k_275_);
lean_ctor_set(v___x_282_, 0, v___x_394_);
v___x_398_ = v___x_282_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_k_275_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v_v_276_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v___x_396_);
lean_ctor_set(v_reuseFailAlloc_399_, 4, v_r_278_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
else
{
lean_object* v_k_401_; lean_object* v_v_402_; lean_object* v___x_404_; 
v_k_401_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_k_401_);
v_v_402_ = lean_ctor_get(v___x_284_, 1);
lean_inc(v_v_402_);
lean_dec_ref(v___x_284_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 3, v_r_278_);
v___x_404_ = v___x_358_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_size_274_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_k_275_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_v_276_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_r_278_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v_r_278_);
v___x_404_ = v_reuseFailAlloc_409_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = lean_unsigned_to_nat(2u);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 4, v___x_404_);
lean_ctor_set(v___x_282_, 3, v_r_278_);
lean_ctor_set(v___x_282_, 2, v_v_402_);
lean_ctor_set(v___x_282_, 1, v_k_401_);
lean_ctor_set(v___x_282_, 0, v___x_405_);
v___x_407_ = v___x_282_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_k_401_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_v_402_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_r_278_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v___x_404_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
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
lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_574_; 
lean_inc(v_r_278_);
lean_inc(v_v_276_);
lean_inc(v_k_275_);
v_isSharedCheck_574_ = !lean_is_exclusive(v_r_90_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; lean_object* v_unused_576_; lean_object* v_unused_577_; lean_object* v_unused_578_; lean_object* v_unused_579_; 
v_unused_575_ = lean_ctor_get(v_r_90_, 4);
lean_dec(v_unused_575_);
v_unused_576_ = lean_ctor_get(v_r_90_, 3);
lean_dec(v_unused_576_);
v_unused_577_ = lean_ctor_get(v_r_90_, 2);
lean_dec(v_unused_577_);
v_unused_578_ = lean_ctor_get(v_r_90_, 1);
lean_dec(v_unused_578_);
v_unused_579_ = lean_ctor_get(v_r_90_, 0);
lean_dec(v_unused_579_);
v___x_423_ = v_r_90_;
v_isShared_424_ = v_isSharedCheck_574_;
goto v_resetjp_422_;
}
else
{
lean_dec(v_r_90_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_574_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v_tree_426_; 
v___x_425_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_275_, v_v_276_, v_l_277_, v_r_278_);
v_tree_426_ = lean_ctor_get(v___x_425_, 2);
lean_inc(v_tree_426_);
if (lean_obj_tag(v_tree_426_) == 0)
{
lean_object* v_k_427_; lean_object* v_v_428_; lean_object* v_size_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_k_427_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_k_427_);
v_v_428_ = lean_ctor_get(v___x_425_, 1);
lean_inc(v_v_428_);
lean_dec_ref(v___x_425_);
v_size_429_ = lean_ctor_get(v_tree_426_, 0);
v___x_430_ = lean_unsigned_to_nat(3u);
v___x_431_ = lean_nat_mul(v___x_430_, v_size_429_);
v___x_432_ = lean_nat_dec_lt(v___x_431_, v_size_269_);
lean_dec(v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
lean_dec(v_r_273_);
v___x_433_ = lean_nat_add(v___x_279_, v_size_269_);
v___x_434_ = lean_nat_add(v___x_433_, v_size_429_);
lean_dec(v___x_433_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 4, v_tree_426_);
lean_ctor_set(v___x_423_, 3, v_l_89_);
lean_ctor_set(v___x_423_, 2, v_v_428_);
lean_ctor_set(v___x_423_, 1, v_k_427_);
lean_ctor_set(v___x_423_, 0, v___x_434_);
v___x_436_ = v___x_423_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_k_427_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_v_428_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_l_89_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v_tree_426_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
else
{
lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_503_; 
lean_inc(v_l_272_);
lean_inc(v_v_271_);
lean_inc(v_k_270_);
lean_inc(v_size_269_);
v_isSharedCheck_503_ = !lean_is_exclusive(v_l_89_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; lean_object* v_unused_505_; lean_object* v_unused_506_; lean_object* v_unused_507_; lean_object* v_unused_508_; 
v_unused_504_ = lean_ctor_get(v_l_89_, 4);
lean_dec(v_unused_504_);
v_unused_505_ = lean_ctor_get(v_l_89_, 3);
lean_dec(v_unused_505_);
v_unused_506_ = lean_ctor_get(v_l_89_, 2);
lean_dec(v_unused_506_);
v_unused_507_ = lean_ctor_get(v_l_89_, 1);
lean_dec(v_unused_507_);
v_unused_508_ = lean_ctor_get(v_l_89_, 0);
lean_dec(v_unused_508_);
v___x_439_ = v_l_89_;
v_isShared_440_ = v_isSharedCheck_503_;
goto v_resetjp_438_;
}
else
{
lean_dec(v_l_89_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_503_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_size_441_; lean_object* v_size_442_; lean_object* v_k_443_; lean_object* v_v_444_; lean_object* v_l_445_; lean_object* v_r_446_; lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_size_441_ = lean_ctor_get(v_l_272_, 0);
v_size_442_ = lean_ctor_get(v_r_273_, 0);
v_k_443_ = lean_ctor_get(v_r_273_, 1);
v_v_444_ = lean_ctor_get(v_r_273_, 2);
v_l_445_ = lean_ctor_get(v_r_273_, 3);
v_r_446_ = lean_ctor_get(v_r_273_, 4);
v___x_447_ = lean_unsigned_to_nat(2u);
v___x_448_ = lean_nat_mul(v___x_447_, v_size_441_);
v___x_449_ = lean_nat_dec_lt(v_size_442_, v___x_448_);
lean_dec(v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_487_; 
lean_inc(v_r_446_);
lean_inc(v_l_445_);
lean_inc(v_v_444_);
lean_inc(v_k_443_);
lean_del_object(v___x_439_);
v_isSharedCheck_487_ = !lean_is_exclusive(v_r_273_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; lean_object* v_unused_489_; lean_object* v_unused_490_; lean_object* v_unused_491_; lean_object* v_unused_492_; 
v_unused_488_ = lean_ctor_get(v_r_273_, 4);
lean_dec(v_unused_488_);
v_unused_489_ = lean_ctor_get(v_r_273_, 3);
lean_dec(v_unused_489_);
v_unused_490_ = lean_ctor_get(v_r_273_, 2);
lean_dec(v_unused_490_);
v_unused_491_ = lean_ctor_get(v_r_273_, 1);
lean_dec(v_unused_491_);
v_unused_492_ = lean_ctor_get(v_r_273_, 0);
lean_dec(v_unused_492_);
v___x_451_ = v_r_273_;
v_isShared_452_ = v_isSharedCheck_487_;
goto v_resetjp_450_;
}
else
{
lean_dec(v_r_273_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_487_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___x_475_; lean_object* v___y_477_; 
v___x_453_ = lean_nat_add(v___x_279_, v_size_269_);
lean_dec(v_size_269_);
v___x_454_ = lean_nat_add(v___x_453_, v_size_429_);
lean_dec(v___x_453_);
v___x_475_ = lean_nat_add(v___x_279_, v_size_441_);
if (lean_obj_tag(v_l_445_) == 0)
{
lean_object* v_size_485_; 
v_size_485_ = lean_ctor_get(v_l_445_, 0);
lean_inc(v_size_485_);
v___y_477_ = v_size_485_;
goto v___jp_476_;
}
else
{
lean_object* v___x_486_; 
v___x_486_ = lean_unsigned_to_nat(0u);
v___y_477_ = v___x_486_;
goto v___jp_476_;
}
v___jp_455_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_459_ = lean_nat_add(v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec(v___y_457_);
lean_inc_ref(v_tree_426_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 4, v_tree_426_);
lean_ctor_set(v___x_451_, 3, v_r_446_);
lean_ctor_set(v___x_451_, 2, v_v_428_);
lean_ctor_set(v___x_451_, 1, v_k_427_);
lean_ctor_set(v___x_451_, 0, v___x_459_);
v___x_461_ = v___x_451_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_k_427_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_v_428_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_r_446_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v_tree_426_);
v___x_461_ = v_reuseFailAlloc_474_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_isSharedCheck_468_ = !lean_is_exclusive(v_tree_426_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; lean_object* v_unused_470_; lean_object* v_unused_471_; lean_object* v_unused_472_; lean_object* v_unused_473_; 
v_unused_469_ = lean_ctor_get(v_tree_426_, 4);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_tree_426_, 3);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_tree_426_, 2);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_tree_426_, 1);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_tree_426_, 0);
lean_dec(v_unused_473_);
v___x_463_ = v_tree_426_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_dec(v_tree_426_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 4, v___x_461_);
lean_ctor_set(v___x_463_, 3, v___y_456_);
lean_ctor_set(v___x_463_, 2, v_v_444_);
lean_ctor_set(v___x_463_, 1, v_k_443_);
lean_ctor_set(v___x_463_, 0, v___x_454_);
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_454_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_k_443_);
lean_ctor_set(v_reuseFailAlloc_467_, 2, v_v_444_);
lean_ctor_set(v_reuseFailAlloc_467_, 3, v___y_456_);
lean_ctor_set(v_reuseFailAlloc_467_, 4, v___x_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
v___jp_476_:
{
lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_478_ = lean_nat_add(v___x_475_, v___y_477_);
lean_dec(v___y_477_);
lean_dec(v___x_475_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 4, v_l_445_);
lean_ctor_set(v___x_423_, 3, v_l_272_);
lean_ctor_set(v___x_423_, 2, v_v_271_);
lean_ctor_set(v___x_423_, 1, v_k_270_);
lean_ctor_set(v___x_423_, 0, v___x_478_);
v___x_480_ = v___x_423_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_k_270_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_v_271_);
lean_ctor_set(v_reuseFailAlloc_484_, 3, v_l_272_);
lean_ctor_set(v_reuseFailAlloc_484_, 4, v_l_445_);
v___x_480_ = v_reuseFailAlloc_484_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_481_; 
v___x_481_ = lean_nat_add(v___x_279_, v_size_429_);
if (lean_obj_tag(v_r_446_) == 0)
{
lean_object* v_size_482_; 
v_size_482_ = lean_ctor_get(v_r_446_, 0);
lean_inc(v_size_482_);
v___y_456_ = v___x_480_;
v___y_457_ = v___x_481_;
v___y_458_ = v_size_482_;
goto v___jp_455_;
}
else
{
lean_object* v___x_483_; 
v___x_483_ = lean_unsigned_to_nat(0u);
v___y_456_ = v___x_480_;
v___y_457_ = v___x_481_;
v___y_458_ = v___x_483_;
goto v___jp_455_;
}
}
}
}
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_493_ = lean_nat_add(v___x_279_, v_size_269_);
lean_dec(v_size_269_);
v___x_494_ = lean_nat_add(v___x_493_, v_size_429_);
lean_dec(v___x_493_);
v___x_495_ = lean_nat_add(v___x_279_, v_size_429_);
v___x_496_ = lean_nat_add(v___x_495_, v_size_442_);
lean_dec(v___x_495_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 4, v_tree_426_);
lean_ctor_set(v___x_423_, 3, v_r_273_);
lean_ctor_set(v___x_423_, 2, v_v_428_);
lean_ctor_set(v___x_423_, 1, v_k_427_);
lean_ctor_set(v___x_423_, 0, v___x_496_);
v___x_498_ = v___x_423_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_k_427_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_v_428_);
lean_ctor_set(v_reuseFailAlloc_502_, 3, v_r_273_);
lean_ctor_set(v_reuseFailAlloc_502_, 4, v_tree_426_);
v___x_498_ = v_reuseFailAlloc_502_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_500_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 4, v___x_498_);
lean_ctor_set(v___x_439_, 0, v___x_494_);
v___x_500_ = v___x_439_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_k_270_);
lean_ctor_set(v_reuseFailAlloc_501_, 2, v_v_271_);
lean_ctor_set(v_reuseFailAlloc_501_, 3, v_l_272_);
lean_ctor_set(v_reuseFailAlloc_501_, 4, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_272_) == 0)
{
lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_532_; 
lean_inc_ref(v_l_272_);
lean_inc(v_v_271_);
lean_inc(v_k_270_);
lean_inc(v_size_269_);
v_isSharedCheck_532_ = !lean_is_exclusive(v_l_89_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; lean_object* v_unused_534_; lean_object* v_unused_535_; lean_object* v_unused_536_; lean_object* v_unused_537_; 
v_unused_533_ = lean_ctor_get(v_l_89_, 4);
lean_dec(v_unused_533_);
v_unused_534_ = lean_ctor_get(v_l_89_, 3);
lean_dec(v_unused_534_);
v_unused_535_ = lean_ctor_get(v_l_89_, 2);
lean_dec(v_unused_535_);
v_unused_536_ = lean_ctor_get(v_l_89_, 1);
lean_dec(v_unused_536_);
v_unused_537_ = lean_ctor_get(v_l_89_, 0);
lean_dec(v_unused_537_);
v___x_510_ = v_l_89_;
v_isShared_511_ = v_isSharedCheck_532_;
goto v_resetjp_509_;
}
else
{
lean_dec(v_l_89_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_532_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
if (lean_obj_tag(v_r_273_) == 0)
{
lean_object* v_k_512_; lean_object* v_v_513_; lean_object* v_size_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v_k_512_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_k_512_);
v_v_513_ = lean_ctor_get(v___x_425_, 1);
lean_inc(v_v_513_);
lean_dec_ref(v___x_425_);
v_size_514_ = lean_ctor_get(v_r_273_, 0);
v___x_515_ = lean_nat_add(v___x_279_, v_size_269_);
lean_dec(v_size_269_);
v___x_516_ = lean_nat_add(v___x_279_, v_size_514_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 4, v_tree_426_);
lean_ctor_set(v___x_423_, 3, v_r_273_);
lean_ctor_set(v___x_423_, 2, v_v_513_);
lean_ctor_set(v___x_423_, 1, v_k_512_);
lean_ctor_set(v___x_423_, 0, v___x_516_);
v___x_518_ = v___x_423_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_k_512_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_v_513_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v_r_273_);
lean_ctor_set(v_reuseFailAlloc_522_, 4, v_tree_426_);
v___x_518_ = v_reuseFailAlloc_522_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_520_; 
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 4, v___x_518_);
lean_ctor_set(v___x_510_, 0, v___x_515_);
v___x_520_ = v___x_510_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_k_270_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v_v_271_);
lean_ctor_set(v_reuseFailAlloc_521_, 3, v_l_272_);
lean_ctor_set(v_reuseFailAlloc_521_, 4, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
else
{
lean_object* v_k_523_; lean_object* v_v_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
lean_dec(v_size_269_);
v_k_523_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_k_523_);
v_v_524_ = lean_ctor_get(v___x_425_, 1);
lean_inc(v_v_524_);
lean_dec_ref(v___x_425_);
v___x_525_ = lean_unsigned_to_nat(3u);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 4, v_r_273_);
lean_ctor_set(v___x_423_, 3, v_r_273_);
lean_ctor_set(v___x_423_, 2, v_v_524_);
lean_ctor_set(v___x_423_, 1, v_k_523_);
lean_ctor_set(v___x_423_, 0, v___x_279_);
v___x_527_ = v___x_423_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_k_523_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v_v_524_);
lean_ctor_set(v_reuseFailAlloc_531_, 3, v_r_273_);
lean_ctor_set(v_reuseFailAlloc_531_, 4, v_r_273_);
v___x_527_ = v_reuseFailAlloc_531_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_529_; 
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 4, v___x_527_);
lean_ctor_set(v___x_510_, 0, v___x_525_);
v___x_529_ = v___x_510_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_k_270_);
lean_ctor_set(v_reuseFailAlloc_530_, 2, v_v_271_);
lean_ctor_set(v_reuseFailAlloc_530_, 3, v_l_272_);
lean_ctor_set(v_reuseFailAlloc_530_, 4, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_273_) == 0)
{
lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_562_; 
lean_inc(v_l_272_);
lean_inc(v_v_271_);
lean_inc(v_k_270_);
v_isSharedCheck_562_ = !lean_is_exclusive(v_l_89_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; lean_object* v_unused_564_; lean_object* v_unused_565_; lean_object* v_unused_566_; lean_object* v_unused_567_; 
v_unused_563_ = lean_ctor_get(v_l_89_, 4);
lean_dec(v_unused_563_);
v_unused_564_ = lean_ctor_get(v_l_89_, 3);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v_l_89_, 2);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_l_89_, 1);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_l_89_, 0);
lean_dec(v_unused_567_);
v___x_539_ = v_l_89_;
v_isShared_540_ = v_isSharedCheck_562_;
goto v_resetjp_538_;
}
else
{
lean_dec(v_l_89_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_562_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_k_541_; lean_object* v_v_542_; lean_object* v_k_543_; lean_object* v_v_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_558_; 
v_k_541_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_k_541_);
v_v_542_ = lean_ctor_get(v___x_425_, 1);
lean_inc(v_v_542_);
lean_dec_ref(v___x_425_);
v_k_543_ = lean_ctor_get(v_r_273_, 1);
v_v_544_ = lean_ctor_get(v_r_273_, 2);
v_isSharedCheck_558_ = !lean_is_exclusive(v_r_273_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; lean_object* v_unused_560_; lean_object* v_unused_561_; 
v_unused_559_ = lean_ctor_get(v_r_273_, 4);
lean_dec(v_unused_559_);
v_unused_560_ = lean_ctor_get(v_r_273_, 3);
lean_dec(v_unused_560_);
v_unused_561_ = lean_ctor_get(v_r_273_, 0);
lean_dec(v_unused_561_);
v___x_546_ = v_r_273_;
v_isShared_547_ = v_isSharedCheck_558_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_v_544_);
lean_inc(v_k_543_);
lean_dec(v_r_273_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_558_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = lean_unsigned_to_nat(3u);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 4, v_l_272_);
lean_ctor_set(v___x_546_, 3, v_l_272_);
lean_ctor_set(v___x_546_, 2, v_v_271_);
lean_ctor_set(v___x_546_, 1, v_k_270_);
lean_ctor_set(v___x_546_, 0, v___x_279_);
v___x_550_ = v___x_546_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_k_270_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_v_271_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v_l_272_);
lean_ctor_set(v_reuseFailAlloc_557_, 4, v_l_272_);
v___x_550_ = v_reuseFailAlloc_557_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_552_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 4, v_l_272_);
lean_ctor_set(v___x_423_, 3, v_l_272_);
lean_ctor_set(v___x_423_, 2, v_v_542_);
lean_ctor_set(v___x_423_, 1, v_k_541_);
lean_ctor_set(v___x_423_, 0, v___x_279_);
v___x_552_ = v___x_423_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_k_541_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_v_542_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v_l_272_);
lean_ctor_set(v_reuseFailAlloc_556_, 4, v_l_272_);
v___x_552_ = v_reuseFailAlloc_556_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_554_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 4, v___x_552_);
lean_ctor_set(v___x_539_, 3, v___x_550_);
lean_ctor_set(v___x_539_, 2, v_v_544_);
lean_ctor_set(v___x_539_, 1, v_k_543_);
lean_ctor_set(v___x_539_, 0, v___x_548_);
v___x_554_ = v___x_539_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_k_543_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_v_544_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
}
else
{
lean_object* v_k_568_; lean_object* v_v_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v_k_568_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_k_568_);
v_v_569_ = lean_ctor_get(v___x_425_, 1);
lean_inc(v_v_569_);
lean_dec_ref(v___x_425_);
v___x_570_ = lean_unsigned_to_nat(2u);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 4, v_r_273_);
lean_ctor_set(v___x_423_, 3, v_l_89_);
lean_ctor_set(v___x_423_, 2, v_v_569_);
lean_ctor_set(v___x_423_, 1, v_k_568_);
lean_ctor_set(v___x_423_, 0, v___x_570_);
v___x_572_ = v___x_423_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_k_568_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_v_569_);
lean_ctor_set(v_reuseFailAlloc_573_, 3, v_l_89_);
lean_ctor_set(v_reuseFailAlloc_573_, 4, v_r_273_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
}
}
else
{
return v_l_89_;
}
}
else
{
return v_r_90_;
}
}
default: 
{
lean_object* v_impl_580_; lean_object* v___x_581_; 
v_impl_580_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___redArg(v_k_85_, v_r_90_);
v___x_581_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_580_) == 0)
{
if (lean_obj_tag(v_l_89_) == 0)
{
lean_object* v_size_582_; lean_object* v_size_583_; lean_object* v_k_584_; lean_object* v_v_585_; lean_object* v_l_586_; lean_object* v_r_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v_size_582_ = lean_ctor_get(v_impl_580_, 0);
lean_inc(v_size_582_);
v_size_583_ = lean_ctor_get(v_l_89_, 0);
v_k_584_ = lean_ctor_get(v_l_89_, 1);
v_v_585_ = lean_ctor_get(v_l_89_, 2);
v_l_586_ = lean_ctor_get(v_l_89_, 3);
v_r_587_ = lean_ctor_get(v_l_89_, 4);
lean_inc(v_r_587_);
v___x_588_ = lean_unsigned_to_nat(3u);
v___x_589_ = lean_nat_mul(v___x_588_, v_size_582_);
v___x_590_ = lean_nat_dec_lt(v___x_589_, v_size_583_);
lean_dec(v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
lean_dec(v_r_587_);
v___x_591_ = lean_nat_add(v___x_581_, v_size_583_);
v___x_592_ = lean_nat_add(v___x_591_, v_size_582_);
lean_dec(v_size_582_);
lean_dec(v___x_591_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v_impl_580_);
lean_ctor_set(v___x_92_, 0, v___x_592_);
v___x_594_ = v___x_92_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v_l_89_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v_impl_580_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
else
{
lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_661_; 
lean_inc(v_l_586_);
lean_inc(v_v_585_);
lean_inc(v_k_584_);
lean_inc(v_size_583_);
v_isSharedCheck_661_ = !lean_is_exclusive(v_l_89_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; lean_object* v_unused_663_; lean_object* v_unused_664_; lean_object* v_unused_665_; lean_object* v_unused_666_; 
v_unused_662_ = lean_ctor_get(v_l_89_, 4);
lean_dec(v_unused_662_);
v_unused_663_ = lean_ctor_get(v_l_89_, 3);
lean_dec(v_unused_663_);
v_unused_664_ = lean_ctor_get(v_l_89_, 2);
lean_dec(v_unused_664_);
v_unused_665_ = lean_ctor_get(v_l_89_, 1);
lean_dec(v_unused_665_);
v_unused_666_ = lean_ctor_get(v_l_89_, 0);
lean_dec(v_unused_666_);
v___x_597_ = v_l_89_;
v_isShared_598_ = v_isSharedCheck_661_;
goto v_resetjp_596_;
}
else
{
lean_dec(v_l_89_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_661_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v_size_599_; lean_object* v_size_600_; lean_object* v_k_601_; lean_object* v_v_602_; lean_object* v_l_603_; lean_object* v_r_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v_size_599_ = lean_ctor_get(v_l_586_, 0);
v_size_600_ = lean_ctor_get(v_r_587_, 0);
v_k_601_ = lean_ctor_get(v_r_587_, 1);
v_v_602_ = lean_ctor_get(v_r_587_, 2);
v_l_603_ = lean_ctor_get(v_r_587_, 3);
v_r_604_ = lean_ctor_get(v_r_587_, 4);
v___x_605_ = lean_unsigned_to_nat(2u);
v___x_606_ = lean_nat_mul(v___x_605_, v_size_599_);
v___x_607_ = lean_nat_dec_lt(v_size_600_, v___x_606_);
lean_dec(v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_636_; 
lean_inc(v_r_604_);
lean_inc(v_l_603_);
lean_inc(v_v_602_);
lean_inc(v_k_601_);
v_isSharedCheck_636_ = !lean_is_exclusive(v_r_587_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; lean_object* v_unused_638_; lean_object* v_unused_639_; lean_object* v_unused_640_; lean_object* v_unused_641_; 
v_unused_637_ = lean_ctor_get(v_r_587_, 4);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v_r_587_, 3);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v_r_587_, 2);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_r_587_, 1);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v_r_587_, 0);
lean_dec(v_unused_641_);
v___x_609_ = v_r_587_;
v_isShared_610_ = v_isSharedCheck_636_;
goto v_resetjp_608_;
}
else
{
lean_dec(v_r_587_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_636_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___x_624_; lean_object* v___y_626_; 
v___x_611_ = lean_nat_add(v___x_581_, v_size_583_);
lean_dec(v_size_583_);
v___x_612_ = lean_nat_add(v___x_611_, v_size_582_);
lean_dec(v___x_611_);
v___x_624_ = lean_nat_add(v___x_581_, v_size_599_);
if (lean_obj_tag(v_l_603_) == 0)
{
lean_object* v_size_634_; 
v_size_634_ = lean_ctor_get(v_l_603_, 0);
lean_inc(v_size_634_);
v___y_626_ = v_size_634_;
goto v___jp_625_;
}
else
{
lean_object* v___x_635_; 
v___x_635_ = lean_unsigned_to_nat(0u);
v___y_626_ = v___x_635_;
goto v___jp_625_;
}
v___jp_613_:
{
lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_617_ = lean_nat_add(v___y_614_, v___y_616_);
lean_dec(v___y_616_);
lean_dec(v___y_614_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 4, v_impl_580_);
lean_ctor_set(v___x_609_, 3, v_r_604_);
lean_ctor_set(v___x_609_, 2, v_v_88_);
lean_ctor_set(v___x_609_, 1, v_k_87_);
lean_ctor_set(v___x_609_, 0, v___x_617_);
v___x_619_ = v___x_609_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_623_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_623_, 3, v_r_604_);
lean_ctor_set(v_reuseFailAlloc_623_, 4, v_impl_580_);
v___x_619_ = v_reuseFailAlloc_623_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_621_; 
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 4, v___x_619_);
lean_ctor_set(v___x_597_, 3, v___y_615_);
lean_ctor_set(v___x_597_, 2, v_v_602_);
lean_ctor_set(v___x_597_, 1, v_k_601_);
lean_ctor_set(v___x_597_, 0, v___x_612_);
v___x_621_ = v___x_597_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_k_601_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v_v_602_);
lean_ctor_set(v_reuseFailAlloc_622_, 3, v___y_615_);
lean_ctor_set(v_reuseFailAlloc_622_, 4, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
v___jp_625_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = lean_nat_add(v___x_624_, v___y_626_);
lean_dec(v___y_626_);
lean_dec(v___x_624_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v_l_603_);
lean_ctor_set(v___x_92_, 3, v_l_586_);
lean_ctor_set(v___x_92_, 2, v_v_585_);
lean_ctor_set(v___x_92_, 1, v_k_584_);
lean_ctor_set(v___x_92_, 0, v___x_627_);
v___x_629_ = v___x_92_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_633_, 3, v_l_586_);
lean_ctor_set(v_reuseFailAlloc_633_, 4, v_l_603_);
v___x_629_ = v_reuseFailAlloc_633_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_630_; 
v___x_630_ = lean_nat_add(v___x_581_, v_size_582_);
lean_dec(v_size_582_);
if (lean_obj_tag(v_r_604_) == 0)
{
lean_object* v_size_631_; 
v_size_631_ = lean_ctor_get(v_r_604_, 0);
lean_inc(v_size_631_);
v___y_614_ = v___x_630_;
v___y_615_ = v___x_629_;
v___y_616_ = v_size_631_;
goto v___jp_613_;
}
else
{
lean_object* v___x_632_; 
v___x_632_ = lean_unsigned_to_nat(0u);
v___y_614_ = v___x_630_;
v___y_615_ = v___x_629_;
v___y_616_ = v___x_632_;
goto v___jp_613_;
}
}
}
}
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
lean_del_object(v___x_92_);
v___x_642_ = lean_nat_add(v___x_581_, v_size_583_);
lean_dec(v_size_583_);
v___x_643_ = lean_nat_add(v___x_642_, v_size_582_);
lean_dec(v___x_642_);
v___x_644_ = lean_nat_add(v___x_581_, v_size_582_);
lean_dec(v_size_582_);
v___x_645_ = lean_nat_add(v___x_644_, v_size_600_);
lean_dec(v___x_644_);
lean_inc_ref(v_impl_580_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 4, v_impl_580_);
lean_ctor_set(v___x_597_, 3, v_r_587_);
lean_ctor_set(v___x_597_, 2, v_v_88_);
lean_ctor_set(v___x_597_, 1, v_k_87_);
lean_ctor_set(v___x_597_, 0, v___x_645_);
v___x_647_ = v___x_597_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_660_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_660_, 3, v_r_587_);
lean_ctor_set(v_reuseFailAlloc_660_, 4, v_impl_580_);
v___x_647_ = v_reuseFailAlloc_660_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
v_isSharedCheck_654_ = !lean_is_exclusive(v_impl_580_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; lean_object* v_unused_656_; lean_object* v_unused_657_; lean_object* v_unused_658_; lean_object* v_unused_659_; 
v_unused_655_ = lean_ctor_get(v_impl_580_, 4);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v_impl_580_, 3);
lean_dec(v_unused_656_);
v_unused_657_ = lean_ctor_get(v_impl_580_, 2);
lean_dec(v_unused_657_);
v_unused_658_ = lean_ctor_get(v_impl_580_, 1);
lean_dec(v_unused_658_);
v_unused_659_ = lean_ctor_get(v_impl_580_, 0);
lean_dec(v_unused_659_);
v___x_649_ = v_impl_580_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_dec(v_impl_580_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 4, v___x_647_);
lean_ctor_set(v___x_649_, 3, v_l_586_);
lean_ctor_set(v___x_649_, 2, v_v_585_);
lean_ctor_set(v___x_649_, 1, v_k_584_);
lean_ctor_set(v___x_649_, 0, v___x_643_);
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_k_584_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_v_585_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v_l_586_);
lean_ctor_set(v_reuseFailAlloc_653_, 4, v___x_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v_size_667_ = lean_ctor_get(v_impl_580_, 0);
lean_inc(v_size_667_);
v___x_668_ = lean_nat_add(v___x_581_, v_size_667_);
lean_dec(v_size_667_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v_impl_580_);
lean_ctor_set(v___x_92_, 0, v___x_668_);
v___x_670_ = v___x_92_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_671_, 3, v_l_89_);
lean_ctor_set(v_reuseFailAlloc_671_, 4, v_impl_580_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
else
{
if (lean_obj_tag(v_l_89_) == 0)
{
lean_object* v_l_672_; 
v_l_672_ = lean_ctor_get(v_l_89_, 3);
if (lean_obj_tag(v_l_672_) == 0)
{
lean_object* v_r_673_; 
lean_inc_ref(v_l_672_);
v_r_673_ = lean_ctor_get(v_l_89_, 4);
lean_inc(v_r_673_);
if (lean_obj_tag(v_r_673_) == 0)
{
lean_object* v_size_674_; lean_object* v_k_675_; lean_object* v_v_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_689_; 
v_size_674_ = lean_ctor_get(v_l_89_, 0);
v_k_675_ = lean_ctor_get(v_l_89_, 1);
v_v_676_ = lean_ctor_get(v_l_89_, 2);
v_isSharedCheck_689_ = !lean_is_exclusive(v_l_89_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; lean_object* v_unused_691_; 
v_unused_690_ = lean_ctor_get(v_l_89_, 4);
lean_dec(v_unused_690_);
v_unused_691_ = lean_ctor_get(v_l_89_, 3);
lean_dec(v_unused_691_);
v___x_678_ = v_l_89_;
v_isShared_679_ = v_isSharedCheck_689_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_v_676_);
lean_inc(v_k_675_);
lean_inc(v_size_674_);
lean_dec(v_l_89_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_689_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_size_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
v_size_680_ = lean_ctor_get(v_r_673_, 0);
v___x_681_ = lean_nat_add(v___x_581_, v_size_674_);
lean_dec(v_size_674_);
v___x_682_ = lean_nat_add(v___x_581_, v_size_680_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 4, v_impl_580_);
lean_ctor_set(v___x_678_, 3, v_r_673_);
lean_ctor_set(v___x_678_, 2, v_v_88_);
lean_ctor_set(v___x_678_, 1, v_k_87_);
lean_ctor_set(v___x_678_, 0, v___x_682_);
v___x_684_ = v___x_678_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_688_, 3, v_r_673_);
lean_ctor_set(v_reuseFailAlloc_688_, 4, v_impl_580_);
v___x_684_ = v_reuseFailAlloc_688_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_686_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v___x_684_);
lean_ctor_set(v___x_92_, 3, v_l_672_);
lean_ctor_set(v___x_92_, 2, v_v_676_);
lean_ctor_set(v___x_92_, 1, v_k_675_);
lean_ctor_set(v___x_92_, 0, v___x_681_);
v___x_686_ = v___x_92_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_k_675_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v_v_676_);
lean_ctor_set(v_reuseFailAlloc_687_, 3, v_l_672_);
lean_ctor_set(v_reuseFailAlloc_687_, 4, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
else
{
lean_object* v_k_692_; lean_object* v_v_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_704_; 
v_k_692_ = lean_ctor_get(v_l_89_, 1);
v_v_693_ = lean_ctor_get(v_l_89_, 2);
v_isSharedCheck_704_ = !lean_is_exclusive(v_l_89_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; lean_object* v_unused_706_; lean_object* v_unused_707_; 
v_unused_705_ = lean_ctor_get(v_l_89_, 4);
lean_dec(v_unused_705_);
v_unused_706_ = lean_ctor_get(v_l_89_, 3);
lean_dec(v_unused_706_);
v_unused_707_ = lean_ctor_get(v_l_89_, 0);
lean_dec(v_unused_707_);
v___x_695_ = v_l_89_;
v_isShared_696_ = v_isSharedCheck_704_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_v_693_);
lean_inc(v_k_692_);
lean_dec(v_l_89_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_704_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_unsigned_to_nat(3u);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 3, v_r_673_);
lean_ctor_set(v___x_695_, 2, v_v_88_);
lean_ctor_set(v___x_695_, 1, v_k_87_);
lean_ctor_set(v___x_695_, 0, v___x_581_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_703_, 3, v_r_673_);
lean_ctor_set(v_reuseFailAlloc_703_, 4, v_r_673_);
v___x_699_ = v_reuseFailAlloc_703_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_701_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v___x_699_);
lean_ctor_set(v___x_92_, 3, v_l_672_);
lean_ctor_set(v___x_92_, 2, v_v_693_);
lean_ctor_set(v___x_92_, 1, v_k_692_);
lean_ctor_set(v___x_92_, 0, v___x_697_);
v___x_701_ = v___x_92_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_k_692_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_v_693_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_l_672_);
lean_ctor_set(v_reuseFailAlloc_702_, 4, v___x_699_);
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
else
{
lean_object* v_r_708_; 
v_r_708_ = lean_ctor_get(v_l_89_, 4);
lean_inc(v_r_708_);
if (lean_obj_tag(v_r_708_) == 0)
{
lean_object* v_k_709_; lean_object* v_v_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_733_; 
lean_inc(v_l_672_);
v_k_709_ = lean_ctor_get(v_l_89_, 1);
v_v_710_ = lean_ctor_get(v_l_89_, 2);
v_isSharedCheck_733_ = !lean_is_exclusive(v_l_89_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; lean_object* v_unused_735_; lean_object* v_unused_736_; 
v_unused_734_ = lean_ctor_get(v_l_89_, 4);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_l_89_, 3);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_l_89_, 0);
lean_dec(v_unused_736_);
v___x_712_ = v_l_89_;
v_isShared_713_ = v_isSharedCheck_733_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_v_710_);
lean_inc(v_k_709_);
lean_dec(v_l_89_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_733_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v_k_714_; lean_object* v_v_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_729_; 
v_k_714_ = lean_ctor_get(v_r_708_, 1);
v_v_715_ = lean_ctor_get(v_r_708_, 2);
v_isSharedCheck_729_ = !lean_is_exclusive(v_r_708_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; lean_object* v_unused_731_; lean_object* v_unused_732_; 
v_unused_730_ = lean_ctor_get(v_r_708_, 4);
lean_dec(v_unused_730_);
v_unused_731_ = lean_ctor_get(v_r_708_, 3);
lean_dec(v_unused_731_);
v_unused_732_ = lean_ctor_get(v_r_708_, 0);
lean_dec(v_unused_732_);
v___x_717_ = v_r_708_;
v_isShared_718_ = v_isSharedCheck_729_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_v_715_);
lean_inc(v_k_714_);
lean_dec(v_r_708_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_729_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_719_ = lean_unsigned_to_nat(3u);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 4, v_l_672_);
lean_ctor_set(v___x_717_, 3, v_l_672_);
lean_ctor_set(v___x_717_, 2, v_v_710_);
lean_ctor_set(v___x_717_, 1, v_k_709_);
lean_ctor_set(v___x_717_, 0, v___x_581_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_k_709_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v_v_710_);
lean_ctor_set(v_reuseFailAlloc_728_, 3, v_l_672_);
lean_ctor_set(v_reuseFailAlloc_728_, 4, v_l_672_);
v___x_721_ = v_reuseFailAlloc_728_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_723_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 4, v_l_672_);
lean_ctor_set(v___x_712_, 2, v_v_88_);
lean_ctor_set(v___x_712_, 1, v_k_87_);
lean_ctor_set(v___x_712_, 0, v___x_581_);
v___x_723_ = v___x_712_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_727_, 3, v_l_672_);
lean_ctor_set(v_reuseFailAlloc_727_, 4, v_l_672_);
v___x_723_ = v_reuseFailAlloc_727_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_725_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v___x_723_);
lean_ctor_set(v___x_92_, 3, v___x_721_);
lean_ctor_set(v___x_92_, 2, v_v_715_);
lean_ctor_set(v___x_92_, 1, v_k_714_);
lean_ctor_set(v___x_92_, 0, v___x_719_);
v___x_725_ = v___x_92_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_k_714_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_v_715_);
lean_ctor_set(v_reuseFailAlloc_726_, 3, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_726_, 4, v___x_723_);
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
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = lean_unsigned_to_nat(2u);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v_r_708_);
lean_ctor_set(v___x_92_, 0, v___x_737_);
v___x_739_ = v___x_92_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_740_, 3, v_l_89_);
lean_ctor_set(v_reuseFailAlloc_740_, 4, v_r_708_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
else
{
lean_object* v___x_742_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v_l_89_);
lean_ctor_set(v___x_92_, 0, v___x_581_);
v___x_742_ = v___x_92_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_k_87_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v_v_88_);
lean_ctor_set(v_reuseFailAlloc_743_, 3, v_l_89_);
lean_ctor_set(v_reuseFailAlloc_743_, 4, v_l_89_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
}
}
else
{
return v_t_86_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___redArg___boxed(lean_object* v_k_746_, lean_object* v_t_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___redArg(v_k_746_, v_t_747_);
lean_dec(v_k_746_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3_spec__5(lean_object* v_init_749_, lean_object* v_x_750_){
_start:
{
if (lean_obj_tag(v_x_750_) == 0)
{
lean_object* v_k_751_; lean_object* v_l_752_; lean_object* v_r_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_k_751_ = lean_ctor_get(v_x_750_, 1);
v_l_752_ = lean_ctor_get(v_x_750_, 3);
v_r_753_ = lean_ctor_get(v_x_750_, 4);
v___x_754_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3_spec__5(v_init_749_, v_l_752_);
v___x_755_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___redArg(v_k_751_, v___x_754_);
v_init_749_ = v___x_755_;
v_x_750_ = v_r_753_;
goto _start;
}
else
{
return v_init_749_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3_spec__5___boxed(lean_object* v_init_757_, lean_object* v_x_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3_spec__5(v_init_757_, v_x_758_);
lean_dec(v_x_758_);
return v_res_759_;
}
}
LEAN_EXPORT double l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1_spec__2(lean_object* v_weight_760_, double v_init_761_, lean_object* v_x_762_){
_start:
{
if (lean_obj_tag(v_x_762_) == 0)
{
lean_object* v_k_763_; lean_object* v_l_764_; lean_object* v_r_765_; double v___x_766_; lean_object* v___x_767_; double v___x_768_; double v___x_769_; 
v_k_763_ = lean_ctor_get(v_x_762_, 1);
lean_inc(v_k_763_);
v_l_764_ = lean_ctor_get(v_x_762_, 3);
lean_inc(v_l_764_);
v_r_765_ = lean_ctor_get(v_x_762_, 4);
lean_inc(v_r_765_);
lean_dec_ref_known(v_x_762_, 5);
lean_inc_ref_n(v_weight_760_, 2);
v___x_766_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1_spec__2(v_weight_760_, v_init_761_, v_l_764_);
v___x_767_ = lean_apply_1(v_weight_760_, v_k_763_);
v___x_768_ = lean_unbox_float(v___x_767_);
lean_dec_ref(v___x_767_);
v___x_769_ = lean_float_add(v___x_766_, v___x_768_);
v_init_761_ = v___x_769_;
v_x_762_ = v_r_765_;
goto _start;
}
else
{
lean_dec_ref(v_weight_760_);
return v_init_761_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1_spec__2___boxed(lean_object* v_weight_771_, lean_object* v_init_772_, lean_object* v_x_773_){
_start:
{
double v_init_boxed_774_; double v_res_775_; lean_object* v_r_776_; 
v_init_boxed_774_ = lean_unbox_float(v_init_772_);
lean_dec_ref(v_init_772_);
v_res_775_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1_spec__2(v_weight_771_, v_init_boxed_774_, v_x_773_);
v_r_776_ = lean_box_float(v_res_775_);
return v_r_776_;
}
}
static double _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0(void){
_start:
{
lean_object* v___x_777_; double v___x_778_; 
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = lean_float_of_nat(v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT double l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore(lean_object* v_weight_779_, lean_object* v_relevant_780_, lean_object* v_candidate_781_){
_start:
{
lean_object* v___x_782_; lean_object* v_R_783_; lean_object* v___y_785_; lean_object* v___x_791_; 
v___x_782_ = l_Lean_NameSet_empty;
v_R_783_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0_spec__0(v_candidate_781_, v___x_782_, v_relevant_780_);
v___x_791_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3_spec__5(v_candidate_781_, v_R_783_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_size_792_; 
v_size_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_size_792_);
lean_dec_ref_known(v___x_791_, 5);
v___y_785_ = v_size_792_;
goto v___jp_784_;
}
else
{
lean_object* v___x_793_; 
v___x_793_ = lean_unsigned_to_nat(0u);
v___y_785_ = v___x_793_;
goto v___jp_784_;
}
v___jp_784_:
{
double v_R_x27_786_; double v___x_787_; double v_M_788_; double v___x_789_; double v___x_790_; 
v_R_x27_786_ = lean_float_of_nat(v___y_785_);
v___x_787_ = lean_float_once(&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0, &l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0_once, _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0);
v_M_788_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1_spec__2(v_weight_779_, v___x_787_, v_R_783_);
v___x_789_ = lean_float_add(v_M_788_, v_R_x27_786_);
v___x_790_ = lean_float_div(v_M_788_, v___x_789_);
return v___x_790_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___boxed(lean_object* v_weight_794_, lean_object* v_relevant_795_, lean_object* v_candidate_796_){
_start:
{
double v_res_797_; lean_object* v_r_798_; 
v_res_797_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore(v_weight_794_, v_relevant_795_, v_candidate_796_);
v_r_798_ = lean_box_float(v_res_797_);
return v_r_798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0(lean_object* v_candidate_799_, lean_object* v_init_800_, lean_object* v_t_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0_spec__0(v_candidate_799_, v_init_800_, v_t_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0___boxed(lean_object* v_candidate_803_, lean_object* v_init_804_, lean_object* v_t_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0(v_candidate_803_, v_init_804_, v_t_805_);
lean_dec(v_candidate_803_);
return v_res_806_;
}
}
LEAN_EXPORT double l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1(lean_object* v_weight_807_, double v_init_808_, lean_object* v_t_809_){
_start:
{
double v___x_810_; 
v___x_810_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1_spec__2(v_weight_807_, v_init_808_, v_t_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1___boxed(lean_object* v_weight_811_, lean_object* v_init_812_, lean_object* v_t_813_){
_start:
{
double v_init_boxed_814_; double v_res_815_; lean_object* v_r_816_; 
v_init_boxed_814_ = lean_unbox_float(v_init_812_);
lean_dec_ref(v_init_812_);
v_res_815_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1(v_weight_811_, v_init_boxed_814_, v_t_813_);
v_r_816_ = lean_box_float(v_res_815_);
return v_r_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2(lean_object* v_00_u03b2_817_, lean_object* v_k_818_, lean_object* v_t_819_, lean_object* v_h_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___redArg(v_k_818_, v_t_819_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___boxed(lean_object* v_00_u03b2_822_, lean_object* v_k_823_, lean_object* v_t_824_, lean_object* v_h_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2(v_00_u03b2_822_, v_k_823_, v_t_824_, v_h_825_);
lean_dec(v_k_823_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3(lean_object* v_init_827_, lean_object* v_t_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3_spec__5(v_init_827_, v_t_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3___boxed(lean_object* v_init_830_, lean_object* v_t_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3(v_init_830_, v_t_831_);
lean_dec(v_t_831_);
return v_res_832_;
}
}
static double _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__0(void){
_start:
{
lean_object* v___x_833_; uint8_t v___x_834_; lean_object* v___x_835_; double v___x_836_; 
v___x_833_ = lean_unsigned_to_nat(1u);
v___x_834_ = 1;
v___x_835_ = lean_unsigned_to_nat(10u);
v___x_836_ = l_Float_ofScientific(v___x_835_, v___x_834_, v___x_833_);
return v___x_836_;
}
}
static double _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__1(void){
_start:
{
lean_object* v___x_837_; uint8_t v___x_838_; lean_object* v___x_839_; double v___x_840_; 
v___x_837_ = lean_unsigned_to_nat(1u);
v___x_838_ = 1;
v___x_839_ = lean_unsigned_to_nat(20u);
v___x_840_ = l_Float_ofScientific(v___x_839_, v___x_838_, v___x_837_);
return v___x_840_;
}
}
LEAN_EXPORT double l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction(lean_object* v_n_841_){
_start:
{
double v___x_842_; double v___x_843_; lean_object* v___x_844_; double v___x_845_; double v___x_846_; double v___x_847_; double v___x_848_; 
v___x_842_ = lean_float_once(&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__0, &l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__0_once, _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__0);
v___x_843_ = lean_float_once(&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__1, &l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__1_once, _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__1);
v___x_844_ = lean_nat_log2(v_n_841_);
v___x_845_ = lean_float_of_nat(v___x_844_);
v___x_846_ = lean_float_add(v___x_845_, v___x_842_);
v___x_847_ = lean_float_div(v___x_843_, v___x_846_);
v___x_848_ = lean_float_add(v___x_842_, v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___boxed(lean_object* v_n_849_){
_start:
{
double v_res_850_; lean_object* v_r_851_; 
v_res_850_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction(v_n_849_);
lean_dec(v_n_849_);
v_r_851_ = lean_box_float(v_res_850_);
return v_r_851_;
}
}
LEAN_EXPORT double l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore___lam__0(lean_object* v_frequency_852_, lean_object* v_n_853_){
_start:
{
lean_object* v___x_854_; double v___x_855_; 
v___x_854_ = lean_apply_1(v_frequency_852_, v_n_853_);
v___x_855_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction(v___x_854_);
lean_dec(v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore___lam__0___boxed(lean_object* v_frequency_856_, lean_object* v_n_857_){
_start:
{
double v_res_858_; lean_object* v_r_859_; 
v_res_858_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore___lam__0(v_frequency_856_, v_n_857_);
v_r_859_ = lean_box_float(v_res_858_);
return v_r_859_;
}
}
LEAN_EXPORT double l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore(lean_object* v_frequency_860_, lean_object* v_relevant_861_, lean_object* v_candidate_862_){
_start:
{
lean_object* v___f_863_; double v___x_864_; 
v___f_863_ = lean_alloc_closure((void*)(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore___lam__0___boxed), 2, 1);
lean_closure_set(v___f_863_, 0, v_frequency_860_);
v___x_864_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore(v___f_863_, v_relevant_861_, v_candidate_862_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore___boxed(lean_object* v_frequency_865_, lean_object* v_relevant_866_, lean_object* v_candidate_867_){
_start:
{
double v_res_868_; lean_object* v_r_869_; 
v_res_868_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore(v_frequency_865_, v_relevant_866_, v_candidate_867_);
v_r_869_ = lean_box_float(v_res_868_);
return v_r_869_;
}
}
static double _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0___closed__0(void){
_start:
{
lean_object* v___x_870_; double v___x_871_; 
v___x_870_ = lean_unsigned_to_nat(1u);
v___x_871_ = lean_float_of_nat(v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT double l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0(lean_object* v_x_872_){
_start:
{
double v___x_873_; 
v___x_873_ = lean_float_once(&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0___closed__0, &l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0___closed__0_once, _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0___closed__0);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0___boxed(lean_object* v_x_874_){
_start:
{
double v_res_875_; lean_object* v_r_876_; 
v_res_875_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0(v_x_874_);
lean_dec(v_x_874_);
v_r_876_ = lean_box_float(v_res_875_);
return v_r_876_;
}
}
LEAN_EXPORT double l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore(lean_object* v_relevant_878_, lean_object* v_candidate_879_){
_start:
{
lean_object* v___f_880_; double v___x_881_; 
v___f_880_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___closed__0));
v___x_881_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore(v___f_880_, v_relevant_878_, v_candidate_879_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___boxed(lean_object* v_relevant_882_, lean_object* v_candidate_883_){
_start:
{
double v_res_884_; lean_object* v_r_885_; 
v_res_884_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore(v_relevant_882_, v_candidate_883_);
v_r_885_ = lean_box_float(v_res_884_);
return v_r_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___lam__0(lean_object* v_accept_886_, lean_object* v_x_887_, lean_object* v_y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___x_893_; 
lean_inc(v___y_891_);
lean_inc_ref(v___y_890_);
lean_inc_ref(v_y_888_);
v___x_893_ = lean_apply_4(v_accept_886_, v_y_888_, v___y_890_, v___y_891_, lean_box(0));
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_911_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_911_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_911_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_911_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_a_899_; uint8_t v___x_906_; 
v___x_906_ = lean_unbox(v_a_894_);
lean_dec(v_a_894_);
if (v___x_906_ == 0)
{
lean_dec_ref(v_y_888_);
lean_dec(v_x_887_);
v_a_899_ = v___y_889_;
goto v___jp_898_;
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_907_ = l_Lean_ConstantInfo_type(v_y_888_);
lean_dec_ref(v_y_888_);
v___x_908_ = l_Lean_Expr_getUsedConstantsAsSet(v___x_907_);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v_x_887_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_array_push(v___y_889_, v___x_909_);
v_a_899_ = v___x_910_;
goto v___jp_898_;
}
v___jp_898_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_900_ = lean_box(0);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v_a_899_);
v___x_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_902_);
v___x_904_ = v___x_896_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v___y_889_);
lean_dec_ref(v_y_888_);
lean_dec(v_x_887_);
v_a_912_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_893_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_893_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___lam__0___boxed(lean_object* v_accept_920_, lean_object* v_x_921_, lean_object* v_y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___lam__0(v_accept_920_, v_x_921_, v_y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
return v_res_927_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__2(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__1));
v___x_932_ = l_Lean_MessageData_ofFormat(v___x_931_);
return v___x_932_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__3(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_box(1);
v___x_934_ = l_Lean_MessageData_ofFormat(v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8(lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
if (lean_obj_tag(v_a_935_) == 0)
{
lean_object* v___x_937_; 
v___x_937_ = l_List_reverse___redArg(v_a_936_);
return v___x_937_;
}
else
{
lean_object* v_head_938_; lean_object* v_tail_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_966_; 
v_head_938_ = lean_ctor_get(v_a_935_, 0);
v_tail_939_ = lean_ctor_get(v_a_935_, 1);
v_isSharedCheck_966_ = !lean_is_exclusive(v_a_935_);
if (v_isSharedCheck_966_ == 0)
{
v___x_941_ = v_a_935_;
v_isShared_942_ = v_isSharedCheck_966_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_tail_939_);
lean_inc(v_head_938_);
lean_dec(v_a_935_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_966_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_fst_943_; lean_object* v_snd_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_965_; 
v_fst_943_ = lean_ctor_get(v_head_938_, 0);
v_snd_944_ = lean_ctor_get(v_head_938_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_head_938_);
if (v_isSharedCheck_965_ == 0)
{
v___x_946_ = v_head_938_;
v_isShared_947_ = v_isSharedCheck_965_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_snd_944_);
lean_inc(v_fst_943_);
lean_dec(v_head_938_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_965_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_948_ = l_Lean_MessageData_ofName(v_fst_943_);
v___x_949_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__2, &l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__2);
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 7);
lean_ctor_set(v___x_946_, 1, v___x_949_);
lean_ctor_set(v___x_946_, 0, v___x_948_);
v___x_951_ = v___x_946_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v___x_949_);
v___x_951_ = v_reuseFailAlloc_964_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; lean_object* v___x_953_; double v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_952_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__3, &l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__3);
v___x_953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_unbox_float(v_snd_944_);
lean_dec(v_snd_944_);
v___x_955_ = lean_float_to_string(v___x_954_);
v___x_956_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
v___x_957_ = l_Lean_MessageData_ofFormat(v___x_956_);
v___x_958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_953_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = l_Lean_MessageData_paren(v___x_958_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v_a_936_);
lean_ctor_set(v___x_941_, 0, v___x_959_);
v___x_961_ = v___x_941_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_a_936_);
v___x_961_ = v_reuseFailAlloc_963_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
v_a_935_ = v_tail_939_;
v_a_936_ = v___x_961_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__2(double v___x_967_, lean_object* v_as_968_, size_t v_sz_969_, size_t v_i_970_, lean_object* v_b_971_){
_start:
{
lean_object* v_a_973_; uint8_t v___x_977_; 
v___x_977_ = lean_usize_dec_lt(v_i_970_, v_sz_969_);
if (v___x_977_ == 0)
{
return v_b_971_;
}
else
{
lean_object* v_a_978_; lean_object* v_snd_979_; lean_object* v_snd_980_; lean_object* v_fst_981_; lean_object* v_snd_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_996_; 
v_a_978_ = lean_array_uget_borrowed(v_as_968_, v_i_970_);
v_snd_979_ = lean_ctor_get(v_a_978_, 1);
v_snd_980_ = lean_ctor_get(v_snd_979_, 1);
v_fst_981_ = lean_ctor_get(v_b_971_, 0);
v_snd_982_ = lean_ctor_get(v_b_971_, 1);
v_isSharedCheck_996_ = !lean_is_exclusive(v_b_971_);
if (v_isSharedCheck_996_ == 0)
{
v___x_984_ = v_b_971_;
v_isShared_985_ = v_isSharedCheck_996_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_snd_982_);
lean_inc(v_fst_981_);
lean_dec(v_b_971_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_996_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
double v___x_986_; uint8_t v___x_987_; 
v___x_986_ = lean_unbox_float(v_snd_980_);
v___x_987_ = lean_float_decLe(v___x_967_, v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; lean_object* v___x_990_; 
lean_inc(v_a_978_);
v___x_988_ = lean_array_push(v_snd_982_, v_a_978_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 1, v___x_988_);
v___x_990_ = v___x_984_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_fst_981_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
v_a_973_ = v___x_990_;
goto v___jp_972_;
}
}
else
{
lean_object* v___x_992_; lean_object* v___x_994_; 
lean_inc(v_a_978_);
v___x_992_ = lean_array_push(v_fst_981_, v_a_978_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_992_);
v___x_994_ = v___x_984_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_snd_982_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
v_a_973_ = v___x_994_;
goto v___jp_972_;
}
}
}
}
v___jp_972_:
{
size_t v___x_974_; size_t v___x_975_; 
v___x_974_ = ((size_t)1ULL);
v___x_975_ = lean_usize_add(v_i_970_, v___x_974_);
v_i_970_ = v___x_975_;
v_b_971_ = v_a_973_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__2___boxed(lean_object* v___x_997_, lean_object* v_as_998_, lean_object* v_sz_999_, lean_object* v_i_1000_, lean_object* v_b_1001_){
_start:
{
double v___x_15616__boxed_1002_; size_t v_sz_boxed_1003_; size_t v_i_boxed_1004_; lean_object* v_res_1005_; 
v___x_15616__boxed_1002_ = lean_unbox_float(v___x_997_);
lean_dec_ref(v___x_997_);
v_sz_boxed_1003_ = lean_unbox_usize(v_sz_999_);
lean_dec(v_sz_999_);
v_i_boxed_1004_ = lean_unbox_usize(v_i_1000_);
lean_dec(v_i_1000_);
v_res_1005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__2(v___x_15616__boxed_1002_, v_as_998_, v_sz_boxed_1003_, v_i_boxed_1004_, v_b_1001_);
lean_dec_ref(v_as_998_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__7(size_t v_sz_1006_, size_t v_i_1007_, lean_object* v_bs_1008_){
_start:
{
uint8_t v___x_1009_; 
v___x_1009_ = lean_usize_dec_lt(v_i_1007_, v_sz_1006_);
if (v___x_1009_ == 0)
{
return v_bs_1008_;
}
else
{
lean_object* v_v_1010_; lean_object* v_snd_1011_; lean_object* v_fst_1012_; lean_object* v_snd_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1026_; 
v_v_1010_ = lean_array_uget_borrowed(v_bs_1008_, v_i_1007_);
v_snd_1011_ = lean_ctor_get(v_v_1010_, 1);
lean_inc(v_snd_1011_);
v_fst_1012_ = lean_ctor_get(v_v_1010_, 0);
lean_inc(v_fst_1012_);
v_snd_1013_ = lean_ctor_get(v_snd_1011_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_snd_1011_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; 
v_unused_1027_ = lean_ctor_get(v_snd_1011_, 0);
lean_dec(v_unused_1027_);
v___x_1015_ = v_snd_1011_;
v_isShared_1016_ = v_isSharedCheck_1026_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_snd_1013_);
lean_dec(v_snd_1011_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1026_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v_bs_x27_1018_; lean_object* v___x_1020_; 
v___x_1017_ = lean_unsigned_to_nat(0u);
v_bs_x27_1018_ = lean_array_uset(v_bs_1008_, v_i_1007_, v___x_1017_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v_fst_1012_);
v___x_1020_ = v___x_1015_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_fst_1012_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_snd_1013_);
v___x_1020_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
size_t v___x_1021_; size_t v___x_1022_; lean_object* v___x_1023_; 
v___x_1021_ = ((size_t)1ULL);
v___x_1022_ = lean_usize_add(v_i_1007_, v___x_1021_);
v___x_1023_ = lean_array_uset(v_bs_x27_1018_, v_i_1007_, v___x_1020_);
v_i_1007_ = v___x_1022_;
v_bs_1008_ = v___x_1023_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__7___boxed(lean_object* v_sz_1028_, lean_object* v_i_1029_, lean_object* v_bs_1030_){
_start:
{
size_t v_sz_boxed_1031_; size_t v_i_boxed_1032_; lean_object* v_res_1033_; 
v_sz_boxed_1031_ = lean_unbox_usize(v_sz_1028_);
lean_dec(v_sz_1028_);
v_i_boxed_1032_ = lean_unbox_usize(v_i_1029_);
lean_dec(v_i_1029_);
v_res_1033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__7(v_sz_boxed_1031_, v_i_boxed_1032_, v_bs_1030_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__11(lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
if (lean_obj_tag(v_a_1034_) == 0)
{
lean_object* v___x_1036_; 
v___x_1036_ = l_List_reverse___redArg(v_a_1035_);
return v___x_1036_;
}
else
{
lean_object* v_head_1037_; lean_object* v_tail_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1047_; 
v_head_1037_ = lean_ctor_get(v_a_1034_, 0);
v_tail_1038_ = lean_ctor_get(v_a_1034_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_a_1034_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1040_ = v_a_1034_;
v_isShared_1041_ = v_isSharedCheck_1047_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_tail_1038_);
lean_inc(v_head_1037_);
lean_dec(v_a_1034_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1047_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1042_ = l_Lean_MessageData_ofName(v_head_1037_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 1, v_a_1035_);
lean_ctor_set(v___x_1040_, 0, v___x_1042_);
v___x_1044_ = v___x_1040_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_a_1035_);
v___x_1044_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
v_a_1034_ = v_tail_1038_;
v_a_1035_ = v___x_1044_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__5(lean_object* v_as_1048_, size_t v_i_1049_, size_t v_stop_1050_, lean_object* v_b_1051_){
_start:
{
uint8_t v___x_1052_; 
v___x_1052_ = lean_usize_dec_eq(v_i_1049_, v_stop_1050_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v_snd_1054_; lean_object* v_fst_1055_; lean_object* v_snd_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; double v___x_1059_; lean_object* v___x_1060_; size_t v___x_1061_; size_t v___x_1062_; 
v___x_1053_ = lean_array_uget_borrowed(v_as_1048_, v_i_1049_);
v_snd_1054_ = lean_ctor_get(v___x_1053_, 1);
v_fst_1055_ = lean_ctor_get(v___x_1053_, 0);
v_snd_1056_ = lean_ctor_get(v_snd_1054_, 1);
v___x_1057_ = lean_box(0);
lean_inc(v_fst_1055_);
v___x_1058_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_1058_, 0, v_fst_1055_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = lean_unbox_float(v_snd_1056_);
lean_ctor_set_float(v___x_1058_, sizeof(void*)*2, v___x_1059_);
v___x_1060_ = lean_array_push(v_b_1051_, v___x_1058_);
v___x_1061_ = ((size_t)1ULL);
v___x_1062_ = lean_usize_add(v_i_1049_, v___x_1061_);
v_i_1049_ = v___x_1062_;
v_b_1051_ = v___x_1060_;
goto _start;
}
else
{
return v_b_1051_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__5___boxed(lean_object* v_as_1064_, lean_object* v_i_1065_, lean_object* v_stop_1066_, lean_object* v_b_1067_){
_start:
{
size_t v_i_boxed_1068_; size_t v_stop_boxed_1069_; lean_object* v_res_1070_; 
v_i_boxed_1068_ = lean_unbox_usize(v_i_1065_);
lean_dec(v_i_1065_);
v_stop_boxed_1069_ = lean_unbox_usize(v_stop_1066_);
lean_dec(v_stop_1066_);
v_res_1070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__5(v_as_1064_, v_i_boxed_1068_, v_stop_boxed_1069_, v_b_1067_);
lean_dec_ref(v_as_1064_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__3(size_t v_sz_1071_, size_t v_i_1072_, lean_object* v_bs_1073_){
_start:
{
uint8_t v___x_1074_; 
v___x_1074_ = lean_usize_dec_lt(v_i_1072_, v_sz_1071_);
if (v___x_1074_ == 0)
{
return v_bs_1073_;
}
else
{
lean_object* v_v_1075_; lean_object* v_snd_1076_; lean_object* v_fst_1077_; lean_object* v_fst_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1091_; 
v_v_1075_ = lean_array_uget_borrowed(v_bs_1073_, v_i_1072_);
v_snd_1076_ = lean_ctor_get(v_v_1075_, 1);
lean_inc(v_snd_1076_);
v_fst_1077_ = lean_ctor_get(v_v_1075_, 0);
lean_inc(v_fst_1077_);
v_fst_1078_ = lean_ctor_get(v_snd_1076_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_snd_1076_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v_snd_1076_, 1);
lean_dec(v_unused_1092_);
v___x_1080_ = v_snd_1076_;
v_isShared_1081_ = v_isSharedCheck_1091_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_fst_1078_);
lean_dec(v_snd_1076_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1091_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v_bs_x27_1083_; lean_object* v___x_1085_; 
v___x_1082_ = lean_unsigned_to_nat(0u);
v_bs_x27_1083_ = lean_array_uset(v_bs_1073_, v_i_1072_, v___x_1082_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v_fst_1078_);
lean_ctor_set(v___x_1080_, 0, v_fst_1077_);
v___x_1085_ = v___x_1080_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_fst_1077_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_fst_1078_);
v___x_1085_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
size_t v___x_1086_; size_t v___x_1087_; lean_object* v___x_1088_; 
v___x_1086_ = ((size_t)1ULL);
v___x_1087_ = lean_usize_add(v_i_1072_, v___x_1086_);
v___x_1088_ = lean_array_uset(v_bs_x27_1083_, v_i_1072_, v___x_1085_);
v_i_1072_ = v___x_1087_;
v_bs_1073_ = v___x_1088_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__3___boxed(lean_object* v_sz_1093_, lean_object* v_i_1094_, lean_object* v_bs_1095_){
_start:
{
size_t v_sz_boxed_1096_; size_t v_i_boxed_1097_; lean_object* v_res_1098_; 
v_sz_boxed_1096_ = lean_unbox_usize(v_sz_1093_);
lean_dec(v_sz_1093_);
v_i_boxed_1097_ = lean_unbox_usize(v_i_1094_);
lean_dec(v_i_1094_);
v_res_1098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__3(v_sz_boxed_1096_, v_i_boxed_1097_, v_bs_1095_);
return v_res_1098_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__0(void){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1099_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__1(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__0);
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__1);
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
lean_ctor_set(v___x_1104_, 2, v___x_1103_);
lean_ctor_set(v___x_1104_, 3, v___x_1103_);
lean_ctor_set(v___x_1104_, 4, v___x_1102_);
lean_ctor_set(v___x_1104_, 5, v___x_1102_);
lean_ctor_set(v___x_1104_, 6, v___x_1102_);
lean_ctor_set(v___x_1104_, 7, v___x_1102_);
lean_ctor_set(v___x_1104_, 8, v___x_1102_);
lean_ctor_set(v___x_1104_, 9, v___x_1102_);
lean_ctor_set(v___x_1104_, 10, v___x_1102_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__3(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = lean_unsigned_to_nat(32u);
v___x_1106_ = lean_mk_empty_array_with_capacity(v___x_1105_);
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__4(void){
_start:
{
size_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1108_ = ((size_t)5ULL);
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = lean_unsigned_to_nat(32u);
v___x_1111_ = lean_mk_empty_array_with_capacity(v___x_1110_);
v___x_1112_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__3);
v___x_1113_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set(v___x_1113_, 1, v___x_1111_);
lean_ctor_set(v___x_1113_, 2, v___x_1109_);
lean_ctor_set(v___x_1113_, 3, v___x_1109_);
lean_ctor_set_usize(v___x_1113_, 4, v___x_1108_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__5(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1114_ = lean_box(1);
v___x_1115_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__4);
v___x_1116_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__1);
v___x_1117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v___x_1115_);
lean_ctor_set(v___x_1117_, 2, v___x_1114_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12(lean_object* v_msgData_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___x_1122_; lean_object* v_env_1123_; lean_object* v_options_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1122_ = lean_st_ref_get(v___y_1120_);
v_env_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc_ref(v_env_1123_);
lean_dec(v___x_1122_);
v_options_1124_ = lean_ctor_get(v___y_1119_, 2);
v___x_1125_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__2);
v___x_1126_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___closed__5);
lean_inc_ref(v_options_1124_);
v___x_1127_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1127_, 0, v_env_1123_);
lean_ctor_set(v___x_1127_, 1, v___x_1125_);
lean_ctor_set(v___x_1127_, 2, v___x_1126_);
lean_ctor_set(v___x_1127_, 3, v_options_1124_);
v___x_1128_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v_msgData_1118_);
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12___boxed(lean_object* v_msgData_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12(v_msgData_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9(lean_object* v_cls_1138_, lean_object* v_msg_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_ref_1143_; lean_object* v___x_1144_; lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1189_; 
v_ref_1143_ = lean_ctor_get(v___y_1140_, 5);
v___x_1144_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__12(v_msg_1139_, v___y_1140_, v___y_1141_);
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1189_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1189_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v_traceState_1150_; lean_object* v_env_1151_; lean_object* v_nextMacroScope_1152_; lean_object* v_ngen_1153_; lean_object* v_auxDeclNGen_1154_; lean_object* v_cache_1155_; lean_object* v_messages_1156_; lean_object* v_infoState_1157_; lean_object* v_snapshotTasks_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1188_; 
v___x_1149_ = lean_st_ref_take(v___y_1141_);
v_traceState_1150_ = lean_ctor_get(v___x_1149_, 4);
v_env_1151_ = lean_ctor_get(v___x_1149_, 0);
v_nextMacroScope_1152_ = lean_ctor_get(v___x_1149_, 1);
v_ngen_1153_ = lean_ctor_get(v___x_1149_, 2);
v_auxDeclNGen_1154_ = lean_ctor_get(v___x_1149_, 3);
v_cache_1155_ = lean_ctor_get(v___x_1149_, 5);
v_messages_1156_ = lean_ctor_get(v___x_1149_, 6);
v_infoState_1157_ = lean_ctor_get(v___x_1149_, 7);
v_snapshotTasks_1158_ = lean_ctor_get(v___x_1149_, 8);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1160_ = v___x_1149_;
v_isShared_1161_ = v_isSharedCheck_1188_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_snapshotTasks_1158_);
lean_inc(v_infoState_1157_);
lean_inc(v_messages_1156_);
lean_inc(v_cache_1155_);
lean_inc(v_traceState_1150_);
lean_inc(v_auxDeclNGen_1154_);
lean_inc(v_ngen_1153_);
lean_inc(v_nextMacroScope_1152_);
lean_inc(v_env_1151_);
lean_dec(v___x_1149_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1188_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
uint64_t v_tid_1162_; lean_object* v_traces_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1187_; 
v_tid_1162_ = lean_ctor_get_uint64(v_traceState_1150_, sizeof(void*)*1);
v_traces_1163_ = lean_ctor_get(v_traceState_1150_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_traceState_1150_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1165_ = v_traceState_1150_;
v_isShared_1166_ = v_isSharedCheck_1187_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_traces_1163_);
lean_dec(v_traceState_1150_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1187_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; double v___x_1168_; uint8_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_float_once(&l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0, &l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0_once, _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0);
v___x_1169_ = 0;
v___x_1170_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___closed__0));
v___x_1171_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1171_, 0, v_cls_1138_);
lean_ctor_set(v___x_1171_, 1, v___x_1167_);
lean_ctor_set(v___x_1171_, 2, v___x_1170_);
lean_ctor_set_float(v___x_1171_, sizeof(void*)*3, v___x_1168_);
lean_ctor_set_float(v___x_1171_, sizeof(void*)*3 + 8, v___x_1168_);
lean_ctor_set_uint8(v___x_1171_, sizeof(void*)*3 + 16, v___x_1169_);
v___x_1172_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___closed__1));
v___x_1173_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v_a_1145_);
lean_ctor_set(v___x_1173_, 2, v___x_1172_);
lean_inc(v_ref_1143_);
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v_ref_1143_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = l_Lean_PersistentArray_push___redArg(v_traces_1163_, v___x_1174_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1175_);
v___x_1177_ = v___x_1165_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1175_);
lean_ctor_set_uint64(v_reuseFailAlloc_1186_, sizeof(void*)*1, v_tid_1162_);
v___x_1177_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1179_; 
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 4, v___x_1177_);
v___x_1179_ = v___x_1160_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_env_1151_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_nextMacroScope_1152_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v_ngen_1153_);
lean_ctor_set(v_reuseFailAlloc_1185_, 3, v_auxDeclNGen_1154_);
lean_ctor_set(v_reuseFailAlloc_1185_, 4, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1185_, 5, v_cache_1155_);
lean_ctor_set(v_reuseFailAlloc_1185_, 6, v_messages_1156_);
lean_ctor_set(v_reuseFailAlloc_1185_, 7, v_infoState_1157_);
lean_ctor_set(v_reuseFailAlloc_1185_, 8, v_snapshotTasks_1158_);
v___x_1179_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1180_ = lean_st_ref_put(v___y_1141_, v___x_1179_);
v___x_1181_ = lean_box(0);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1181_);
v___x_1183_ = v___x_1147_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___boxed(lean_object* v_cls_1190_, lean_object* v_msg_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9(v_cls_1190_, v_msg_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__10(lean_object* v_init_1196_, lean_object* v_x_1197_){
_start:
{
if (lean_obj_tag(v_x_1197_) == 0)
{
lean_object* v_k_1198_; lean_object* v_l_1199_; lean_object* v_r_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v_k_1198_ = lean_ctor_get(v_x_1197_, 1);
v_l_1199_ = lean_ctor_get(v_x_1197_, 3);
v_r_1200_ = lean_ctor_get(v_x_1197_, 4);
v___x_1201_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__10(v_init_1196_, v_r_1200_);
lean_inc(v_k_1198_);
v___x_1202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1202_, 0, v_k_1198_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v_init_1196_ = v___x_1202_;
v_x_1197_ = v_l_1199_;
goto _start;
}
else
{
return v_init_1196_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__10___boxed(lean_object* v_init_1204_, lean_object* v_x_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__10(v_init_1204_, v_x_1205_);
lean_dec(v_x_1205_);
return v_res_1206_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg___lam__0(lean_object* v_x_1207_, lean_object* v_x_1208_){
_start:
{
lean_object* v_snd_1209_; lean_object* v_snd_1210_; lean_object* v_snd_1211_; lean_object* v_snd_1212_; double v___x_1213_; double v___x_1214_; uint8_t v___x_1215_; 
v_snd_1209_ = lean_ctor_get(v_x_1207_, 1);
v_snd_1210_ = lean_ctor_get(v_x_1208_, 1);
v_snd_1211_ = lean_ctor_get(v_snd_1209_, 1);
v_snd_1212_ = lean_ctor_get(v_snd_1210_, 1);
v___x_1213_ = lean_unbox_float(v_snd_1212_);
v___x_1214_ = lean_unbox_float(v_snd_1211_);
v___x_1215_ = lean_float_decLt(v___x_1213_, v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg___lam__0___boxed(lean_object* v_x_1216_, lean_object* v_x_1217_){
_start:
{
uint8_t v_res_1218_; lean_object* v_r_1219_; 
v_res_1218_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg___lam__0(v_x_1216_, v_x_1217_);
lean_dec_ref(v_x_1217_);
lean_dec_ref(v_x_1216_);
v_r_1219_ = lean_box(v_res_1218_);
return v_r_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__8___redArg(lean_object* v_hi_1220_, lean_object* v_pivot_1221_, lean_object* v_as_1222_, lean_object* v_i_1223_, lean_object* v_k_1224_){
_start:
{
uint8_t v___x_1225_; 
v___x_1225_ = lean_nat_dec_lt(v_k_1224_, v_hi_1220_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec(v_k_1224_);
v___x_1226_ = lean_array_fswap(v_as_1222_, v_i_1223_, v_hi_1220_);
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v_i_1223_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
return v___x_1227_;
}
else
{
lean_object* v___x_1228_; lean_object* v_snd_1229_; lean_object* v_snd_1230_; lean_object* v_snd_1231_; lean_object* v_snd_1232_; double v___x_1233_; double v___x_1234_; uint8_t v___x_1235_; 
v___x_1228_ = lean_array_fget_borrowed(v_as_1222_, v_k_1224_);
v_snd_1229_ = lean_ctor_get(v___x_1228_, 1);
v_snd_1230_ = lean_ctor_get(v_pivot_1221_, 1);
v_snd_1231_ = lean_ctor_get(v_snd_1229_, 1);
v_snd_1232_ = lean_ctor_get(v_snd_1230_, 1);
v___x_1233_ = lean_unbox_float(v_snd_1232_);
v___x_1234_ = lean_unbox_float(v_snd_1231_);
v___x_1235_ = lean_float_decLt(v___x_1233_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_unsigned_to_nat(1u);
v___x_1237_ = lean_nat_add(v_k_1224_, v___x_1236_);
lean_dec(v_k_1224_);
v_k_1224_ = v___x_1237_;
goto _start;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1239_ = lean_array_fswap(v_as_1222_, v_i_1223_, v_k_1224_);
v___x_1240_ = lean_unsigned_to_nat(1u);
v___x_1241_ = lean_nat_add(v_i_1223_, v___x_1240_);
lean_dec(v_i_1223_);
v___x_1242_ = lean_nat_add(v_k_1224_, v___x_1240_);
lean_dec(v_k_1224_);
v_as_1222_ = v___x_1239_;
v_i_1223_ = v___x_1241_;
v_k_1224_ = v___x_1242_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__8___redArg___boxed(lean_object* v_hi_1244_, lean_object* v_pivot_1245_, lean_object* v_as_1246_, lean_object* v_i_1247_, lean_object* v_k_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__8___redArg(v_hi_1244_, v_pivot_1245_, v_as_1246_, v_i_1247_, v_k_1248_);
lean_dec_ref(v_pivot_1245_);
lean_dec(v_hi_1244_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg(lean_object* v_n_1250_, lean_object* v_as_1251_, lean_object* v_lo_1252_, lean_object* v_hi_1253_){
_start:
{
lean_object* v___y_1255_; uint8_t v___x_1265_; 
v___x_1265_ = lean_nat_dec_lt(v_lo_1252_, v_hi_1253_);
if (v___x_1265_ == 0)
{
lean_dec(v_lo_1252_);
return v_as_1251_;
}
else
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v_mid_1268_; lean_object* v___y_1270_; lean_object* v___y_1276_; lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1266_ = lean_nat_add(v_lo_1252_, v_hi_1253_);
v___x_1267_ = lean_unsigned_to_nat(1u);
v_mid_1268_ = lean_nat_shiftr(v___x_1266_, v___x_1267_);
lean_dec(v___x_1266_);
v___x_1281_ = lean_array_fget_borrowed(v_as_1251_, v_mid_1268_);
v___x_1282_ = lean_array_fget_borrowed(v_as_1251_, v_lo_1252_);
v___x_1283_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg___lam__0(v___x_1281_, v___x_1282_);
if (v___x_1283_ == 0)
{
v___y_1276_ = v_as_1251_;
goto v___jp_1275_;
}
else
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_array_fswap(v_as_1251_, v_lo_1252_, v_mid_1268_);
v___y_1276_ = v___x_1284_;
goto v___jp_1275_;
}
v___jp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1271_ = lean_array_fget_borrowed(v___y_1270_, v_mid_1268_);
v___x_1272_ = lean_array_fget_borrowed(v___y_1270_, v_hi_1253_);
v___x_1273_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg___lam__0(v___x_1271_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_dec(v_mid_1268_);
v___y_1255_ = v___y_1270_;
goto v___jp_1254_;
}
else
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_array_fswap(v___y_1270_, v_mid_1268_, v_hi_1253_);
lean_dec(v_mid_1268_);
v___y_1255_ = v___x_1274_;
goto v___jp_1254_;
}
}
v___jp_1275_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1277_ = lean_array_fget_borrowed(v___y_1276_, v_hi_1253_);
v___x_1278_ = lean_array_fget_borrowed(v___y_1276_, v_lo_1252_);
v___x_1279_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg___lam__0(v___x_1277_, v___x_1278_);
if (v___x_1279_ == 0)
{
v___y_1270_ = v___y_1276_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1280_; 
v___x_1280_ = lean_array_fswap(v___y_1276_, v_lo_1252_, v_hi_1253_);
v___y_1270_ = v___x_1280_;
goto v___jp_1269_;
}
}
}
v___jp_1254_:
{
lean_object* v_pivot_1256_; lean_object* v___x_1257_; lean_object* v_fst_1258_; lean_object* v_snd_1259_; uint8_t v___x_1260_; 
v_pivot_1256_ = lean_array_fget(v___y_1255_, v_hi_1253_);
lean_inc_n(v_lo_1252_, 2);
v___x_1257_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__8___redArg(v_hi_1253_, v_pivot_1256_, v___y_1255_, v_lo_1252_, v_lo_1252_);
lean_dec(v_pivot_1256_);
v_fst_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_fst_1258_);
v_snd_1259_ = lean_ctor_get(v___x_1257_, 1);
lean_inc(v_snd_1259_);
lean_dec_ref(v___x_1257_);
v___x_1260_ = lean_nat_dec_le(v_hi_1253_, v_fst_1258_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg(v_n_1250_, v_snd_1259_, v_lo_1252_, v_fst_1258_);
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = lean_nat_add(v_fst_1258_, v___x_1262_);
lean_dec(v_fst_1258_);
v_as_1251_ = v___x_1261_;
v_lo_1252_ = v___x_1263_;
goto _start;
}
else
{
lean_dec(v_fst_1258_);
lean_dec(v_lo_1252_);
return v_snd_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg___boxed(lean_object* v_n_1285_, lean_object* v_as_1286_, lean_object* v_lo_1287_, lean_object* v_hi_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg(v_n_1285_, v_as_1286_, v_lo_1287_, v_hi_1288_);
lean_dec(v_hi_1288_);
lean_dec(v_n_1285_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__4(lean_object* v_as_1290_, size_t v_i_1291_, size_t v_stop_1292_, lean_object* v_b_1293_){
_start:
{
uint8_t v___x_1294_; 
v___x_1294_ = lean_usize_dec_eq(v_i_1291_, v_stop_1292_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; lean_object* v_snd_1296_; lean_object* v_fst_1297_; lean_object* v___x_1298_; size_t v___x_1299_; size_t v___x_1300_; 
v___x_1295_ = lean_array_uget_borrowed(v_as_1290_, v_i_1291_);
v_snd_1296_ = lean_ctor_get(v___x_1295_, 1);
v_fst_1297_ = lean_ctor_get(v_snd_1296_, 0);
lean_inc(v_fst_1297_);
v___x_1298_ = l_Lean_NameSet_append(v_b_1293_, v_fst_1297_);
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = lean_usize_add(v_i_1291_, v___x_1299_);
v_i_1291_ = v___x_1300_;
v_b_1293_ = v___x_1298_;
goto _start;
}
else
{
return v_b_1293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__4___boxed(lean_object* v_as_1302_, lean_object* v_i_1303_, lean_object* v_stop_1304_, lean_object* v_b_1305_){
_start:
{
size_t v_i_boxed_1306_; size_t v_stop_boxed_1307_; lean_object* v_res_1308_; 
v_i_boxed_1306_ = lean_unbox_usize(v_i_1303_);
lean_dec(v_i_1303_);
v_stop_boxed_1307_ = lean_unbox_usize(v_stop_1304_);
lean_dec(v_stop_1304_);
v_res_1308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__4(v_as_1302_, v_i_boxed_1306_, v_stop_boxed_1307_, v_b_1305_);
lean_dec_ref(v_as_1302_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__1(lean_object* v_score_1309_, lean_object* v___x_1310_, size_t v_sz_1311_, size_t v_i_1312_, lean_object* v_bs_1313_){
_start:
{
uint8_t v___x_1314_; 
v___x_1314_ = lean_usize_dec_lt(v_i_1312_, v_sz_1311_);
if (v___x_1314_ == 0)
{
lean_dec(v___x_1310_);
lean_dec_ref(v_score_1309_);
return v_bs_1313_;
}
else
{
lean_object* v_v_1315_; lean_object* v_fst_1316_; lean_object* v_snd_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1332_; 
v_v_1315_ = lean_array_uget(v_bs_1313_, v_i_1312_);
v_fst_1316_ = lean_ctor_get(v_v_1315_, 0);
v_snd_1317_ = lean_ctor_get(v_v_1315_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_v_1315_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1319_ = v_v_1315_;
v_isShared_1320_ = v_isSharedCheck_1332_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_snd_1317_);
lean_inc(v_fst_1316_);
lean_dec(v_v_1315_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1332_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v_bs_x27_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1321_ = lean_unsigned_to_nat(0u);
v_bs_x27_1322_ = lean_array_uset(v_bs_1313_, v_i_1312_, v___x_1321_);
lean_inc_ref(v_score_1309_);
lean_inc(v_snd_1317_);
lean_inc(v___x_1310_);
v___x_1323_ = lean_apply_2(v_score_1309_, v___x_1310_, v_snd_1317_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 1, v___x_1323_);
lean_ctor_set(v___x_1319_, 0, v_snd_1317_);
v___x_1325_ = v___x_1319_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_snd_1317_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
lean_object* v___x_1326_; size_t v___x_1327_; size_t v___x_1328_; lean_object* v___x_1329_; 
v___x_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1326_, 0, v_fst_1316_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
v___x_1327_ = ((size_t)1ULL);
v___x_1328_ = lean_usize_add(v_i_1312_, v___x_1327_);
v___x_1329_ = lean_array_uset(v_bs_x27_1322_, v_i_1312_, v___x_1326_);
v_i_1312_ = v___x_1328_;
v_bs_1313_ = v___x_1329_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__1___boxed(lean_object* v_score_1333_, lean_object* v___x_1334_, lean_object* v_sz_1335_, lean_object* v_i_1336_, lean_object* v_bs_1337_){
_start:
{
size_t v_sz_boxed_1338_; size_t v_i_boxed_1339_; lean_object* v_res_1340_; 
v_sz_boxed_1338_ = lean_unbox_usize(v_sz_1335_);
lean_dec(v_sz_1335_);
v_i_boxed_1339_ = lean_unbox_usize(v_i_1336_);
lean_dec(v_i_1336_);
v_res_1340_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__1(v_score_1333_, v___x_1334_, v_sz_boxed_1338_, v_i_boxed_1339_, v_bs_1337_);
return v_res_1340_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__2));
v___x_1346_ = l_Lean_stringToMessageData(v___x_1345_);
return v___x_1346_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__4));
v___x_1349_ = l_Lean_stringToMessageData(v___x_1348_);
return v___x_1349_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__6));
v___x_1352_ = l_Lean_stringToMessageData(v___x_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1(lean_object* v___f_1353_, lean_object* v_fst_1354_, double v_c_1355_, lean_object* v___x_1356_, lean_object* v___x_1357_, lean_object* v_fst_1358_, lean_object* v_snd_1359_, lean_object* v_fst_1360_, lean_object* v_score_1361_, lean_object* v___x_1362_, lean_object* v_____r_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; size_t v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; size_t v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1413_; size_t v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1422_; size_t v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; uint8_t v___y_1431_; size_t v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___x_1492_; 
lean_inc(v___y_1365_);
lean_inc_ref(v___y_1364_);
v___x_1492_ = lean_apply_3(v___f_1353_, v___y_1364_, v___y_1365_, lean_box(0));
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; uint8_t v___x_1494_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1493_);
lean_dec_ref_known(v___x_1492_, 1);
v___x_1494_ = lean_unbox(v_a_1493_);
lean_dec(v_a_1493_);
if (v___x_1494_ == 0)
{
v___y_1440_ = v___y_1364_;
v___y_1441_ = v___y_1365_;
goto v___jp_1439_;
}
else
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1495_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__7, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__7_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__7);
v___x_1496_ = lean_box(0);
v___x_1497_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__10(v___x_1496_, v_fst_1358_);
v___x_1498_ = l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__11(v___x_1497_, v___x_1496_);
v___x_1499_ = l_Lean_MessageData_ofList(v___x_1498_);
v___x_1500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1495_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
v___x_1501_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5);
v___x_1502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1500_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
lean_inc(v___x_1362_);
v___x_1503_ = l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9(v___x_1362_, v___x_1502_, v___y_1364_, v___y_1365_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_dec_ref_known(v___x_1503_, 1);
v___y_1440_ = v___y_1364_;
v___y_1441_ = v___y_1365_;
goto v___jp_1439_;
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec(v___x_1362_);
lean_dec_ref(v_score_1361_);
lean_dec(v_fst_1360_);
lean_dec(v_snd_1359_);
lean_dec(v_fst_1358_);
lean_dec(v___x_1357_);
lean_dec(v___x_1356_);
lean_dec(v_fst_1354_);
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
lean_dec(v___x_1362_);
lean_dec_ref(v_score_1361_);
lean_dec(v_fst_1360_);
lean_dec(v_snd_1359_);
lean_dec(v_fst_1358_);
lean_dec(v___x_1357_);
lean_dec(v___x_1356_);
lean_dec(v_fst_1354_);
v_a_1512_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1492_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1492_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
v___jp_1367_:
{
double v___x_1372_; double v___x_1373_; double v___x_1374_; double v___x_1375_; double v___x_1376_; double v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1372_ = lean_float_of_nat(v___y_1369_);
v___x_1373_ = lean_unbox_float(v_fst_1354_);
v___x_1374_ = lean_float_sub(v___x_1372_, v___x_1373_);
v___x_1375_ = lean_float_div(v___x_1374_, v_c_1355_);
v___x_1376_ = lean_unbox_float(v_fst_1354_);
lean_dec(v_fst_1354_);
v___x_1377_ = lean_float_add(v___x_1376_, v___x_1375_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___y_1371_);
lean_ctor_set(v___x_1378_, 1, v___y_1370_);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___y_1368_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = lean_box_float(v___x_1377_);
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
lean_ctor_set(v___x_1381_, 1, v___x_1379_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1356_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
v___jp_1385_:
{
size_t v_sz_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v_sz_1392_ = lean_array_size(v___y_1387_);
v___x_1393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__3(v_sz_1392_, v___y_1386_, v___y_1387_);
v___x_1394_ = lean_nat_dec_lt(v___x_1357_, v___y_1389_);
lean_dec(v___x_1357_);
if (v___x_1394_ == 0)
{
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
v___y_1368_ = v___x_1393_;
v___y_1369_ = v___y_1388_;
v___y_1370_ = v___y_1391_;
v___y_1371_ = v_fst_1358_;
goto v___jp_1367_;
}
else
{
uint8_t v___x_1395_; 
v___x_1395_ = lean_nat_dec_le(v___y_1389_, v___y_1389_);
if (v___x_1395_ == 0)
{
if (v___x_1394_ == 0)
{
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
v___y_1368_ = v___x_1393_;
v___y_1369_ = v___y_1388_;
v___y_1370_ = v___y_1391_;
v___y_1371_ = v_fst_1358_;
goto v___jp_1367_;
}
else
{
size_t v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_usize_of_nat(v___y_1389_);
lean_dec(v___y_1389_);
v___x_1397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__4(v___y_1390_, v___y_1386_, v___x_1396_, v_fst_1358_);
lean_dec_ref(v___y_1390_);
v___y_1368_ = v___x_1393_;
v___y_1369_ = v___y_1388_;
v___y_1370_ = v___y_1391_;
v___y_1371_ = v___x_1397_;
goto v___jp_1367_;
}
}
else
{
size_t v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = lean_usize_of_nat(v___y_1389_);
lean_dec(v___y_1389_);
v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__4(v___y_1390_, v___y_1386_, v___x_1398_, v_fst_1358_);
lean_dec_ref(v___y_1390_);
v___y_1368_ = v___x_1393_;
v___y_1369_ = v___y_1388_;
v___y_1370_ = v___y_1391_;
v___y_1371_ = v___x_1399_;
goto v___jp_1367_;
}
}
}
v___jp_1400_:
{
lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1405_ = lean_array_get_size(v___y_1404_);
v___x_1406_ = lean_nat_dec_lt(v___x_1357_, v___x_1405_);
if (v___x_1406_ == 0)
{
v___y_1386_ = v___y_1401_;
v___y_1387_ = v___y_1402_;
v___y_1388_ = v___y_1403_;
v___y_1389_ = v___x_1405_;
v___y_1390_ = v___y_1404_;
v___y_1391_ = v_snd_1359_;
goto v___jp_1385_;
}
else
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_nat_dec_le(v___x_1405_, v___x_1405_);
if (v___x_1407_ == 0)
{
if (v___x_1406_ == 0)
{
v___y_1386_ = v___y_1401_;
v___y_1387_ = v___y_1402_;
v___y_1388_ = v___y_1403_;
v___y_1389_ = v___x_1405_;
v___y_1390_ = v___y_1404_;
v___y_1391_ = v_snd_1359_;
goto v___jp_1385_;
}
else
{
size_t v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_usize_of_nat(v___x_1405_);
v___x_1409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__5(v___y_1404_, v___y_1401_, v___x_1408_, v_snd_1359_);
v___y_1386_ = v___y_1401_;
v___y_1387_ = v___y_1402_;
v___y_1388_ = v___y_1403_;
v___y_1389_ = v___x_1405_;
v___y_1390_ = v___y_1404_;
v___y_1391_ = v___x_1409_;
goto v___jp_1385_;
}
}
else
{
size_t v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_usize_of_nat(v___x_1405_);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__5(v___y_1404_, v___y_1401_, v___x_1410_, v_snd_1359_);
v___y_1386_ = v___y_1401_;
v___y_1387_ = v___y_1402_;
v___y_1388_ = v___y_1403_;
v___y_1389_ = v___x_1405_;
v___y_1390_ = v___y_1404_;
v___y_1391_ = v___x_1411_;
goto v___jp_1385_;
}
}
}
v___jp_1412_:
{
lean_object* v___x_1420_; 
v___x_1420_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg(v___y_1417_, v___y_1418_, v___y_1413_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec(v___y_1417_);
v___y_1401_ = v___y_1414_;
v___y_1402_ = v___y_1415_;
v___y_1403_ = v___y_1416_;
v___y_1404_ = v___x_1420_;
goto v___jp_1400_;
}
v___jp_1421_:
{
uint8_t v___x_1429_; 
v___x_1429_ = lean_nat_dec_le(v___y_1428_, v___y_1422_);
if (v___x_1429_ == 0)
{
lean_dec(v___y_1422_);
lean_inc(v___y_1428_);
v___y_1413_ = v___y_1428_;
v___y_1414_ = v___y_1423_;
v___y_1415_ = v___y_1424_;
v___y_1416_ = v___y_1425_;
v___y_1417_ = v___y_1426_;
v___y_1418_ = v___y_1427_;
v___y_1419_ = v___y_1428_;
goto v___jp_1412_;
}
else
{
v___y_1413_ = v___y_1428_;
v___y_1414_ = v___y_1423_;
v___y_1415_ = v___y_1424_;
v___y_1416_ = v___y_1425_;
v___y_1417_ = v___y_1426_;
v___y_1418_ = v___y_1427_;
v___y_1419_ = v___y_1422_;
goto v___jp_1412_;
}
}
v___jp_1430_:
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_unsigned_to_nat(1u);
if (v___y_1431_ == 0)
{
lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1437_ = lean_nat_sub(v___y_1434_, v___x_1436_);
v___x_1438_ = lean_nat_dec_le(v___x_1357_, v___x_1437_);
if (v___x_1438_ == 0)
{
lean_inc(v___x_1437_);
v___y_1422_ = v___x_1437_;
v___y_1423_ = v___y_1432_;
v___y_1424_ = v___y_1433_;
v___y_1425_ = v___x_1436_;
v___y_1426_ = v___y_1434_;
v___y_1427_ = v___y_1435_;
v___y_1428_ = v___x_1437_;
goto v___jp_1421_;
}
else
{
lean_inc(v___x_1357_);
v___y_1422_ = v___x_1437_;
v___y_1423_ = v___y_1432_;
v___y_1424_ = v___y_1433_;
v___y_1425_ = v___x_1436_;
v___y_1426_ = v___y_1434_;
v___y_1427_ = v___y_1435_;
v___y_1428_ = v___x_1357_;
goto v___jp_1421_;
}
}
else
{
lean_dec(v___y_1434_);
v___y_1401_ = v___y_1432_;
v___y_1402_ = v___y_1433_;
v___y_1403_ = v___x_1436_;
v___y_1404_ = v___y_1435_;
goto v___jp_1400_;
}
}
v___jp_1439_:
{
size_t v_sz_1442_; size_t v___x_1443_; lean_object* v___x_1444_; lean_object* v_bs_1445_; lean_object* v___x_1446_; size_t v_sz_1447_; double v___x_1448_; lean_object* v___x_1449_; lean_object* v_fst_1450_; lean_object* v_snd_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1491_; 
v_sz_1442_ = lean_array_size(v_fst_1360_);
v___x_1443_ = ((size_t)0ULL);
lean_inc(v_fst_1360_);
lean_inc(v_fst_1358_);
v___x_1444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__1(v_score_1361_, v_fst_1358_, v_sz_1442_, v___x_1443_, v_fst_1360_);
v_bs_1445_ = lean_mk_empty_array_with_capacity(v___x_1357_);
lean_inc_ref(v_bs_1445_);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v_bs_1445_);
lean_ctor_set(v___x_1446_, 1, v_bs_1445_);
v_sz_1447_ = lean_array_size(v___x_1444_);
v___x_1448_ = lean_unbox_float(v_fst_1354_);
v___x_1449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__2(v___x_1448_, v___x_1444_, v_sz_1447_, v___x_1443_, v___x_1446_);
lean_dec_ref(v___x_1444_);
v_fst_1450_ = lean_ctor_get(v___x_1449_, 0);
v_snd_1451_ = lean_ctor_get(v___x_1449_, 1);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1453_ = v___x_1449_;
v_isShared_1454_ = v_isSharedCheck_1491_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_snd_1451_);
lean_inc(v_fst_1450_);
lean_dec(v___x_1449_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1491_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; uint8_t v___x_1456_; 
v___x_1455_ = lean_array_get_size(v_fst_1450_);
v___x_1456_ = lean_nat_dec_eq(v___x_1455_, v___x_1357_);
if (v___x_1456_ == 0)
{
lean_object* v_options_1457_; uint8_t v_hasTrace_1458_; 
lean_del_object(v___x_1453_);
lean_dec(v_fst_1360_);
v_options_1457_ = lean_ctor_get(v___y_1440_, 2);
v_hasTrace_1458_ = lean_ctor_get_uint8(v_options_1457_, sizeof(void*)*1);
if (v_hasTrace_1458_ == 0)
{
lean_dec(v___x_1362_);
v___y_1431_ = v___x_1456_;
v___y_1432_ = v___x_1443_;
v___y_1433_ = v_snd_1451_;
v___y_1434_ = v___x_1455_;
v___y_1435_ = v_fst_1450_;
goto v___jp_1430_;
}
else
{
lean_object* v_inheritedTraceOptions_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v_inheritedTraceOptions_1459_ = lean_ctor_get(v___y_1440_, 13);
v___x_1460_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__1));
lean_inc(v___x_1362_);
v___x_1461_ = l_Lean_Name_append(v___x_1460_, v___x_1362_);
v___x_1462_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1459_, v_options_1457_, v___x_1461_);
lean_dec(v___x_1461_);
if (v___x_1462_ == 0)
{
lean_dec(v___x_1362_);
v___y_1431_ = v___x_1456_;
v___y_1432_ = v___x_1443_;
v___y_1433_ = v_snd_1451_;
v___y_1434_ = v___x_1455_;
v___y_1435_ = v_fst_1450_;
goto v___jp_1430_;
}
else
{
lean_object* v___x_1463_; size_t v_sz_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1463_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__3);
v_sz_1464_ = lean_array_size(v_fst_1450_);
lean_inc(v_fst_1450_);
v___x_1465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__7(v_sz_1464_, v___x_1443_, v_fst_1450_);
v___x_1466_ = lean_array_to_list(v___x_1465_);
v___x_1467_ = lean_box(0);
v___x_1468_ = l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8(v___x_1466_, v___x_1467_);
v___x_1469_ = l_Lean_MessageData_ofList(v___x_1468_);
v___x_1470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1463_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5);
v___x_1472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1470_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
v___x_1473_ = l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9(v___x_1362_, v___x_1472_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_dec_ref_known(v___x_1473_, 1);
v___y_1431_ = v___x_1456_;
v___y_1432_ = v___x_1443_;
v___y_1433_ = v_snd_1451_;
v___y_1434_ = v___x_1455_;
v___y_1435_ = v_fst_1450_;
goto v___jp_1430_;
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_dec(v_snd_1451_);
lean_dec(v_fst_1450_);
lean_dec(v_snd_1359_);
lean_dec(v_fst_1358_);
lean_dec(v___x_1357_);
lean_dec(v___x_1356_);
lean_dec(v_fst_1354_);
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
lean_dec(v_snd_1451_);
lean_dec(v_fst_1450_);
lean_dec(v___x_1362_);
lean_dec(v___x_1357_);
lean_dec(v___x_1356_);
lean_inc(v_snd_1359_);
v___x_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1482_, 0, v_snd_1359_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 1, v_snd_1359_);
lean_ctor_set(v___x_1453_, 0, v_fst_1358_);
v___x_1484_ = v___x_1453_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_fst_1358_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_snd_1359_);
v___x_1484_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1485_, 0, v_fst_1360_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v_fst_1354_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1482_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
return v___x_1489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___boxed(lean_object* v___f_1520_, lean_object* v_fst_1521_, lean_object* v_c_1522_, lean_object* v___x_1523_, lean_object* v___x_1524_, lean_object* v_fst_1525_, lean_object* v_snd_1526_, lean_object* v_fst_1527_, lean_object* v_score_1528_, lean_object* v___x_1529_, lean_object* v_____r_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
double v_c_boxed_1534_; lean_object* v_res_1535_; 
v_c_boxed_1534_ = lean_unbox_float(v_c_1522_);
lean_dec_ref(v_c_1522_);
v_res_1535_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1(v___f_1520_, v_fst_1521_, v_c_boxed_1534_, v___x_1523_, v___x_1524_, v_fst_1525_, v_snd_1526_, v_fst_1527_, v_score_1528_, v___x_1529_, v_____r_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__0(lean_object* v___x_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_options_1540_; uint8_t v_hasTrace_1541_; 
v_options_1540_ = lean_ctor_get(v___y_1537_, 2);
v_hasTrace_1541_ = lean_ctor_get_uint8(v_options_1540_, sizeof(void*)*1);
if (v_hasTrace_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_dec(v___x_1536_);
v___x_1542_ = lean_box(v_hasTrace_1541_);
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
return v___x_1543_;
}
else
{
lean_object* v_inheritedTraceOptions_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_inheritedTraceOptions_1544_ = lean_ctor_get(v___y_1537_, 13);
v___x_1545_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__1));
v___x_1546_ = l_Lean_Name_append(v___x_1545_, v___x_1536_);
v___x_1547_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1544_, v_options_1540_, v___x_1546_);
lean_dec(v___x_1546_);
v___x_1548_ = lean_box(v___x_1547_);
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
return v___x_1549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__0___boxed(lean_object* v___x_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__0(v___x_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
return v_res_1554_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__1));
v___x_1559_ = l_Lean_stringToMessageData(v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg(lean_object* v_score_1560_, double v_c_1561_, lean_object* v_maxSuggestions_1562_, lean_object* v_a_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___y_1568_; lean_object* v_snd_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1667_; 
v_snd_1588_ = lean_ctor_get(v_a_1563_, 1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_a_1563_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; 
v_unused_1668_ = lean_ctor_get(v_a_1563_, 0);
lean_dec(v_unused_1668_);
v___x_1590_ = v_a_1563_;
v_isShared_1591_ = v_isSharedCheck_1667_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_snd_1588_);
lean_dec(v_a_1563_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1667_;
goto v_resetjp_1589_;
}
v___jp_1567_:
{
if (lean_obj_tag(v___y_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1579_; 
v_a_1569_ = lean_ctor_get(v___y_1568_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___y_1568_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1571_ = v___y_1568_;
v_isShared_1572_ = v_isSharedCheck_1579_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___y_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1579_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
if (lean_obj_tag(v_a_1569_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1575_; 
lean_dec_ref(v_score_1560_);
v_a_1573_ = lean_ctor_get(v_a_1569_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v_a_1569_, 1);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v_a_1573_);
v___x_1575_ = v___x_1571_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
else
{
lean_object* v_a_1577_; 
lean_del_object(v___x_1571_);
v_a_1577_ = lean_ctor_get(v_a_1569_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v_a_1569_, 1);
v_a_1563_ = v_a_1577_;
goto _start;
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec_ref(v_score_1560_);
v_a_1580_ = lean_ctor_get(v___y_1568_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___y_1568_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___y_1568_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___y_1568_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
v_resetjp_1589_:
{
lean_object* v_snd_1592_; lean_object* v_snd_1593_; lean_object* v_fst_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1665_; 
v_snd_1592_ = lean_ctor_get(v_snd_1588_, 1);
lean_inc(v_snd_1592_);
v_snd_1593_ = lean_ctor_get(v_snd_1592_, 1);
lean_inc(v_snd_1593_);
v_fst_1594_ = lean_ctor_get(v_snd_1588_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_snd_1588_);
if (v_isSharedCheck_1665_ == 0)
{
lean_object* v_unused_1666_; 
v_unused_1666_ = lean_ctor_get(v_snd_1588_, 1);
lean_dec(v_unused_1666_);
v___x_1596_ = v_snd_1588_;
v_isShared_1597_ = v_isSharedCheck_1665_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_fst_1594_);
lean_dec(v_snd_1588_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1665_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v_fst_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1663_; 
v_fst_1598_ = lean_ctor_get(v_snd_1592_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_snd_1592_);
if (v_isSharedCheck_1663_ == 0)
{
lean_object* v_unused_1664_; 
v_unused_1664_ = lean_ctor_get(v_snd_1592_, 1);
lean_dec(v_unused_1664_);
v___x_1600_ = v_snd_1592_;
v_isShared_1601_ = v_isSharedCheck_1663_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_fst_1598_);
lean_dec(v_snd_1592_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1663_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v_fst_1602_; lean_object* v_snd_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1662_; 
v_fst_1602_ = lean_ctor_get(v_snd_1593_, 0);
v_snd_1603_ = lean_ctor_get(v_snd_1593_, 1);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_snd_1593_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1605_ = v_snd_1593_;
v_isShared_1606_ = v_isSharedCheck_1662_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_snd_1603_);
lean_inc(v_fst_1602_);
lean_dec(v_snd_1593_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1662_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___y_1610_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1607_ = lean_box(0);
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1658_ = lean_array_get_size(v_fst_1598_);
v___x_1659_ = lean_nat_dec_lt(v___x_1608_, v___x_1658_);
if (v___x_1659_ == 0)
{
v___y_1610_ = v___x_1659_;
goto v___jp_1609_;
}
else
{
lean_object* v___x_1660_; uint8_t v___x_1661_; 
v___x_1660_ = lean_array_get_size(v_snd_1603_);
v___x_1661_ = lean_nat_dec_lt(v___x_1660_, v_maxSuggestions_1562_);
v___y_1610_ = v___x_1661_;
goto v___jp_1609_;
}
v___jp_1609_:
{
if (v___y_1610_ == 0)
{
lean_object* v___x_1612_; 
lean_dec_ref(v_score_1560_);
if (v_isShared_1606_ == 0)
{
v___x_1612_ = v___x_1605_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_fst_1602_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_snd_1603_);
v___x_1612_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
lean_object* v___x_1614_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 1, v___x_1612_);
v___x_1614_ = v___x_1600_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_fst_1598_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v___x_1612_);
v___x_1614_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1616_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 1, v___x_1614_);
v___x_1616_ = v___x_1596_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_fst_1594_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1618_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 1, v___x_1616_);
lean_ctor_set(v___x_1590_, 0, v___x_1607_);
v___x_1618_ = v___x_1590_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
return v___x_1619_;
}
}
}
}
}
else
{
lean_object* v___x_1624_; lean_object* v___f_1625_; lean_object* v___x_1626_; 
lean_del_object(v___x_1605_);
lean_del_object(v___x_1600_);
lean_del_object(v___x_1596_);
lean_del_object(v___x_1590_);
v___x_1624_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__1_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_));
v___f_1625_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__0));
v___x_1626_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__0(v___x_1624_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; uint8_t v___x_1628_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v___x_1628_ = lean_unbox(v_a_1627_);
lean_dec(v_a_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = lean_box(0);
lean_inc_ref(v_score_1560_);
v___x_1630_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1(v___f_1625_, v_fst_1594_, v_c_1561_, v___x_1607_, v___x_1608_, v_fst_1602_, v_snd_1603_, v_fst_1598_, v_score_1560_, v___x_1624_, v___x_1629_, v___y_1564_, v___y_1565_);
v___y_1568_ = v___x_1630_;
goto v___jp_1567_;
}
else
{
lean_object* v___x_1631_; double v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1631_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__2);
v___x_1632_ = lean_unbox_float(v_fst_1594_);
v___x_1633_ = lean_float_to_string(v___x_1632_);
v___x_1634_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
v___x_1635_ = l_Lean_MessageData_ofFormat(v___x_1634_);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1631_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5);
v___x_1638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9(v___x_1624_, v___x_1638_, v___y_1564_, v___y_1565_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1641_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 1);
lean_inc_ref(v_score_1560_);
v___x_1641_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1(v___f_1625_, v_fst_1594_, v_c_1561_, v___x_1607_, v___x_1608_, v_fst_1602_, v_snd_1603_, v_fst_1598_, v_score_1560_, v___x_1624_, v_a_1640_, v___y_1564_, v___y_1565_);
v___y_1568_ = v___x_1641_;
goto v___jp_1567_;
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec(v_snd_1603_);
lean_dec(v_fst_1602_);
lean_dec(v_fst_1598_);
lean_dec(v_fst_1594_);
lean_dec_ref(v_score_1560_);
v_a_1642_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1639_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1639_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v_snd_1603_);
lean_dec(v_fst_1602_);
lean_dec(v_fst_1598_);
lean_dec(v_fst_1594_);
lean_dec_ref(v_score_1560_);
v_a_1650_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1626_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1626_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
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
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___boxed(lean_object* v_score_1669_, lean_object* v_c_1670_, lean_object* v_maxSuggestions_1671_, lean_object* v_a_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
double v_c_boxed_1676_; lean_object* v_res_1677_; 
v_c_boxed_1676_ = lean_unbox_float(v_c_1670_);
lean_dec_ref(v_c_1670_);
v_res_1677_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg(v_score_1669_, v_c_boxed_1676_, v_maxSuggestions_1671_, v_a_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v_maxSuggestions_1671_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1678_, lean_object* v_b_1679_, lean_object* v_acc_1680_, lean_object* v_i_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_keyArray_1690_; lean_object* v_valueArray_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v_keyArray_1690_ = lean_ctor_get(v_b_1679_, 1);
v_valueArray_1691_ = lean_ctor_get(v_b_1679_, 2);
v___x_1692_ = lean_array_get_size(v_keyArray_1690_);
v___x_1693_ = lean_nat_dec_lt(v_i_1681_, v___x_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_dec(v_i_1681_);
lean_dec_ref(v_f_1678_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v_acc_1680_);
lean_ctor_set(v___x_1694_, 1, v___y_1682_);
v___x_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
v___x_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
return v___x_1696_;
}
else
{
lean_object* v___x_1697_; uint8_t v_isSome_1698_; 
v___x_1697_ = lean_array_fget_borrowed(v_keyArray_1690_, v_i_1681_);
v_isSome_1698_ = lean_noption_is_some(v___x_1697_);
if (v_isSome_1698_ == 0)
{
goto v___jp_1686_;
}
else
{
lean_object* v___x_1699_; uint8_t v_isSome_1700_; 
v___x_1699_ = lean_array_fget_borrowed(v_valueArray_1691_, v_i_1681_);
v_isSome_1700_ = lean_noption_is_some(v___x_1699_);
if (v_isSome_1700_ == 0)
{
goto v___jp_1686_;
}
else
{
lean_object* v_val_1701_; lean_object* v_val_1702_; lean_object* v___x_1703_; 
lean_inc(v___x_1697_);
v_val_1701_ = lean_noption_get(v___x_1697_);
lean_inc(v___x_1699_);
v_val_1702_ = lean_noption_get(v___x_1699_);
lean_inc_ref(v_f_1678_);
lean_inc(v___y_1684_);
lean_inc_ref(v___y_1683_);
v___x_1703_ = lean_apply_6(v_f_1678_, v_val_1701_, v_val_1702_, v___y_1682_, v___y_1683_, v___y_1684_, lean_box(0));
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
if (lean_obj_tag(v_a_1704_) == 0)
{
lean_dec_ref_known(v_a_1704_, 1);
lean_dec(v_i_1681_);
lean_dec_ref(v_f_1678_);
return v___x_1703_;
}
else
{
lean_object* v_a_1705_; lean_object* v_fst_1706_; lean_object* v_snd_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_dec_ref_known(v___x_1703_, 1);
v_a_1705_ = lean_ctor_get(v_a_1704_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v_a_1704_, 1);
v_fst_1706_ = lean_ctor_get(v_a_1705_, 0);
lean_inc(v_fst_1706_);
v_snd_1707_ = lean_ctor_get(v_a_1705_, 1);
lean_inc(v_snd_1707_);
lean_dec(v_a_1705_);
v___x_1708_ = lean_unsigned_to_nat(1u);
v___x_1709_ = lean_nat_add(v_i_1681_, v___x_1708_);
lean_dec(v_i_1681_);
v_acc_1680_ = v_fst_1706_;
v_i_1681_ = v___x_1709_;
v___y_1682_ = v_snd_1707_;
goto _start;
}
}
else
{
lean_dec(v_i_1681_);
lean_dec_ref(v_f_1678_);
return v___x_1703_;
}
}
}
}
v___jp_1686_:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = lean_unsigned_to_nat(1u);
v___x_1688_ = lean_nat_add(v_i_1681_, v___x_1687_);
lean_dec(v_i_1681_);
v_i_1681_ = v___x_1688_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_1711_, lean_object* v_b_1712_, lean_object* v_acc_1713_, lean_object* v_i_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0_spec__1___redArg(v_f_1711_, v_b_1712_, v_acc_1713_, v_i_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec_ref(v_b_1712_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0___redArg(lean_object* v_f_1720_, lean_object* v_init_1721_, lean_object* v_b_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = lean_unsigned_to_nat(0u);
v___x_1728_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0_spec__1___redArg(v_f_1720_, v_b_1722_, v_init_1721_, v___x_1727_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0___redArg___boxed(lean_object* v_f_1729_, lean_object* v_init_1730_, lean_object* v_b_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0___redArg(v_f_1729_, v_init_1730_, v_b_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec_ref(v_b_1731_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg___lam__0(lean_object* v_f_1737_, lean_object* v_x_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
lean_inc(v___y_1743_);
lean_inc_ref(v___y_1742_);
v___x_1745_ = lean_apply_6(v_f_1737_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, lean_box(0));
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg___lam__0___boxed(lean_object* v_f_1746_, lean_object* v_x_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg___lam__0(v_f_1746_, v_x_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__20___redArg(lean_object* v_f_1755_, lean_object* v_keys_1756_, lean_object* v_vals_1757_, lean_object* v_i_1758_, lean_object* v_acc_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = lean_array_get_size(v_keys_1756_);
v___x_1765_ = lean_nat_dec_lt(v_i_1758_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_dec(v_i_1758_);
lean_dec_ref(v_f_1755_);
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v_acc_1759_);
lean_ctor_set(v___x_1766_, 1, v___y_1760_);
v___x_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
return v___x_1768_;
}
else
{
lean_object* v_k_1769_; lean_object* v_v_1770_; lean_object* v___x_1771_; 
v_k_1769_ = lean_array_fget_borrowed(v_keys_1756_, v_i_1758_);
v_v_1770_ = lean_array_fget_borrowed(v_vals_1757_, v_i_1758_);
lean_inc_ref(v_f_1755_);
lean_inc(v___y_1762_);
lean_inc_ref(v___y_1761_);
lean_inc(v_v_1770_);
lean_inc(v_k_1769_);
v___x_1771_ = lean_apply_7(v_f_1755_, v_acc_1759_, v_k_1769_, v_v_1770_, v___y_1760_, v___y_1761_, v___y_1762_, lean_box(0));
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
if (lean_obj_tag(v_a_1772_) == 0)
{
lean_dec_ref_known(v_a_1772_, 1);
lean_dec(v_i_1758_);
lean_dec_ref(v_f_1755_);
return v___x_1771_;
}
else
{
lean_object* v_a_1773_; lean_object* v_fst_1774_; lean_object* v_snd_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_dec_ref_known(v___x_1771_, 1);
v_a_1773_ = lean_ctor_get(v_a_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v_a_1772_, 1);
v_fst_1774_ = lean_ctor_get(v_a_1773_, 0);
lean_inc(v_fst_1774_);
v_snd_1775_ = lean_ctor_get(v_a_1773_, 1);
lean_inc(v_snd_1775_);
lean_dec(v_a_1773_);
v___x_1776_ = lean_unsigned_to_nat(1u);
v___x_1777_ = lean_nat_add(v_i_1758_, v___x_1776_);
lean_dec(v_i_1758_);
v_i_1758_ = v___x_1777_;
v_acc_1759_ = v_fst_1774_;
v___y_1760_ = v_snd_1775_;
goto _start;
}
}
else
{
lean_dec(v_i_1758_);
lean_dec_ref(v_f_1755_);
return v___x_1771_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__20___redArg___boxed(lean_object* v_f_1779_, lean_object* v_keys_1780_, lean_object* v_vals_1781_, lean_object* v_i_1782_, lean_object* v_acc_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__20___redArg(v_f_1779_, v_keys_1780_, v_vals_1781_, v_i_1782_, v_acc_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec_ref(v_vals_1781_);
lean_dec_ref(v_keys_1780_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17___redArg(lean_object* v_f_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
if (lean_obj_tag(v_x_1790_) == 0)
{
lean_object* v_es_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1820_; 
v_es_1796_ = lean_ctor_get(v_x_1790_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_x_1790_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1798_ = v_x_1790_;
v_isShared_1799_ = v_isSharedCheck_1820_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_es_1796_);
lean_dec(v_x_1790_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1820_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1801_ = lean_array_get_size(v_es_1796_);
v___x_1802_ = lean_nat_dec_lt(v___x_1800_, v___x_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
lean_dec_ref(v_es_1796_);
lean_dec_ref(v_f_1789_);
v___x_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1803_, 0, v_x_1791_);
lean_ctor_set(v___x_1803_, 1, v___y_1792_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set_tag(v___x_1798_, 1);
lean_ctor_set(v___x_1798_, 0, v___x_1803_);
v___x_1805_ = v___x_1798_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
return v___x_1806_;
}
}
else
{
uint8_t v___x_1808_; 
v___x_1808_ = lean_nat_dec_le(v___x_1801_, v___x_1801_);
if (v___x_1808_ == 0)
{
if (v___x_1802_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
lean_dec_ref(v_es_1796_);
lean_dec_ref(v_f_1789_);
v___x_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1809_, 0, v_x_1791_);
lean_ctor_set(v___x_1809_, 1, v___y_1792_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set_tag(v___x_1798_, 1);
lean_ctor_set(v___x_1798_, 0, v___x_1809_);
v___x_1811_ = v___x_1798_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1812_; 
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
return v___x_1812_;
}
}
else
{
size_t v___x_1814_; size_t v___x_1815_; lean_object* v___x_1816_; 
lean_del_object(v___x_1798_);
v___x_1814_ = ((size_t)0ULL);
v___x_1815_ = lean_usize_of_nat(v___x_1801_);
v___x_1816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__19___redArg(v_f_1789_, v_es_1796_, v___x_1814_, v___x_1815_, v_x_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec_ref(v_es_1796_);
return v___x_1816_;
}
}
else
{
size_t v___x_1817_; size_t v___x_1818_; lean_object* v___x_1819_; 
lean_del_object(v___x_1798_);
v___x_1817_ = ((size_t)0ULL);
v___x_1818_ = lean_usize_of_nat(v___x_1801_);
v___x_1819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__19___redArg(v_f_1789_, v_es_1796_, v___x_1817_, v___x_1818_, v_x_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec_ref(v_es_1796_);
return v___x_1819_;
}
}
}
}
else
{
lean_object* v_ks_1821_; lean_object* v_vs_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v_ks_1821_ = lean_ctor_get(v_x_1790_, 0);
lean_inc_ref(v_ks_1821_);
v_vs_1822_ = lean_ctor_get(v_x_1790_, 1);
lean_inc_ref(v_vs_1822_);
lean_dec_ref_known(v_x_1790_, 2);
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__20___redArg(v_f_1789_, v_ks_1821_, v_vs_1822_, v___x_1823_, v_x_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec_ref(v_vs_1822_);
lean_dec_ref(v_ks_1821_);
return v___x_1824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__19___redArg(lean_object* v_f_1825_, lean_object* v_as_1826_, size_t v_i_1827_, size_t v_stop_1828_, lean_object* v_b_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_fst_1835_; lean_object* v_snd_1836_; lean_object* v___y_1841_; uint8_t v___x_1846_; 
v___x_1846_ = lean_usize_dec_eq(v_i_1827_, v_stop_1828_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_array_uget_borrowed(v_as_1826_, v_i_1827_);
switch(lean_obj_tag(v___x_1847_))
{
case 0:
{
lean_object* v_key_1848_; lean_object* v_val_1849_; lean_object* v___x_1850_; 
v_key_1848_ = lean_ctor_get(v___x_1847_, 0);
v_val_1849_ = lean_ctor_get(v___x_1847_, 1);
lean_inc_ref(v_f_1825_);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v_val_1849_);
lean_inc(v_key_1848_);
v___x_1850_ = lean_apply_7(v_f_1825_, v_b_1829_, v_key_1848_, v_val_1849_, v___y_1830_, v___y_1831_, v___y_1832_, lean_box(0));
v___y_1841_ = v___x_1850_;
goto v___jp_1840_;
}
case 1:
{
lean_object* v_node_1851_; lean_object* v___x_1852_; 
v_node_1851_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_node_1851_);
lean_inc_ref(v_f_1825_);
v___x_1852_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17___redArg(v_f_1825_, v_node_1851_, v_b_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
v___y_1841_ = v___x_1852_;
goto v___jp_1840_;
}
default: 
{
v_fst_1835_ = v_b_1829_;
v_snd_1836_ = v___y_1830_;
goto v___jp_1834_;
}
}
}
else
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
lean_dec_ref(v_f_1825_);
v___x_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1853_, 0, v_b_1829_);
lean_ctor_set(v___x_1853_, 1, v___y_1830_);
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
return v___x_1855_;
}
v___jp_1834_:
{
size_t v___x_1837_; size_t v___x_1838_; 
v___x_1837_ = ((size_t)1ULL);
v___x_1838_ = lean_usize_add(v_i_1827_, v___x_1837_);
v_i_1827_ = v___x_1838_;
v_b_1829_ = v_fst_1835_;
v___y_1830_ = v_snd_1836_;
goto _start;
}
v___jp_1840_:
{
if (lean_obj_tag(v___y_1841_) == 0)
{
lean_object* v_a_1842_; 
v_a_1842_ = lean_ctor_get(v___y_1841_, 0);
if (lean_obj_tag(v_a_1842_) == 0)
{
lean_dec_ref(v_f_1825_);
return v___y_1841_;
}
else
{
lean_object* v_a_1843_; lean_object* v_fst_1844_; lean_object* v_snd_1845_; 
lean_inc_ref(v_a_1842_);
lean_dec_ref_known(v___y_1841_, 1);
v_a_1843_ = lean_ctor_get(v_a_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref_known(v_a_1842_, 1);
v_fst_1844_ = lean_ctor_get(v_a_1843_, 0);
lean_inc(v_fst_1844_);
v_snd_1845_ = lean_ctor_get(v_a_1843_, 1);
lean_inc(v_snd_1845_);
lean_dec(v_a_1843_);
v_fst_1835_ = v_fst_1844_;
v_snd_1836_ = v_snd_1845_;
goto v___jp_1834_;
}
}
else
{
lean_dec_ref(v_f_1825_);
return v___y_1841_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__19___redArg___boxed(lean_object* v_f_1856_, lean_object* v_as_1857_, lean_object* v_i_1858_, lean_object* v_stop_1859_, lean_object* v_b_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
size_t v_i_boxed_1865_; size_t v_stop_boxed_1866_; lean_object* v_res_1867_; 
v_i_boxed_1865_ = lean_unbox_usize(v_i_1858_);
lean_dec(v_i_1858_);
v_stop_boxed_1866_ = lean_unbox_usize(v_stop_1859_);
lean_dec(v_stop_1859_);
v_res_1867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__19___redArg(v_f_1856_, v_as_1857_, v_i_boxed_1865_, v_stop_boxed_1866_, v_b_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v_as_1857_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17___redArg___boxed(lean_object* v_f_1868_, lean_object* v_x_1869_, lean_object* v_x_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17___redArg(v_f_1868_, v_x_1869_, v_x_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg(lean_object* v_map_1876_, lean_object* v_f_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___f_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___f_1882_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1882_, 0, v_f_1877_);
v___x_1883_ = lean_box(0);
v___x_1884_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17___redArg(v___f_1882_, v_map_1876_, v___x_1883_, v___y_1878_, v___y_1879_, v___y_1880_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg___boxed(lean_object* v_map_1885_, lean_object* v_f_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg(v_map_1885_, v_f_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0___redArg(lean_object* v_s_1892_, lean_object* v_f_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_map_u2081_1898_; lean_object* v_map_u2082_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v_map_u2081_1898_ = lean_ctor_get(v_s_1892_, 0);
lean_inc_ref(v_map_u2081_1898_);
v_map_u2082_1899_ = lean_ctor_get(v_s_1892_, 1);
lean_inc_ref(v_map_u2082_1899_);
lean_dec_ref(v_s_1892_);
v___x_1900_ = lean_box(0);
lean_inc_ref(v_f_1893_);
v___x_1901_ = l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0___redArg(v_f_1893_, v___x_1900_, v_map_u2081_1898_, v___y_1894_, v___y_1895_, v___y_1896_);
lean_dec_ref(v_map_u2081_1898_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
if (lean_obj_tag(v_a_1902_) == 0)
{
lean_dec_ref_known(v_a_1902_, 1);
lean_dec_ref(v_map_u2082_1899_);
lean_dec_ref(v_f_1893_);
return v___x_1901_;
}
else
{
lean_object* v_a_1903_; lean_object* v_snd_1904_; lean_object* v___x_1905_; 
lean_dec_ref_known(v___x_1901_, 1);
v_a_1903_ = lean_ctor_get(v_a_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v_a_1902_, 1);
v_snd_1904_ = lean_ctor_get(v_a_1903_, 1);
lean_inc(v_snd_1904_);
lean_dec(v_a_1903_);
v___x_1905_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg(v_map_u2082_1899_, v_f_1893_, v_snd_1904_, v___y_1895_, v___y_1896_);
return v___x_1905_;
}
}
else
{
lean_dec_ref(v_map_u2082_1899_);
lean_dec_ref(v_f_1893_);
return v___x_1901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0___redArg___boxed(lean_object* v_s_1906_, lean_object* v_f_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0___redArg(v_s_1906_, v_f_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo(lean_object* v_initialRelevant_1917_, lean_object* v_score_1918_, lean_object* v_accept_1919_, lean_object* v_maxSuggestions_1920_, double v_p_1921_, double v_c_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v___x_1926_; lean_object* v_env_1927_; lean_object* v___f_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1926_ = lean_st_ref_get(v_a_1924_);
v_env_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc_ref(v_env_1927_);
lean_dec(v___x_1926_);
v___f_1928_ = lean_alloc_closure((void*)(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1928_, 0, v_accept_1919_);
v___x_1929_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___closed__0));
v___x_1930_ = l_Lean_Environment_constants(v_env_1927_);
v___x_1931_ = l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0___redArg(v___x_1930_, v___f_1928_, v___x_1929_, v_a_1923_, v_a_1924_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; lean_object* v_a_1935_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v___x_1933_ = ((lean_object*)(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___closed__1));
if (lean_obj_tag(v_a_1932_) == 0)
{
lean_object* v_a_1968_; 
v_a_1968_ = lean_ctor_get(v_a_1932_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v_a_1932_, 1);
v_a_1935_ = v_a_1968_;
goto v___jp_1934_;
}
else
{
lean_object* v_a_1969_; lean_object* v_snd_1970_; 
v_a_1969_ = lean_ctor_get(v_a_1932_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v_a_1932_, 1);
v_snd_1970_ = lean_ctor_get(v_a_1969_, 1);
lean_inc(v_snd_1970_);
lean_dec(v_a_1969_);
v_a_1935_ = v_snd_1970_;
goto v___jp_1934_;
}
v___jp_1934_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1936_ = lean_box(0);
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v_initialRelevant_1917_);
lean_ctor_set(v___x_1937_, 1, v___x_1933_);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v_a_1935_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_box_float(v_p_1921_);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v___x_1938_);
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1936_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
v___x_1942_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg(v_score_1918_, v_c_1922_, v_maxSuggestions_1920_, v___x_1941_, v_a_1923_, v_a_1924_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1959_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1959_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1959_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v_fst_1947_; 
v_fst_1947_ = lean_ctor_get(v_a_1943_, 0);
if (lean_obj_tag(v_fst_1947_) == 0)
{
lean_object* v_snd_1948_; lean_object* v_snd_1949_; lean_object* v_snd_1950_; lean_object* v_snd_1951_; lean_object* v___x_1953_; 
v_snd_1948_ = lean_ctor_get(v_a_1943_, 1);
lean_inc(v_snd_1948_);
lean_dec(v_a_1943_);
v_snd_1949_ = lean_ctor_get(v_snd_1948_, 1);
lean_inc(v_snd_1949_);
lean_dec(v_snd_1948_);
v_snd_1950_ = lean_ctor_get(v_snd_1949_, 1);
lean_inc(v_snd_1950_);
lean_dec(v_snd_1949_);
v_snd_1951_ = lean_ctor_get(v_snd_1950_, 1);
lean_inc(v_snd_1951_);
lean_dec(v_snd_1950_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v_snd_1951_);
v___x_1953_ = v___x_1945_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_snd_1951_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
else
{
lean_object* v_val_1955_; lean_object* v___x_1957_; 
lean_inc_ref(v_fst_1947_);
lean_dec(v_a_1943_);
v_val_1955_ = lean_ctor_get(v_fst_1947_, 0);
lean_inc(v_val_1955_);
lean_dec_ref_known(v_fst_1947_, 1);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v_val_1955_);
v___x_1957_ = v___x_1945_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_val_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
v_a_1960_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1942_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1942_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec_ref(v_score_1918_);
lean_dec(v_initialRelevant_1917_);
v_a_1971_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1931_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1931_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___boxed(lean_object* v_initialRelevant_1979_, lean_object* v_score_1980_, lean_object* v_accept_1981_, lean_object* v_maxSuggestions_1982_, lean_object* v_p_1983_, lean_object* v_c_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
double v_p_boxed_1988_; double v_c_boxed_1989_; lean_object* v_res_1990_; 
v_p_boxed_1988_ = lean_unbox_float(v_p_1983_);
lean_dec_ref(v_p_1983_);
v_c_boxed_1989_ = lean_unbox_float(v_c_1984_);
lean_dec_ref(v_c_1984_);
v_res_1990_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo(v_initialRelevant_1979_, v_score_1980_, v_accept_1981_, v_maxSuggestions_1982_, v_p_boxed_1988_, v_c_boxed_1989_, v_a_1985_, v_a_1986_);
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_maxSuggestions_1982_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0(lean_object* v_00_u03b2_1991_, lean_object* v_s_1992_, lean_object* v_f_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0___redArg(v_s_1992_, v_f_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0___boxed(lean_object* v_00_u03b2_1999_, lean_object* v_s_2000_, lean_object* v_f_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0(v_00_u03b2_1999_, v_s_2000_, v_f_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6(lean_object* v_n_2007_, lean_object* v_as_2008_, lean_object* v_lo_2009_, lean_object* v_hi_2010_, lean_object* v_w_2011_, lean_object* v_hlo_2012_, lean_object* v_hhi_2013_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg(v_n_2007_, v_as_2008_, v_lo_2009_, v_hi_2010_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___boxed(lean_object* v_n_2015_, lean_object* v_as_2016_, lean_object* v_lo_2017_, lean_object* v_hi_2018_, lean_object* v_w_2019_, lean_object* v_hlo_2020_, lean_object* v_hhi_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6(v_n_2015_, v_as_2016_, v_lo_2017_, v_hi_2018_, v_w_2019_, v_hlo_2020_, v_hhi_2021_);
lean_dec(v_hi_2018_);
lean_dec(v_n_2015_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12(lean_object* v_score_2023_, double v_c_2024_, lean_object* v_maxSuggestions_2025_, lean_object* v_inst_2026_, lean_object* v_a_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg(v_score_2023_, v_c_2024_, v_maxSuggestions_2025_, v_a_2027_, v___y_2028_, v___y_2029_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___boxed(lean_object* v_score_2032_, lean_object* v_c_2033_, lean_object* v_maxSuggestions_2034_, lean_object* v_inst_2035_, lean_object* v_a_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
double v_c_boxed_2040_; lean_object* v_res_2041_; 
v_c_boxed_2040_ = lean_unbox_float(v_c_2033_);
lean_dec_ref(v_c_2033_);
v_res_2041_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12(v_score_2032_, v_c_boxed_2040_, v_maxSuggestions_2034_, v_inst_2035_, v_a_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v_maxSuggestions_2034_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0(lean_object* v_00_u03b2_2042_, lean_object* v_f_2043_, lean_object* v_init_2044_, lean_object* v_b_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0___redArg(v_f_2043_, v_init_2044_, v_b_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2051_, lean_object* v_f_2052_, lean_object* v_init_2053_, lean_object* v_b_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0(v_00_u03b2_2051_, v_f_2052_, v_init_2053_, v_b_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec_ref(v_b_2054_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1(lean_object* v_00_u03b2_2060_, lean_object* v_map_2061_, lean_object* v_f_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg(v_map_2061_, v_f_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2068_, lean_object* v_map_2069_, lean_object* v_f_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1(v_00_u03b2_2068_, v_map_2069_, v_f_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__8(lean_object* v_n_2076_, lean_object* v_lo_2077_, lean_object* v_hi_2078_, lean_object* v_hhi_2079_, lean_object* v_pivot_2080_, lean_object* v_as_2081_, lean_object* v_i_2082_, lean_object* v_k_2083_, lean_object* v_ilo_2084_, lean_object* v_ik_2085_, lean_object* v_w_2086_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__8___redArg(v_hi_2078_, v_pivot_2080_, v_as_2081_, v_i_2082_, v_k_2083_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__8___boxed(lean_object* v_n_2088_, lean_object* v_lo_2089_, lean_object* v_hi_2090_, lean_object* v_hhi_2091_, lean_object* v_pivot_2092_, lean_object* v_as_2093_, lean_object* v_i_2094_, lean_object* v_k_2095_, lean_object* v_ilo_2096_, lean_object* v_ik_2097_, lean_object* v_w_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__8(v_n_2088_, v_lo_2089_, v_hi_2090_, v_hhi_2091_, v_pivot_2092_, v_as_2093_, v_i_2094_, v_k_2095_, v_ilo_2096_, v_ik_2097_, v_w_2098_);
lean_dec_ref(v_pivot_2092_);
lean_dec(v_hi_2090_);
lean_dec(v_lo_2089_);
lean_dec(v_n_2088_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2100_, lean_object* v_f_2101_, lean_object* v_b_2102_, lean_object* v_acc_2103_, lean_object* v_i_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0_spec__1___redArg(v_f_2101_, v_b_2102_, v_acc_2103_, v_i_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2110_, lean_object* v_f_2111_, lean_object* v_b_2112_, lean_object* v_acc_2113_, lean_object* v_i_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0_spec__1(v_00_u03b2_2110_, v_f_2111_, v_b_2112_, v_acc_2113_, v_i_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec_ref(v_b_2112_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3___redArg(lean_object* v_map_2120_, lean_object* v_f_2121_, lean_object* v_init_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17___redArg(v_f_2121_, v_map_2120_, v_init_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_map_2128_, lean_object* v_f_2129_, lean_object* v_init_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3___redArg(v_map_2128_, v_f_2129_, v_init_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_2136_, lean_object* v_00_u03b2_2137_, lean_object* v_map_2138_, lean_object* v_f_2139_, lean_object* v_init_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17___redArg(v_f_2139_, v_map_2138_, v_init_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_2146_, lean_object* v_00_u03b2_2147_, lean_object* v_map_2148_, lean_object* v_f_2149_, lean_object* v_init_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3(v_00_u03c3_2146_, v_00_u03b2_2147_, v_map_2148_, v_f_2149_, v_init_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17(lean_object* v_00_u03c3_2156_, lean_object* v_00_u03b1_2157_, lean_object* v_00_u03b2_2158_, lean_object* v_f_2159_, lean_object* v_x_2160_, lean_object* v_x_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17___redArg(v_f_2159_, v_x_2160_, v_x_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17___boxed(lean_object* v_00_u03c3_2167_, lean_object* v_00_u03b1_2168_, lean_object* v_00_u03b2_2169_, lean_object* v_f_2170_, lean_object* v_x_2171_, lean_object* v_x_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17(v_00_u03c3_2167_, v_00_u03b1_2168_, v_00_u03b2_2169_, v_f_2170_, v_x_2171_, v_x_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__19(lean_object* v_00_u03b1_2178_, lean_object* v_00_u03b2_2179_, lean_object* v_00_u03c3_2180_, lean_object* v_f_2181_, lean_object* v_as_2182_, size_t v_i_2183_, size_t v_stop_2184_, lean_object* v_b_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__19___redArg(v_f_2181_, v_as_2182_, v_i_2183_, v_stop_2184_, v_b_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__19___boxed(lean_object* v_00_u03b1_2191_, lean_object* v_00_u03b2_2192_, lean_object* v_00_u03c3_2193_, lean_object* v_f_2194_, lean_object* v_as_2195_, lean_object* v_i_2196_, lean_object* v_stop_2197_, lean_object* v_b_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
size_t v_i_boxed_2203_; size_t v_stop_boxed_2204_; lean_object* v_res_2205_; 
v_i_boxed_2203_ = lean_unbox_usize(v_i_2196_);
lean_dec(v_i_2196_);
v_stop_boxed_2204_ = lean_unbox_usize(v_stop_2197_);
lean_dec(v_stop_2197_);
v_res_2205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__19(v_00_u03b1_2191_, v_00_u03b2_2192_, v_00_u03c3_2193_, v_f_2194_, v_as_2195_, v_i_boxed_2203_, v_stop_boxed_2204_, v_b_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec_ref(v_as_2195_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__20(lean_object* v_00_u03c3_2206_, lean_object* v_00_u03b1_2207_, lean_object* v_00_u03b2_2208_, lean_object* v_f_2209_, lean_object* v_keys_2210_, lean_object* v_vals_2211_, lean_object* v_heq_2212_, lean_object* v_i_2213_, lean_object* v_acc_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__20___redArg(v_f_2209_, v_keys_2210_, v_vals_2211_, v_i_2213_, v_acc_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__20___boxed(lean_object* v_00_u03c3_2220_, lean_object* v_00_u03b1_2221_, lean_object* v_00_u03b2_2222_, lean_object* v_f_2223_, lean_object* v_keys_2224_, lean_object* v_vals_2225_, lean_object* v_heq_2226_, lean_object* v_i_2227_, lean_object* v_acc_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__3_spec__17_spec__20(v_00_u03c3_2220_, v_00_u03b1_2221_, v_00_u03b2_2222_, v_f_2223_, v_keys_2224_, v_vals_2225_, v_heq_2226_, v_i_2227_, v_acc_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec_ref(v_vals_2225_);
lean_dec_ref(v_keys_2224_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_mepoSelector___lam__0(lean_object* v_env_2234_, lean_object* v_ci_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v___x_2239_; uint8_t v___x_2240_; uint8_t v___x_2241_; 
v___x_2239_ = l_Lean_ConstantInfo_name(v_ci_2235_);
v___x_2240_ = 0;
lean_inc(v___x_2239_);
lean_inc_ref(v_env_2234_);
v___x_2241_ = l_Lean_LibrarySuggestions_isDeniedPremise(v_env_2234_, v___x_2239_, v___x_2240_);
if (v___x_2241_ == 0)
{
uint8_t v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2242_ = l_Lean_wasOriginallyTheorem(v_env_2234_, v___x_2239_);
v___x_2243_ = lean_box(v___x_2242_);
v___x_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
return v___x_2244_;
}
else
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
lean_dec(v___x_2239_);
lean_dec_ref(v_env_2234_);
v___x_2245_ = lean_box(v___x_2240_);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
return v___x_2246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_mepoSelector___lam__0___boxed(lean_object* v_env_2247_, lean_object* v_ci_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_LibrarySuggestions_mepoSelector___lam__0(v_env_2247_, v_ci_2248_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec_ref(v_ci_2248_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0___redArg(lean_object* v_t_2253_, lean_object* v_k_2254_, lean_object* v_fallback_2255_){
_start:
{
if (lean_obj_tag(v_t_2253_) == 0)
{
lean_object* v_k_2256_; lean_object* v_v_2257_; lean_object* v_l_2258_; lean_object* v_r_2259_; uint8_t v___x_2260_; 
v_k_2256_ = lean_ctor_get(v_t_2253_, 1);
v_v_2257_ = lean_ctor_get(v_t_2253_, 2);
v_l_2258_ = lean_ctor_get(v_t_2253_, 3);
v_r_2259_ = lean_ctor_get(v_t_2253_, 4);
v___x_2260_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2254_, v_k_2256_);
switch(v___x_2260_)
{
case 0:
{
v_t_2253_ = v_l_2258_;
goto _start;
}
case 1:
{
lean_inc(v_v_2257_);
return v_v_2257_;
}
default: 
{
v_t_2253_ = v_r_2259_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2255_);
return v_fallback_2255_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0___redArg___boxed(lean_object* v_t_2263_, lean_object* v_k_2264_, lean_object* v_fallback_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0___redArg(v_t_2263_, v_k_2264_, v_fallback_2265_);
lean_dec(v_fallback_2265_);
lean_dec(v_k_2264_);
lean_dec(v_t_2263_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_mepoSelector___lam__1(lean_object* v_a_2267_, lean_object* v_n_2268_){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = lean_unsigned_to_nat(0u);
v___x_2270_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0___redArg(v_a_2267_, v_n_2268_, v___x_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_mepoSelector___lam__1___boxed(lean_object* v_a_2271_, lean_object* v_n_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_LibrarySuggestions_mepoSelector___lam__1(v_a_2271_, v_n_2272_);
lean_dec(v_n_2272_);
lean_dec(v_a_2271_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_mepoSelector(uint8_t v_useRarity_2275_, double v_p_2276_, double v_c_2277_, lean_object* v_g_2278_, lean_object* v_config_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_MVarId_getRelevantConstants(v_g_2278_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; lean_object* v_env_2288_; lean_object* v___f_2289_; lean_object* v_score_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2285_, 1);
v___x_2287_ = lean_st_ref_get(v_a_2283_);
v_env_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc_ref(v_env_2288_);
lean_dec(v___x_2287_);
v___f_2289_ = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_mepoSelector___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2289_, 0, v_env_2288_);
if (v_useRarity_2275_ == 0)
{
lean_object* v___x_2306_; 
v___x_2306_ = ((lean_object*)(l_Lean_LibrarySuggestions_mepoSelector___closed__0));
v_score_2291_ = v___x_2306_;
v___y_2292_ = v_a_2282_;
v___y_2293_ = v_a_2283_;
goto v___jp_2290_;
}
else
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(v_a_2283_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___f_2309_; lean_object* v___x_2310_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref_known(v___x_2307_, 1);
v___f_2309_ = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_mepoSelector___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2309_, 0, v_a_2308_);
v___x_2310_ = lean_alloc_closure((void*)(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore___boxed), 3, 1);
lean_closure_set(v___x_2310_, 0, v___f_2309_);
v_score_2291_ = v___x_2310_;
v___y_2292_ = v_a_2282_;
v___y_2293_ = v_a_2283_;
goto v___jp_2290_;
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec_ref(v___f_2289_);
lean_dec(v_a_2286_);
lean_dec_ref(v_config_2279_);
v_a_2311_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2307_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2307_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
v___jp_2290_:
{
lean_object* v_maxSuggestions_2294_; lean_object* v___x_2295_; 
v_maxSuggestions_2294_ = lean_ctor_get(v_config_2279_, 0);
lean_inc(v_maxSuggestions_2294_);
lean_dec_ref(v_config_2279_);
v___x_2295_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo(v_a_2286_, v_score_2291_, v___f_2289_, v_maxSuggestions_2294_, v_p_2276_, v_c_2277_, v___y_2292_, v___y_2293_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2305_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2298_ = v___x_2295_;
v_isShared_2299_ = v_isSharedCheck_2305_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2295_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2305_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2300_ = lean_unsigned_to_nat(0u);
v___x_2301_ = l_Array_extract___redArg(v_a_2296_, v___x_2300_, v_maxSuggestions_2294_);
lean_dec(v_a_2296_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v___x_2301_);
v___x_2303_ = v___x_2298_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v___x_2301_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
else
{
lean_dec(v_maxSuggestions_2294_);
return v___x_2295_;
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec_ref(v_config_2279_);
v_a_2319_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2285_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2285_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_mepoSelector___boxed(lean_object* v_useRarity_2327_, lean_object* v_p_2328_, lean_object* v_c_2329_, lean_object* v_g_2330_, lean_object* v_config_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
uint8_t v_useRarity_boxed_2337_; double v_p_boxed_2338_; double v_c_boxed_2339_; lean_object* v_res_2340_; 
v_useRarity_boxed_2337_ = lean_unbox(v_useRarity_2327_);
v_p_boxed_2338_ = lean_unbox_float(v_p_2328_);
lean_dec_ref(v_p_2328_);
v_c_boxed_2339_ = lean_unbox_float(v_c_2329_);
lean_dec_ref(v_c_2329_);
v_res_2340_ = l_Lean_LibrarySuggestions_mepoSelector(v_useRarity_boxed_2337_, v_p_boxed_2338_, v_c_boxed_2339_, v_g_2330_, v_config_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0(lean_object* v_00_u03b4_2341_, lean_object* v_t_2342_, lean_object* v_k_2343_, lean_object* v_fallback_2344_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0___redArg(v_t_2342_, v_k_2343_, v_fallback_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0___boxed(lean_object* v_00_u03b4_2346_, lean_object* v_t_2347_, lean_object* v_k_2348_, lean_object* v_fallback_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0(v_00_u03b4_2346_, v_t_2347_, v_k_2348_, v_fallback_2349_);
lean_dec(v_fallback_2349_);
lean_dec(v_k_2348_);
lean_dec(v_t_2347_);
return v_res_2350_;
}
}
lean_object* runtime_initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_LibrarySuggestions_SymbolFrequency(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_LibrarySuggestions_MePo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_LibrarySuggestions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_LibrarySuggestions_MePo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin);
lean_object* initialize_Lean_LibrarySuggestions_SymbolFrequency(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LibrarySuggestions_MePo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_LibrarySuggestions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LibrarySuggestions_MePo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_LibrarySuggestions_MePo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_LibrarySuggestions_MePo(builtin);
}
#ifdef __cplusplus
}
#endif
