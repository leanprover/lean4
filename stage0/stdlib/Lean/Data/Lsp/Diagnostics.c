// Lean compiler output
// Module: Lean.Data.Lsp.Diagnostics
// Imports: public import Lean.Data.Lsp.Basic public import Lean.Data.Lsp.Utf16
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Lsp_instFromJsonLocation_fromJson(lean_object*);
lean_object* l_Lean_instToJsonBool___lam__0___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instBEqLocation_beq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Lsp_instBEqRange_beq(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instBEqRange_beq___boxed(lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqBool___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
lean_object* l_Array_instBEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_instBEq___private__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Lsp_instToJsonLocation_toJson(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Lsp_instInhabitedRange_default;
lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
lean_object* l_Array_fromJson_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Option_fromJson_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getInt_x3f(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_compare(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f___boxed(lean_object*);
lean_object* l_Lean_instFromJsonJson___lam__0(lean_object*);
uint8_t l_Lean_Lsp_instOrdLocation_ord(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
extern lean_object* l_Lean_Lsp_instInhabitedLocation_default;
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_toJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToJsonString___lam__0(lean_object*);
lean_object* l_Lean_Json_opt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedDiagnosticSeverity_default;
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedDiagnosticSeverity;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticSeverity_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticSeverity_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqDiagnosticSeverity_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqDiagnosticSeverity = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticSeverity_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticSeverity_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instOrdDiagnosticSeverity_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0 = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instOrdDiagnosticSeverity = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticSeverity___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "unknown DiagnosticSeverity '"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value;
static lean_once_cell_t l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0;
static lean_once_cell_t l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1;
static lean_once_cell_t l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2;
static lean_once_cell_t l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3;
static lean_once_cell_t l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4;
static lean_once_cell_t l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5;
static lean_once_cell_t l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6;
static lean_once_cell_t l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_int_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_int_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_string_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_string_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0;
static lean_once_cell_t l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticCode_default;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticCode;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticCode_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticCode_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqDiagnosticCode_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticCode___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticCode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqDiagnosticCode = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticCode___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticCode_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticCode_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instOrdDiagnosticCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instOrdDiagnosticCode_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instOrdDiagnosticCode___closed__0 = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticCode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instOrdDiagnosticCode = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticCode___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "expected string or integer diagnostic code, got '"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDiagnosticCode = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticCode___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDiagnosticCode___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticCode___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticCode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDiagnosticCode = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticCode___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedDiagnosticTag_default;
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedDiagnosticTag;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticTag_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticTag_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqDiagnosticTag_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticTag___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticTag_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticTag_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instOrdDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instOrdDiagnosticTag_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instOrdDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instOrdDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticTag___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unknown DiagnosticTag"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticTag___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticTag___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDiagnosticTag___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedLeanDiagnosticTag_default;
LEAN_EXPORT uint8_t l_Lean_Lsp_instInhabitedLeanDiagnosticTag;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqLeanDiagnosticTag_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqLeanDiagnosticTag_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqLeanDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdLeanDiagnosticTag_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdLeanDiagnosticTag_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instOrdLeanDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instOrdLeanDiagnosticTag_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instOrdLeanDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instOrdLeanDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instOrdLeanDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instOrdLeanDiagnosticTag___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "unknown LeanDiagnosticTag"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanDiagnosticTag = (const lean_object*)&l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0_value;
static const lean_string_object l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0 = (const lean_object*)&l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0_value;
static lean_once_cell_t l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqDiagnosticRelatedInformation = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1_value;
static const lean_array_object l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "DiagnosticRelatedInformation"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(144, 67, 100, 141, 182, 93, 157, 48)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 206, 14, 113, 158, 249, 116, 159)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(149, 62, 76, 216, 222, 7, 163, 13)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0 = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instOrdDiagnosticRelatedInformation = (const lean_object*)&l_Lean_Lsp_instOrdDiagnosticRelatedInformation___closed__0_value;
static lean_once_cell_t l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqRange_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1;
static lean_once_cell_t l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2;
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instBEq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instBEqDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3_value;
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instBEq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instBEqLeanDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4_value;
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instBEq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Lsp_instBEqDiagnosticRelatedInformation___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5_value;
static const lean_closure_object l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_instBEq___private__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6 = (const lean_object*)&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonRange_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonLeanDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_toJson, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonDiagnosticRelatedInformation___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5_value;
static const lean_closure_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "range"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fullRange"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "severity"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isSilent"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "source"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tags"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "leanTags"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "relatedInformation"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15_value;
static const lean_string_object l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16 = (const lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRange_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "DiagnosticWith"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(215, 36, 183, 1, 15, 160, 190, 39)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(113, 10, 234, 83, 106, 95, 218, 176)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fullRange\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(204, 14, 121, 252, 204, 139, 33, 252)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticSeverity___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "severity\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__16 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(136, 53, 226, 217, 90, 118, 120, 32)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getBool_x3f___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__21_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "isSilent\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__23 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__23_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(192, 110, 237, 190, 164, 148, 251, 95)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticCode___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "code\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__29 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__29_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__29_value),LEAN_SCALAR_PTR_LITERAL(96, 225, 246, 128, 47, 4, 255, 46)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getStr_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__34 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__34_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__34_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "source\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__36 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__36_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__36_value),LEAN_SCALAR_PTR_LITERAL(6, 190, 134, 180, 155, 172, 192, 107)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__43_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tags\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__45 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__45_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__45_value),LEAN_SCALAR_PTR_LITERAL(96, 97, 143, 141, 248, 70, 73, 149)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__50_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "leanTags\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__52 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__52_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__52_value),LEAN_SCALAR_PTR_LITERAL(202, 184, 187, 33, 211, 98, 60, 106)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__57_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "relatedInformation\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__59 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__59_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__59_value),LEAN_SCALAR_PTR_LITERAL(21, 251, 114, 194, 100, 169, 63, 219)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instFromJsonJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_fromJson_x3f, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__64_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "data\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__66 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__66_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__66_value),LEAN_SCALAR_PTR_LITERAL(14, 29, 170, 31, 135, 79, 138, 199)}};
static const lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67 = (const lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0 = (const lean_object*)&l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1 = (const lean_object*)&l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default = (const lean_object*)&l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instInhabitedPublishDiagnosticsParams = (const lean_object*)&l_Lean_Lsp_instInhabitedPublishDiagnosticsParams_default___closed__1_value;
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instBEqPublishDiagnosticsParams = (const lean_object*)&l_Lean_Lsp_instBEqPublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2(lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "uri"};
static const lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "isIncremental"};
static const lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "diagnostics"};
static const lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams = (const lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams___closed__0_value;
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24(lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0 = (const lean_object*)&l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0_value;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "PublishDiagnosticsParams"};
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 161, 220, 51, 147, 166, 27, 251)}};
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 169, 49, 149, 57, 117, 3, 84)}};
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7;
static const lean_string_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "version\?"};
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__8_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__8_value),LEAN_SCALAR_PTR_LITERAL(251, 148, 229, 74, 154, 149, 54, 79)}};
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12;
static const lean_string_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "isIncremental\?"};
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__13_value),LEAN_SCALAR_PTR_LITERAL(93, 146, 63, 25, 119, 245, 185, 30)}};
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17;
static const lean_ctor_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(236, 43, 109, 94, 169, 251, 160, 225)}};
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20;
static lean_once_cell_t l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams = (const lean_object*)&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
uint8_t v_x_boxed_7_; lean_object* v_res_8_; 
v_x_boxed_7_ = lean_unbox(v_x_6_);
v_res_8_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_x_boxed_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_toCtorIdx(uint8_t v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_toCtorIdx___boxed(lean_object* v_x_11_){
_start:
{
uint8_t v_x_4__boxed_12_; lean_object* v_res_13_; 
v_x_4__boxed_12_ = lean_unbox(v_x_11_);
v_res_13_ = l_Lean_Lsp_DiagnosticSeverity_toCtorIdx(v_x_4__boxed_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg(lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg___boxed(lean_object* v_k_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Lsp_DiagnosticSeverity_ctorElim___redArg(v_k_15_);
lean_dec(v_k_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, uint8_t v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_inc(v_k_21_);
return v_k_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_ctorElim___boxed(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
uint8_t v_t_boxed_27_; lean_object* v_res_28_; 
v_t_boxed_27_ = lean_unbox(v_t_24_);
v_res_28_ = l_Lean_Lsp_DiagnosticSeverity_ctorElim(v_motive_22_, v_ctorIdx_23_, v_t_boxed_27_, v_h_25_, v_k_26_);
lean_dec(v_k_26_);
lean_dec(v_ctorIdx_23_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg(lean_object* v_error_29_){
_start:
{
lean_inc(v_error_29_);
return v_error_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg___boxed(lean_object* v_error_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Lsp_DiagnosticSeverity_error_elim___redArg(v_error_30_);
lean_dec(v_error_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim(lean_object* v_motive_32_, uint8_t v_t_33_, lean_object* v_h_34_, lean_object* v_error_35_){
_start:
{
lean_inc(v_error_35_);
return v_error_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_error_elim___boxed(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_error_39_){
_start:
{
uint8_t v_t_boxed_40_; lean_object* v_res_41_; 
v_t_boxed_40_ = lean_unbox(v_t_37_);
v_res_41_ = l_Lean_Lsp_DiagnosticSeverity_error_elim(v_motive_36_, v_t_boxed_40_, v_h_38_, v_error_39_);
lean_dec(v_error_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg(lean_object* v_warning_42_){
_start:
{
lean_inc(v_warning_42_);
return v_warning_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg___boxed(lean_object* v_warning_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Lsp_DiagnosticSeverity_warning_elim___redArg(v_warning_43_);
lean_dec(v_warning_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim(lean_object* v_motive_45_, uint8_t v_t_46_, lean_object* v_h_47_, lean_object* v_warning_48_){
_start:
{
lean_inc(v_warning_48_);
return v_warning_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_warning_elim___boxed(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_warning_52_){
_start:
{
uint8_t v_t_boxed_53_; lean_object* v_res_54_; 
v_t_boxed_53_ = lean_unbox(v_t_50_);
v_res_54_ = l_Lean_Lsp_DiagnosticSeverity_warning_elim(v_motive_49_, v_t_boxed_53_, v_h_51_, v_warning_52_);
lean_dec(v_warning_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg(lean_object* v_information_55_){
_start:
{
lean_inc(v_information_55_);
return v_information_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg___boxed(lean_object* v_information_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Lsp_DiagnosticSeverity_information_elim___redArg(v_information_56_);
lean_dec(v_information_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim(lean_object* v_motive_58_, uint8_t v_t_59_, lean_object* v_h_60_, lean_object* v_information_61_){
_start:
{
lean_inc(v_information_61_);
return v_information_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_information_elim___boxed(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_information_65_){
_start:
{
uint8_t v_t_boxed_66_; lean_object* v_res_67_; 
v_t_boxed_66_ = lean_unbox(v_t_63_);
v_res_67_ = l_Lean_Lsp_DiagnosticSeverity_information_elim(v_motive_62_, v_t_boxed_66_, v_h_64_, v_information_65_);
lean_dec(v_information_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg(lean_object* v_hint_68_){
_start:
{
lean_inc(v_hint_68_);
return v_hint_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg___boxed(lean_object* v_hint_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Lsp_DiagnosticSeverity_hint_elim___redArg(v_hint_69_);
lean_dec(v_hint_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim(lean_object* v_motive_71_, uint8_t v_t_72_, lean_object* v_h_73_, lean_object* v_hint_74_){
_start:
{
lean_inc(v_hint_74_);
return v_hint_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticSeverity_hint_elim___boxed(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_hint_78_){
_start:
{
uint8_t v_t_boxed_79_; lean_object* v_res_80_; 
v_t_boxed_79_ = lean_unbox(v_t_76_);
v_res_80_ = l_Lean_Lsp_DiagnosticSeverity_hint_elim(v_motive_75_, v_t_boxed_79_, v_h_77_, v_hint_78_);
lean_dec(v_hint_78_);
return v_res_80_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDiagnosticSeverity_default(void){
_start:
{
uint8_t v___x_81_; 
v___x_81_ = 0;
return v___x_81_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDiagnosticSeverity(void){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = 0;
return v___x_82_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticSeverity_beq(uint8_t v_x_83_, uint8_t v_y_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_85_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_x_83_);
v___x_86_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_y_84_);
v___x_87_ = lean_nat_dec_eq(v___x_85_, v___x_86_);
lean_dec(v___x_86_);
lean_dec(v___x_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticSeverity_beq___boxed(lean_object* v_x_88_, lean_object* v_y_89_){
_start:
{
uint8_t v_x_17__boxed_90_; uint8_t v_y_18__boxed_91_; uint8_t v_res_92_; lean_object* v_r_93_; 
v_x_17__boxed_90_ = lean_unbox(v_x_88_);
v_y_18__boxed_91_ = lean_unbox(v_y_89_);
v_res_92_ = l_Lean_Lsp_instBEqDiagnosticSeverity_beq(v_x_17__boxed_90_, v_y_18__boxed_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticSeverity_ord(uint8_t v_x_96_, uint8_t v_y_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_98_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_x_96_);
v___x_99_ = l_Lean_Lsp_DiagnosticSeverity_ctorIdx(v_y_97_);
v___x_100_ = lean_nat_dec_lt(v___x_98_, v___x_99_);
if (v___x_100_ == 0)
{
uint8_t v___x_101_; 
v___x_101_ = lean_nat_dec_eq(v___x_98_, v___x_99_);
lean_dec(v___x_99_);
lean_dec(v___x_98_);
if (v___x_101_ == 0)
{
uint8_t v___x_102_; 
v___x_102_ = 2;
return v___x_102_;
}
else
{
uint8_t v___x_103_; 
v___x_103_ = 1;
return v___x_103_;
}
}
else
{
uint8_t v___x_104_; 
lean_dec(v___x_99_);
lean_dec(v___x_98_);
v___x_104_ = 0;
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticSeverity_ord___boxed(lean_object* v_x_105_, lean_object* v_y_106_){
_start:
{
uint8_t v_x_30__boxed_107_; uint8_t v_y_31__boxed_108_; uint8_t v_res_109_; lean_object* v_r_110_; 
v_x_30__boxed_107_ = lean_unbox(v_x_105_);
v_y_31__boxed_108_ = lean_unbox(v_y_106_);
v_res_109_ = l_Lean_Lsp_instOrdDiagnosticSeverity_ord(v_x_30__boxed_107_, v_y_31__boxed_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0(lean_object* v_j_127_){
_start:
{
lean_object* v___x_136_; 
lean_inc(v_j_127_);
v___x_136_ = l_Lean_Json_getNat_x3f(v_j_127_);
if (lean_obj_tag(v___x_136_) == 1)
{
lean_object* v_a_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_137_);
lean_dec_ref_known(v___x_136_, 1);
v___x_138_ = lean_unsigned_to_nat(1u);
v___x_139_ = lean_nat_dec_eq(v_a_137_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(2u);
v___x_141_ = lean_nat_dec_eq(v_a_137_, v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(3u);
v___x_143_ = lean_nat_dec_eq(v_a_137_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(4u);
v___x_145_ = lean_nat_dec_eq(v_a_137_, v___x_144_);
lean_dec(v_a_137_);
if (v___x_145_ == 0)
{
goto v___jp_128_;
}
else
{
lean_object* v___x_146_; 
lean_dec(v_j_127_);
v___x_146_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__2));
return v___x_146_;
}
}
else
{
lean_object* v___x_147_; 
lean_dec(v_a_137_);
lean_dec(v_j_127_);
v___x_147_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__3));
return v___x_147_;
}
}
else
{
lean_object* v___x_148_; 
lean_dec(v_a_137_);
lean_dec(v_j_127_);
v___x_148_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__4));
return v___x_148_;
}
}
else
{
lean_object* v___x_149_; 
lean_dec(v_a_137_);
lean_dec(v_j_127_);
v___x_149_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__5));
return v___x_149_;
}
}
else
{
lean_dec_ref(v___x_136_);
goto v___jp_128_;
}
v___jp_128_:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_129_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0));
v___x_130_ = lean_unsigned_to_nat(80u);
v___x_131_ = l_Lean_Json_pretty(v_j_127_, v___x_130_);
v___x_132_ = lean_string_append(v___x_129_, v___x_131_);
lean_dec_ref(v___x_131_);
v___x_133_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_134_ = lean_string_append(v___x_132_, v___x_133_);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = l_Lean_JsonNumber_fromNat(v___x_152_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__0);
v___x_155_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(2u);
v___x_157_ = l_Lean_JsonNumber_fromNat(v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__2);
v___x_159_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_unsigned_to_nat(3u);
v___x_161_ = l_Lean_JsonNumber_fromNat(v___x_160_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__4);
v___x_163_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(4u);
v___x_165_ = l_Lean_JsonNumber_fromNat(v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__6);
v___x_167_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0(uint8_t v_x_168_){
_start:
{
switch(v_x_168_)
{
case 0:
{
lean_object* v___x_169_; 
v___x_169_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
return v___x_169_;
}
case 1:
{
lean_object* v___x_170_; 
v___x_170_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
return v___x_170_;
}
case 2:
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5);
return v___x_171_;
}
default: 
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7);
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___boxed(lean_object* v_x_173_){
_start:
{
uint8_t v_x_106__boxed_174_; lean_object* v_res_175_; 
v_x_106__boxed_174_ = lean_unbox(v_x_173_);
v_res_175_ = l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0(v_x_106__boxed_174_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorIdx(lean_object* v_x_178_){
_start:
{
if (lean_obj_tag(v_x_178_) == 0)
{
lean_object* v___x_179_; 
v___x_179_ = lean_unsigned_to_nat(0u);
return v___x_179_;
}
else
{
lean_object* v___x_180_; 
v___x_180_ = lean_unsigned_to_nat(1u);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorIdx___boxed(lean_object* v_x_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Lsp_DiagnosticCode_ctorIdx(v_x_181_);
lean_dec_ref(v_x_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(lean_object* v_t_183_, lean_object* v_k_184_){
_start:
{
if (lean_obj_tag(v_t_183_) == 0)
{
lean_object* v_i_185_; lean_object* v___x_186_; 
v_i_185_ = lean_ctor_get(v_t_183_, 0);
lean_inc(v_i_185_);
lean_dec_ref_known(v_t_183_, 1);
v___x_186_ = lean_apply_1(v_k_184_, v_i_185_);
return v___x_186_;
}
else
{
lean_object* v_s_187_; lean_object* v___x_188_; 
v_s_187_ = lean_ctor_get(v_t_183_, 0);
lean_inc_ref(v_s_187_);
lean_dec_ref_known(v_t_183_, 1);
v___x_188_ = lean_apply_1(v_k_184_, v_s_187_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim(lean_object* v_motive_189_, lean_object* v_ctorIdx_190_, lean_object* v_t_191_, lean_object* v_h_192_, lean_object* v_k_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_191_, v_k_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_ctorElim___boxed(lean_object* v_motive_195_, lean_object* v_ctorIdx_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_k_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Lsp_DiagnosticCode_ctorElim(v_motive_195_, v_ctorIdx_196_, v_t_197_, v_h_198_, v_k_199_);
lean_dec(v_ctorIdx_196_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_int_elim___redArg(lean_object* v_t_201_, lean_object* v_int_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_201_, v_int_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_int_elim(lean_object* v_motive_204_, lean_object* v_t_205_, lean_object* v_h_206_, lean_object* v_int_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_205_, v_int_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_string_elim___redArg(lean_object* v_t_209_, lean_object* v_string_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_209_, v_string_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticCode_string_elim(lean_object* v_motive_212_, lean_object* v_t_213_, lean_object* v_h_214_, lean_object* v_string_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Lsp_DiagnosticCode_ctorElim___redArg(v_t_213_, v_string_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_nat_to_int(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_obj_once(&l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0, &l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0_once, _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__0);
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default(void){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_obj_once(&l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1, &l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1_once, _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default___closed__1);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticCode(void){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Lsp_instInhabitedDiagnosticCode_default;
return v___x_222_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticCode_beq(lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
if (lean_obj_tag(v_x_223_) == 0)
{
if (lean_obj_tag(v_x_224_) == 0)
{
lean_object* v_i_225_; lean_object* v_i_226_; uint8_t v___x_227_; 
v_i_225_ = lean_ctor_get(v_x_223_, 0);
v_i_226_ = lean_ctor_get(v_x_224_, 0);
v___x_227_ = lean_int_dec_eq(v_i_225_, v_i_226_);
return v___x_227_;
}
else
{
uint8_t v___x_228_; 
v___x_228_ = 0;
return v___x_228_;
}
}
else
{
if (lean_obj_tag(v_x_224_) == 1)
{
lean_object* v_s_229_; lean_object* v_s_230_; uint8_t v___x_231_; 
v_s_229_ = lean_ctor_get(v_x_223_, 0);
v_s_230_ = lean_ctor_get(v_x_224_, 0);
v___x_231_ = lean_string_dec_eq(v_s_229_, v_s_230_);
return v___x_231_;
}
else
{
uint8_t v___x_232_; 
v___x_232_ = 0;
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticCode_beq___boxed(lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
uint8_t v_res_235_; lean_object* v_r_236_; 
v_res_235_ = l_Lean_Lsp_instBEqDiagnosticCode_beq(v_x_233_, v_x_234_);
lean_dec_ref(v_x_234_);
lean_dec_ref(v_x_233_);
v_r_236_ = lean_box(v_res_235_);
return v_r_236_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticCode_ord(lean_object* v_x_239_, lean_object* v_x_240_){
_start:
{
if (lean_obj_tag(v_x_239_) == 0)
{
if (lean_obj_tag(v_x_240_) == 0)
{
lean_object* v_i_241_; lean_object* v_i_242_; uint8_t v___x_243_; 
v_i_241_ = lean_ctor_get(v_x_239_, 0);
v_i_242_ = lean_ctor_get(v_x_240_, 0);
v___x_243_ = lean_int_dec_lt(v_i_241_, v_i_242_);
if (v___x_243_ == 0)
{
uint8_t v___x_244_; 
v___x_244_ = lean_int_dec_eq(v_i_241_, v_i_242_);
if (v___x_244_ == 0)
{
uint8_t v___x_245_; 
v___x_245_ = 2;
return v___x_245_;
}
else
{
uint8_t v___x_246_; 
v___x_246_ = 1;
return v___x_246_;
}
}
else
{
uint8_t v___x_247_; 
v___x_247_ = 0;
return v___x_247_;
}
}
else
{
uint8_t v___x_248_; 
v___x_248_ = 0;
return v___x_248_;
}
}
else
{
if (lean_obj_tag(v_x_240_) == 0)
{
uint8_t v___x_249_; 
v___x_249_ = 2;
return v___x_249_;
}
else
{
lean_object* v_s_250_; lean_object* v_s_251_; uint8_t v___x_252_; 
v_s_250_ = lean_ctor_get(v_x_239_, 0);
v_s_251_ = lean_ctor_get(v_x_240_, 0);
v___x_252_ = lean_string_compare(v_s_250_, v_s_251_);
if (v___x_252_ == 1)
{
return v___x_252_;
}
else
{
return v___x_252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticCode_ord___boxed(lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
uint8_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l_Lean_Lsp_instOrdDiagnosticCode_ord(v_x_253_, v_x_254_);
lean_dec_ref(v_x_254_);
lean_dec_ref(v_x_253_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0(lean_object* v_x_260_){
_start:
{
switch(lean_obj_tag(v_x_260_))
{
case 2:
{
lean_object* v_n_269_; lean_object* v_mantissa_270_; lean_object* v_exponent_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_n_269_ = lean_ctor_get(v_x_260_, 0);
v_mantissa_270_ = lean_ctor_get(v_n_269_, 0);
v_exponent_271_ = lean_ctor_get(v_n_269_, 1);
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_nat_dec_eq(v_exponent_271_, v___x_272_);
if (v___x_273_ == 0)
{
goto v___jp_261_;
}
else
{
lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_281_; 
lean_inc(v_mantissa_270_);
v_isSharedCheck_281_ = !lean_is_exclusive(v_x_260_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; 
v_unused_282_ = lean_ctor_get(v_x_260_, 0);
lean_dec(v_unused_282_);
v___x_275_ = v_x_260_;
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
else
{
lean_dec(v_x_260_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
lean_ctor_set_tag(v___x_275_, 0);
lean_ctor_set(v___x_275_, 0, v_mantissa_270_);
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_mantissa_270_);
v___x_278_ = v_reuseFailAlloc_280_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; 
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
}
}
case 3:
{
lean_object* v_s_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_291_; 
v_s_283_ = lean_ctor_get(v_x_260_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v_x_260_);
if (v_isSharedCheck_291_ == 0)
{
v___x_285_ = v_x_260_;
v_isShared_286_ = v_isSharedCheck_291_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_s_283_);
lean_dec(v_x_260_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_291_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set_tag(v___x_285_, 1);
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_s_283_);
v___x_288_ = v_reuseFailAlloc_290_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; 
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
}
default: 
{
goto v___jp_261_;
}
}
v___jp_261_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_262_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0));
v___x_263_ = lean_unsigned_to_nat(80u);
v___x_264_ = l_Lean_Json_pretty(v_x_260_, v___x_263_);
v___x_265_ = lean_string_append(v___x_262_, v___x_264_);
lean_dec_ref(v___x_264_);
v___x_266_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_267_ = lean_string_append(v___x_265_, v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticCode___lam__0(lean_object* v_x_294_){
_start:
{
if (lean_obj_tag(v_x_294_) == 0)
{
lean_object* v_i_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_303_; 
v_i_295_ = lean_ctor_get(v_x_294_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v_x_294_);
if (v_isSharedCheck_303_ == 0)
{
v___x_297_ = v_x_294_;
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_i_295_);
lean_dec(v_x_294_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = l_Lean_JsonNumber_fromInt(v_i_295_);
if (v_isShared_298_ == 0)
{
lean_ctor_set_tag(v___x_297_, 2);
lean_ctor_set(v___x_297_, 0, v___x_299_);
v___x_301_ = v___x_297_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
else
{
lean_object* v_s_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
v_s_304_ = lean_ctor_get(v_x_294_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v_x_294_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v_x_294_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_s_304_);
lean_dec(v_x_294_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set_tag(v___x_306_, 3);
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_s_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorIdx(uint8_t v_x_314_){
_start:
{
if (v_x_314_ == 0)
{
lean_object* v___x_315_; 
v___x_315_ = lean_unsigned_to_nat(0u);
return v___x_315_;
}
else
{
lean_object* v___x_316_; 
v___x_316_ = lean_unsigned_to_nat(1u);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorIdx___boxed(lean_object* v_x_317_){
_start:
{
uint8_t v_x_boxed_318_; lean_object* v_res_319_; 
v_x_boxed_318_ = lean_unbox(v_x_317_);
v_res_319_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_x_boxed_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_toCtorIdx(uint8_t v_x_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_toCtorIdx___boxed(lean_object* v_x_322_){
_start:
{
uint8_t v_x_4__boxed_323_; lean_object* v_res_324_; 
v_x_4__boxed_323_ = lean_unbox(v_x_322_);
v_res_324_ = l_Lean_Lsp_DiagnosticTag_toCtorIdx(v_x_4__boxed_323_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___redArg(lean_object* v_k_325_){
_start:
{
lean_inc(v_k_325_);
return v_k_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___redArg___boxed(lean_object* v_k_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Lsp_DiagnosticTag_ctorElim___redArg(v_k_326_);
lean_dec(v_k_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim(lean_object* v_motive_328_, lean_object* v_ctorIdx_329_, uint8_t v_t_330_, lean_object* v_h_331_, lean_object* v_k_332_){
_start:
{
lean_inc(v_k_332_);
return v_k_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___boxed(lean_object* v_motive_333_, lean_object* v_ctorIdx_334_, lean_object* v_t_335_, lean_object* v_h_336_, lean_object* v_k_337_){
_start:
{
uint8_t v_t_boxed_338_; lean_object* v_res_339_; 
v_t_boxed_338_ = lean_unbox(v_t_335_);
v_res_339_ = l_Lean_Lsp_DiagnosticTag_ctorElim(v_motive_333_, v_ctorIdx_334_, v_t_boxed_338_, v_h_336_, v_k_337_);
lean_dec(v_k_337_);
lean_dec(v_ctorIdx_334_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg(lean_object* v_unnecessary_340_){
_start:
{
lean_inc(v_unnecessary_340_);
return v_unnecessary_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg___boxed(lean_object* v_unnecessary_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg(v_unnecessary_341_);
lean_dec(v_unnecessary_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim(lean_object* v_motive_343_, uint8_t v_t_344_, lean_object* v_h_345_, lean_object* v_unnecessary_346_){
_start:
{
lean_inc(v_unnecessary_346_);
return v_unnecessary_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___boxed(lean_object* v_motive_347_, lean_object* v_t_348_, lean_object* v_h_349_, lean_object* v_unnecessary_350_){
_start:
{
uint8_t v_t_boxed_351_; lean_object* v_res_352_; 
v_t_boxed_351_ = lean_unbox(v_t_348_);
v_res_352_ = l_Lean_Lsp_DiagnosticTag_unnecessary_elim(v_motive_347_, v_t_boxed_351_, v_h_349_, v_unnecessary_350_);
lean_dec(v_unnecessary_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg(lean_object* v_deprecated_353_){
_start:
{
lean_inc(v_deprecated_353_);
return v_deprecated_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg___boxed(lean_object* v_deprecated_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg(v_deprecated_354_);
lean_dec(v_deprecated_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim(lean_object* v_motive_356_, uint8_t v_t_357_, lean_object* v_h_358_, lean_object* v_deprecated_359_){
_start:
{
lean_inc(v_deprecated_359_);
return v_deprecated_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___boxed(lean_object* v_motive_360_, lean_object* v_t_361_, lean_object* v_h_362_, lean_object* v_deprecated_363_){
_start:
{
uint8_t v_t_boxed_364_; lean_object* v_res_365_; 
v_t_boxed_364_ = lean_unbox(v_t_361_);
v_res_365_ = l_Lean_Lsp_DiagnosticTag_deprecated_elim(v_motive_360_, v_t_boxed_364_, v_h_362_, v_deprecated_363_);
lean_dec(v_deprecated_363_);
return v_res_365_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDiagnosticTag_default(void){
_start:
{
uint8_t v___x_366_; 
v___x_366_ = 0;
return v___x_366_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDiagnosticTag(void){
_start:
{
uint8_t v___x_367_; 
v___x_367_ = 0;
return v___x_367_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticTag_beq(uint8_t v_x_368_, uint8_t v_y_369_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_370_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_x_368_);
v___x_371_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_y_369_);
v___x_372_ = lean_nat_dec_eq(v___x_370_, v___x_371_);
lean_dec(v___x_371_);
lean_dec(v___x_370_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticTag_beq___boxed(lean_object* v_x_373_, lean_object* v_y_374_){
_start:
{
uint8_t v_x_17__boxed_375_; uint8_t v_y_18__boxed_376_; uint8_t v_res_377_; lean_object* v_r_378_; 
v_x_17__boxed_375_ = lean_unbox(v_x_373_);
v_y_18__boxed_376_ = lean_unbox(v_y_374_);
v_res_377_ = l_Lean_Lsp_instBEqDiagnosticTag_beq(v_x_17__boxed_375_, v_y_18__boxed_376_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticTag_ord(uint8_t v_x_381_, uint8_t v_y_382_){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_383_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_x_381_);
v___x_384_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_y_382_);
v___x_385_ = lean_nat_dec_lt(v___x_383_, v___x_384_);
if (v___x_385_ == 0)
{
uint8_t v___x_386_; 
v___x_386_ = lean_nat_dec_eq(v___x_383_, v___x_384_);
lean_dec(v___x_384_);
lean_dec(v___x_383_);
if (v___x_386_ == 0)
{
uint8_t v___x_387_; 
v___x_387_ = 2;
return v___x_387_;
}
else
{
uint8_t v___x_388_; 
v___x_388_ = 1;
return v___x_388_;
}
}
else
{
uint8_t v___x_389_; 
lean_dec(v___x_384_);
lean_dec(v___x_383_);
v___x_389_ = 0;
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticTag_ord___boxed(lean_object* v_x_390_, lean_object* v_y_391_){
_start:
{
uint8_t v_x_30__boxed_392_; uint8_t v_y_31__boxed_393_; uint8_t v_res_394_; lean_object* v_r_395_; 
v_x_30__boxed_392_ = lean_unbox(v_x_390_);
v_y_31__boxed_393_ = lean_unbox(v_y_391_);
v_res_394_ = l_Lean_Lsp_instOrdDiagnosticTag_ord(v_x_30__boxed_392_, v_y_31__boxed_393_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0(lean_object* v_j_407_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_Json_getNat_x3f(v_j_407_);
if (lean_obj_tag(v___x_410_) == 1)
{
lean_object* v_a_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_410_, 1);
v___x_412_ = lean_unsigned_to_nat(1u);
v___x_413_ = lean_nat_dec_eq(v_a_411_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_unsigned_to_nat(2u);
v___x_415_ = lean_nat_dec_eq(v_a_411_, v___x_414_);
lean_dec(v_a_411_);
if (v___x_415_ == 0)
{
goto v___jp_408_;
}
else
{
lean_object* v___x_416_; 
v___x_416_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2));
return v___x_416_;
}
}
else
{
lean_object* v___x_417_; 
lean_dec(v_a_411_);
v___x_417_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3));
return v___x_417_;
}
}
else
{
lean_dec_ref(v___x_410_);
goto v___jp_408_;
}
v___jp_408_:
{
lean_object* v___x_409_; 
v___x_409_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__1));
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticTag___lam__0(uint8_t v_x_420_){
_start:
{
if (v_x_420_ == 0)
{
lean_object* v___x_421_; 
v___x_421_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
return v___x_421_;
}
else
{
lean_object* v___x_422_; 
v___x_422_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticTag___lam__0___boxed(lean_object* v_x_423_){
_start:
{
uint8_t v_x_48__boxed_424_; lean_object* v_res_425_; 
v_x_48__boxed_424_ = lean_unbox(v_x_423_);
v_res_425_ = l_Lean_Lsp_instToJsonDiagnosticTag___lam__0(v_x_48__boxed_424_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(uint8_t v_x_428_){
_start:
{
if (v_x_428_ == 0)
{
lean_object* v___x_429_; 
v___x_429_ = lean_unsigned_to_nat(0u);
return v___x_429_;
}
else
{
lean_object* v___x_430_; 
v___x_430_ = lean_unsigned_to_nat(1u);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorIdx___boxed(lean_object* v_x_431_){
_start:
{
uint8_t v_x_boxed_432_; lean_object* v_res_433_; 
v_x_boxed_432_ = lean_unbox(v_x_431_);
v_res_433_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_x_boxed_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx(uint8_t v_x_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx___boxed(lean_object* v_x_436_){
_start:
{
uint8_t v_x_4__boxed_437_; lean_object* v_res_438_; 
v_x_4__boxed_437_ = lean_unbox(v_x_436_);
v_res_438_ = l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx(v_x_4__boxed_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg(lean_object* v_k_439_){
_start:
{
lean_inc(v_k_439_);
return v_k_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg___boxed(lean_object* v_k_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg(v_k_440_);
lean_dec(v_k_440_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim(lean_object* v_motive_442_, lean_object* v_ctorIdx_443_, uint8_t v_t_444_, lean_object* v_h_445_, lean_object* v_k_446_){
_start:
{
lean_inc(v_k_446_);
return v_k_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___boxed(lean_object* v_motive_447_, lean_object* v_ctorIdx_448_, lean_object* v_t_449_, lean_object* v_h_450_, lean_object* v_k_451_){
_start:
{
uint8_t v_t_boxed_452_; lean_object* v_res_453_; 
v_t_boxed_452_ = lean_unbox(v_t_449_);
v_res_453_ = l_Lean_Lsp_LeanDiagnosticTag_ctorElim(v_motive_447_, v_ctorIdx_448_, v_t_boxed_452_, v_h_450_, v_k_451_);
lean_dec(v_k_451_);
lean_dec(v_ctorIdx_448_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg(lean_object* v_unsolvedGoals_454_){
_start:
{
lean_inc(v_unsolvedGoals_454_);
return v_unsolvedGoals_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg___boxed(lean_object* v_unsolvedGoals_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg(v_unsolvedGoals_455_);
lean_dec(v_unsolvedGoals_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim(lean_object* v_motive_457_, uint8_t v_t_458_, lean_object* v_h_459_, lean_object* v_unsolvedGoals_460_){
_start:
{
lean_inc(v_unsolvedGoals_460_);
return v_unsolvedGoals_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___boxed(lean_object* v_motive_461_, lean_object* v_t_462_, lean_object* v_h_463_, lean_object* v_unsolvedGoals_464_){
_start:
{
uint8_t v_t_boxed_465_; lean_object* v_res_466_; 
v_t_boxed_465_ = lean_unbox(v_t_462_);
v_res_466_ = l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim(v_motive_461_, v_t_boxed_465_, v_h_463_, v_unsolvedGoals_464_);
lean_dec(v_unsolvedGoals_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg(lean_object* v_goalsAccomplished_467_){
_start:
{
lean_inc(v_goalsAccomplished_467_);
return v_goalsAccomplished_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg___boxed(lean_object* v_goalsAccomplished_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg(v_goalsAccomplished_468_);
lean_dec(v_goalsAccomplished_468_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim(lean_object* v_motive_470_, uint8_t v_t_471_, lean_object* v_h_472_, lean_object* v_goalsAccomplished_473_){
_start:
{
lean_inc(v_goalsAccomplished_473_);
return v_goalsAccomplished_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___boxed(lean_object* v_motive_474_, lean_object* v_t_475_, lean_object* v_h_476_, lean_object* v_goalsAccomplished_477_){
_start:
{
uint8_t v_t_boxed_478_; lean_object* v_res_479_; 
v_t_boxed_478_ = lean_unbox(v_t_475_);
v_res_479_ = l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim(v_motive_474_, v_t_boxed_478_, v_h_476_, v_goalsAccomplished_477_);
lean_dec(v_goalsAccomplished_477_);
return v_res_479_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag_default(void){
_start:
{
uint8_t v___x_480_; 
v___x_480_ = 0;
return v___x_480_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag(void){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = 0;
return v___x_481_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(uint8_t v_x_482_, uint8_t v_y_483_){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_484_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_x_482_);
v___x_485_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_y_483_);
v___x_486_ = lean_nat_dec_eq(v___x_484_, v___x_485_);
lean_dec(v___x_485_);
lean_dec(v___x_484_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqLeanDiagnosticTag_beq___boxed(lean_object* v_x_487_, lean_object* v_y_488_){
_start:
{
uint8_t v_x_17__boxed_489_; uint8_t v_y_18__boxed_490_; uint8_t v_res_491_; lean_object* v_r_492_; 
v_x_17__boxed_489_ = lean_unbox(v_x_487_);
v_y_18__boxed_490_ = lean_unbox(v_y_488_);
v_res_491_ = l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(v_x_17__boxed_489_, v_y_18__boxed_490_);
v_r_492_ = lean_box(v_res_491_);
return v_r_492_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdLeanDiagnosticTag_ord(uint8_t v_x_495_, uint8_t v_y_496_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_497_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_x_495_);
v___x_498_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_y_496_);
v___x_499_ = lean_nat_dec_lt(v___x_497_, v___x_498_);
if (v___x_499_ == 0)
{
uint8_t v___x_500_; 
v___x_500_ = lean_nat_dec_eq(v___x_497_, v___x_498_);
lean_dec(v___x_498_);
lean_dec(v___x_497_);
if (v___x_500_ == 0)
{
uint8_t v___x_501_; 
v___x_501_ = 2;
return v___x_501_;
}
else
{
uint8_t v___x_502_; 
v___x_502_ = 1;
return v___x_502_;
}
}
else
{
uint8_t v___x_503_; 
lean_dec(v___x_498_);
lean_dec(v___x_497_);
v___x_503_ = 0;
return v___x_503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdLeanDiagnosticTag_ord___boxed(lean_object* v_x_504_, lean_object* v_y_505_){
_start:
{
uint8_t v_x_30__boxed_506_; uint8_t v_y_31__boxed_507_; uint8_t v_res_508_; lean_object* v_r_509_; 
v_x_30__boxed_506_ = lean_unbox(v_x_504_);
v_y_31__boxed_507_ = lean_unbox(v_y_505_);
v_res_508_ = l_Lean_Lsp_instOrdLeanDiagnosticTag_ord(v_x_30__boxed_506_, v_y_31__boxed_507_);
v_r_509_ = lean_box(v_res_508_);
return v_r_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0(lean_object* v_j_521_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Json_getNat_x3f(v_j_521_);
if (lean_obj_tag(v___x_524_) == 1)
{
lean_object* v_a_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_524_, 1);
v___x_526_ = lean_unsigned_to_nat(1u);
v___x_527_ = lean_nat_dec_eq(v_a_525_, v___x_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(2u);
v___x_529_ = lean_nat_dec_eq(v_a_525_, v___x_528_);
lean_dec(v_a_525_);
if (v___x_529_ == 0)
{
goto v___jp_522_;
}
else
{
lean_object* v___x_530_; 
v___x_530_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2));
return v___x_530_;
}
}
else
{
lean_object* v___x_531_; 
lean_dec(v_a_525_);
v___x_531_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3));
return v___x_531_;
}
}
else
{
lean_dec_ref(v___x_524_);
goto v___jp_522_;
}
v___jp_522_:
{
lean_object* v___x_523_; 
v___x_523_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__1));
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0(uint8_t v_x_534_){
_start:
{
if (v_x_534_ == 0)
{
lean_object* v___x_535_; 
v___x_535_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
return v___x_535_;
}
else
{
lean_object* v___x_536_; 
v___x_536_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0___boxed(lean_object* v_x_537_){
_start:
{
uint8_t v_x_48__boxed_538_; lean_object* v_res_539_; 
v_x_48__boxed_538_ = lean_unbox(v_x_537_);
v_res_539_ = l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0(v_x_48__boxed_538_);
return v_res_539_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = ((lean_object*)(l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0));
v___x_544_ = l_Lean_Lsp_instInhabitedLocation_default;
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v___x_543_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default(void){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = lean_obj_once(&l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1, &l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1_once, _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1);
return v___x_546_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation(void){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default;
return v___x_547_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
lean_object* v_location_550_; lean_object* v_message_551_; lean_object* v_location_552_; lean_object* v_message_553_; uint8_t v___x_554_; 
v_location_550_ = lean_ctor_get(v_x_548_, 0);
v_message_551_ = lean_ctor_get(v_x_548_, 1);
v_location_552_ = lean_ctor_get(v_x_549_, 0);
v_message_553_ = lean_ctor_get(v_x_549_, 1);
v___x_554_ = l_Lean_Lsp_instBEqLocation_beq(v_location_550_, v_location_552_);
if (v___x_554_ == 0)
{
return v___x_554_;
}
else
{
uint8_t v___x_555_; 
v___x_555_ = lean_string_dec_eq(v_message_551_, v_message_553_);
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq___boxed(lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
uint8_t v_res_558_; lean_object* v_r_559_; 
v_res_558_ = l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(v_x_556_, v_x_557_);
lean_dec_ref(v_x_557_);
lean_dec_ref(v_x_556_);
v_r_559_ = lean_box(v_res_558_);
return v_r_559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
if (lean_obj_tag(v_a_562_) == 0)
{
lean_object* v___x_564_; 
v___x_564_ = lean_array_to_list(v_a_563_);
return v___x_564_;
}
else
{
lean_object* v_head_565_; lean_object* v_tail_566_; lean_object* v___x_567_; 
v_head_565_ = lean_ctor_get(v_a_562_, 0);
lean_inc(v_head_565_);
v_tail_566_ = lean_ctor_get(v_a_562_, 1);
lean_inc(v_tail_566_);
lean_dec_ref_known(v_a_562_, 2);
v___x_567_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_563_, v_head_565_);
v_a_562_ = v_tail_566_;
v_a_563_ = v___x_567_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(lean_object* v_x_573_){
_start:
{
lean_object* v_location_574_; lean_object* v_message_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_595_; 
v_location_574_ = lean_ctor_get(v_x_573_, 0);
v_message_575_ = lean_ctor_get(v_x_573_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v_x_573_);
if (v_isSharedCheck_595_ == 0)
{
v___x_577_ = v_x_573_;
v_isShared_578_ = v_isSharedCheck_595_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_message_575_);
lean_inc(v_location_574_);
lean_dec(v_x_573_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_595_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_579_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0));
v___x_580_ = l_Lean_Lsp_instToJsonLocation_toJson(v_location_574_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 1, v___x_580_);
lean_ctor_set(v___x_577_, 0, v___x_579_);
v___x_582_ = v___x_577_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___x_580_);
v___x_582_ = v_reuseFailAlloc_594_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_583_ = lean_box(0);
v___x_584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
v___x_586_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_586_, 0, v_message_575_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v___x_583_);
v___x_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set(v___x_589_, 1, v___x_583_);
v___x_590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_584_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2));
v___x_592_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(v___x_590_, v___x_591_);
v___x_593_ = l_Lean_Json_mkObj(v___x_592_);
lean_dec(v___x_592_);
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(lean_object* v_j_598_, lean_object* v_k_599_){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = l_Lean_Json_getObjValD(v_j_598_, v_k_599_);
v___x_601_ = l_Lean_Lsp_instFromJsonLocation_fromJson(v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0___boxed(lean_object* v_j_602_, lean_object* v_k_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(v_j_602_, v_k_603_);
lean_dec_ref(v_k_603_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(lean_object* v_j_605_, lean_object* v_k_606_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = l_Lean_Json_getObjValD(v_j_605_, v_k_606_);
v___x_608_ = l_Lean_Json_getStr_x3f(v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1___boxed(lean_object* v_j_609_, lean_object* v_k_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_j_609_, v_k_610_);
lean_dec_ref(v_k_610_);
return v_res_611_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4(void){
_start:
{
uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = 1;
v___x_620_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3));
v___x_621_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_620_, v___x_619_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5));
v___x_624_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4);
v___x_625_ = lean_string_append(v___x_624_, v___x_623_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8(void){
_start:
{
uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = 1;
v___x_629_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7));
v___x_630_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_629_, v___x_628_);
return v___x_630_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8);
v___x_632_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6);
v___x_633_ = lean_string_append(v___x_632_, v___x_631_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_636_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9);
v___x_637_ = lean_string_append(v___x_636_, v___x_635_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13(void){
_start:
{
uint8_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = 1;
v___x_641_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12));
v___x_642_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_641_, v___x_640_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13);
v___x_644_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6);
v___x_645_ = lean_string_append(v___x_644_, v___x_643_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_647_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14);
v___x_648_ = lean_string_append(v___x_647_, v___x_646_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(lean_object* v_json_649_){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0));
lean_inc(v_json_649_);
v___x_651_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(v_json_649_, v___x_650_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_661_; 
lean_dec(v_json_649_);
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_661_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_661_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_656_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11);
v___x_657_ = lean_string_append(v___x_656_, v_a_652_);
lean_dec(v_a_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_657_);
v___x_659_ = v___x_654_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
else
{
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec(v_json_649_);
v_a_662_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_651_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_651_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set_tag(v___x_664_, 0);
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_a_670_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_651_, 1);
v___x_671_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
v___x_672_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_649_, v___x_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_682_; 
lean_dec(v_a_670_);
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_682_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_682_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_682_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_677_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15);
v___x_678_ = lean_string_append(v___x_677_, v_a_673_);
lean_dec(v_a_673_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_678_);
v___x_680_ = v___x_675_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
else
{
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec(v_a_670_);
v_a_683_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_672_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_672_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set_tag(v___x_685_, 0);
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_699_; 
v_a_691_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_699_ == 0)
{
v___x_693_ = v___x_672_;
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_672_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v_a_670_);
lean_ctor_set(v___x_695_, 1, v_a_691_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_695_);
v___x_697_ = v___x_693_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord(lean_object* v_x_702_, lean_object* v_x_703_){
_start:
{
lean_object* v_location_704_; lean_object* v_message_705_; lean_object* v_location_706_; lean_object* v_message_707_; uint8_t v___x_708_; 
v_location_704_ = lean_ctor_get(v_x_702_, 0);
v_message_705_ = lean_ctor_get(v_x_702_, 1);
v_location_706_ = lean_ctor_get(v_x_703_, 0);
v_message_707_ = lean_ctor_get(v_x_703_, 1);
v___x_708_ = l_Lean_Lsp_instOrdLocation_ord(v_location_704_, v_location_706_);
if (v___x_708_ == 1)
{
uint8_t v___x_709_; 
v___x_709_ = lean_string_compare(v_message_705_, v_message_707_);
if (v___x_709_ == 1)
{
return v___x_709_;
}
else
{
return v___x_709_;
}
}
else
{
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord___boxed(lean_object* v_x_710_, lean_object* v_x_711_){
_start:
{
uint8_t v_res_712_; lean_object* v_r_713_; 
v_res_712_ = l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord(v_x_710_, v_x_711_);
lean_dec_ref(v_x_711_);
lean_dec_ref(v_x_710_);
v_r_713_ = lean_box(v_res_712_);
return v_r_713_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = l_Lean_Lsp_instInhabitedRange_default;
v___x_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(lean_object* v_inst_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_719_ = l_Lean_Lsp_instInhabitedRange_default;
v___x_720_ = lean_obj_once(&l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0, &l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0_once, _init_l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0);
v___x_721_ = lean_box(0);
v___x_722_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_722_, 0, v___x_719_);
lean_ctor_set(v___x_722_, 1, v___x_720_);
lean_ctor_set(v___x_722_, 2, v___x_721_);
lean_ctor_set(v___x_722_, 3, v___x_721_);
lean_ctor_set(v___x_722_, 4, v___x_721_);
lean_ctor_set(v___x_722_, 5, v___x_721_);
lean_ctor_set(v___x_722_, 6, v_inst_718_);
lean_ctor_set(v___x_722_, 7, v___x_721_);
lean_ctor_set(v___x_722_, 8, v___x_721_);
lean_ctor_set(v___x_722_, 9, v___x_721_);
lean_ctor_set(v___x_722_, 10, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default(lean_object* v_00_u03b1_723_, lean_object* v_inst_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith___redArg(lean_object* v_inst_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith(lean_object* v_a_728_, lean_object* v_inst_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_729_);
return v___x_730_;
}
}
static lean_object* _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1(void){
_start:
{
lean_object* v___x_732_; lean_object* v___f_733_; 
v___x_732_ = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
v___f_733_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_733_, 0, v___x_732_);
return v___f_733_;
}
}
static lean_object* _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2(void){
_start:
{
lean_object* v___x_734_; lean_object* v___f_735_; 
v___x_734_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_735_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_735_, 0, v___x_734_);
return v___f_735_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(lean_object* v_inst_743_, lean_object* v_x_744_, lean_object* v_x_745_){
_start:
{
lean_object* v_range_746_; lean_object* v_fullRange_x3f_747_; lean_object* v_severity_x3f_748_; lean_object* v_isSilent_x3f_749_; lean_object* v_code_x3f_750_; lean_object* v_source_x3f_751_; lean_object* v_message_752_; lean_object* v_tags_x3f_753_; lean_object* v_leanTags_x3f_754_; lean_object* v_relatedInformation_x3f_755_; lean_object* v_data_x3f_756_; lean_object* v_range_757_; lean_object* v_fullRange_x3f_758_; lean_object* v_severity_x3f_759_; lean_object* v_isSilent_x3f_760_; lean_object* v_code_x3f_761_; lean_object* v_source_x3f_762_; lean_object* v_message_763_; lean_object* v_tags_x3f_764_; lean_object* v_leanTags_x3f_765_; lean_object* v_relatedInformation_x3f_766_; lean_object* v_data_x3f_767_; uint8_t v___x_768_; 
v_range_746_ = lean_ctor_get(v_x_744_, 0);
lean_inc_ref(v_range_746_);
v_fullRange_x3f_747_ = lean_ctor_get(v_x_744_, 1);
lean_inc(v_fullRange_x3f_747_);
v_severity_x3f_748_ = lean_ctor_get(v_x_744_, 2);
lean_inc(v_severity_x3f_748_);
v_isSilent_x3f_749_ = lean_ctor_get(v_x_744_, 3);
lean_inc(v_isSilent_x3f_749_);
v_code_x3f_750_ = lean_ctor_get(v_x_744_, 4);
lean_inc(v_code_x3f_750_);
v_source_x3f_751_ = lean_ctor_get(v_x_744_, 5);
lean_inc(v_source_x3f_751_);
v_message_752_ = lean_ctor_get(v_x_744_, 6);
lean_inc(v_message_752_);
v_tags_x3f_753_ = lean_ctor_get(v_x_744_, 7);
lean_inc(v_tags_x3f_753_);
v_leanTags_x3f_754_ = lean_ctor_get(v_x_744_, 8);
lean_inc(v_leanTags_x3f_754_);
v_relatedInformation_x3f_755_ = lean_ctor_get(v_x_744_, 9);
lean_inc(v_relatedInformation_x3f_755_);
v_data_x3f_756_ = lean_ctor_get(v_x_744_, 10);
lean_inc(v_data_x3f_756_);
lean_dec_ref(v_x_744_);
v_range_757_ = lean_ctor_get(v_x_745_, 0);
lean_inc_ref(v_range_757_);
v_fullRange_x3f_758_ = lean_ctor_get(v_x_745_, 1);
lean_inc(v_fullRange_x3f_758_);
v_severity_x3f_759_ = lean_ctor_get(v_x_745_, 2);
lean_inc(v_severity_x3f_759_);
v_isSilent_x3f_760_ = lean_ctor_get(v_x_745_, 3);
lean_inc(v_isSilent_x3f_760_);
v_code_x3f_761_ = lean_ctor_get(v_x_745_, 4);
lean_inc(v_code_x3f_761_);
v_source_x3f_762_ = lean_ctor_get(v_x_745_, 5);
lean_inc(v_source_x3f_762_);
v_message_763_ = lean_ctor_get(v_x_745_, 6);
lean_inc(v_message_763_);
v_tags_x3f_764_ = lean_ctor_get(v_x_745_, 7);
lean_inc(v_tags_x3f_764_);
v_leanTags_x3f_765_ = lean_ctor_get(v_x_745_, 8);
lean_inc(v_leanTags_x3f_765_);
v_relatedInformation_x3f_766_ = lean_ctor_get(v_x_745_, 9);
lean_inc(v_relatedInformation_x3f_766_);
v_data_x3f_767_ = lean_ctor_get(v_x_745_, 10);
lean_inc(v_data_x3f_767_);
lean_dec_ref(v_x_745_);
v___x_768_ = l_Lean_Lsp_instBEqRange_beq(v_range_746_, v_range_757_);
lean_dec_ref(v_range_757_);
lean_dec_ref(v_range_746_);
if (v___x_768_ == 0)
{
lean_dec(v_data_x3f_767_);
lean_dec(v_relatedInformation_x3f_766_);
lean_dec(v_leanTags_x3f_765_);
lean_dec(v_tags_x3f_764_);
lean_dec(v_message_763_);
lean_dec(v_source_x3f_762_);
lean_dec(v_code_x3f_761_);
lean_dec(v_isSilent_x3f_760_);
lean_dec(v_severity_x3f_759_);
lean_dec(v_fullRange_x3f_758_);
lean_dec(v_data_x3f_756_);
lean_dec(v_relatedInformation_x3f_755_);
lean_dec(v_leanTags_x3f_754_);
lean_dec(v_tags_x3f_753_);
lean_dec(v_message_752_);
lean_dec(v_source_x3f_751_);
lean_dec(v_code_x3f_750_);
lean_dec(v_isSilent_x3f_749_);
lean_dec(v_severity_x3f_748_);
lean_dec(v_fullRange_x3f_747_);
lean_dec_ref(v_inst_743_);
return v___x_768_;
}
else
{
lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_769_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0));
v___x_770_ = l_Option_instBEq_beq___redArg(v___x_769_, v_fullRange_x3f_747_, v_fullRange_x3f_758_);
if (v___x_770_ == 0)
{
lean_dec(v_data_x3f_767_);
lean_dec(v_relatedInformation_x3f_766_);
lean_dec(v_leanTags_x3f_765_);
lean_dec(v_tags_x3f_764_);
lean_dec(v_message_763_);
lean_dec(v_source_x3f_762_);
lean_dec(v_code_x3f_761_);
lean_dec(v_isSilent_x3f_760_);
lean_dec(v_severity_x3f_759_);
lean_dec(v_data_x3f_756_);
lean_dec(v_relatedInformation_x3f_755_);
lean_dec(v_leanTags_x3f_754_);
lean_dec(v_tags_x3f_753_);
lean_dec(v_message_752_);
lean_dec(v_source_x3f_751_);
lean_dec(v_code_x3f_750_);
lean_dec(v_isSilent_x3f_749_);
lean_dec(v_severity_x3f_748_);
lean_dec_ref(v_inst_743_);
return v___x_770_;
}
else
{
lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_771_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0));
v___x_772_ = l_Option_instBEq_beq___redArg(v___x_771_, v_severity_x3f_748_, v_severity_x3f_759_);
if (v___x_772_ == 0)
{
lean_dec(v_data_x3f_767_);
lean_dec(v_relatedInformation_x3f_766_);
lean_dec(v_leanTags_x3f_765_);
lean_dec(v_tags_x3f_764_);
lean_dec(v_message_763_);
lean_dec(v_source_x3f_762_);
lean_dec(v_code_x3f_761_);
lean_dec(v_isSilent_x3f_760_);
lean_dec(v_data_x3f_756_);
lean_dec(v_relatedInformation_x3f_755_);
lean_dec(v_leanTags_x3f_754_);
lean_dec(v_tags_x3f_753_);
lean_dec(v_message_752_);
lean_dec(v_source_x3f_751_);
lean_dec(v_code_x3f_750_);
lean_dec(v_isSilent_x3f_749_);
lean_dec_ref(v_inst_743_);
return v___x_772_;
}
else
{
lean_object* v___f_773_; uint8_t v___x_774_; 
v___f_773_ = lean_obj_once(&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1, &l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1_once, _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1);
v___x_774_ = l_Option_instBEq_beq___redArg(v___f_773_, v_isSilent_x3f_749_, v_isSilent_x3f_760_);
if (v___x_774_ == 0)
{
lean_dec(v_data_x3f_767_);
lean_dec(v_relatedInformation_x3f_766_);
lean_dec(v_leanTags_x3f_765_);
lean_dec(v_tags_x3f_764_);
lean_dec(v_message_763_);
lean_dec(v_source_x3f_762_);
lean_dec(v_code_x3f_761_);
lean_dec(v_data_x3f_756_);
lean_dec(v_relatedInformation_x3f_755_);
lean_dec(v_leanTags_x3f_754_);
lean_dec(v_tags_x3f_753_);
lean_dec(v_message_752_);
lean_dec(v_source_x3f_751_);
lean_dec(v_code_x3f_750_);
lean_dec_ref(v_inst_743_);
return v___x_774_;
}
else
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticCode___closed__0));
v___x_776_ = l_Option_instBEq_beq___redArg(v___x_775_, v_code_x3f_750_, v_code_x3f_761_);
if (v___x_776_ == 0)
{
lean_dec(v_data_x3f_767_);
lean_dec(v_relatedInformation_x3f_766_);
lean_dec(v_leanTags_x3f_765_);
lean_dec(v_tags_x3f_764_);
lean_dec(v_message_763_);
lean_dec(v_source_x3f_762_);
lean_dec(v_data_x3f_756_);
lean_dec(v_relatedInformation_x3f_755_);
lean_dec(v_leanTags_x3f_754_);
lean_dec(v_tags_x3f_753_);
lean_dec(v_message_752_);
lean_dec(v_source_x3f_751_);
lean_dec_ref(v_inst_743_);
return v___x_776_;
}
else
{
lean_object* v___f_777_; uint8_t v___x_778_; 
v___f_777_ = lean_obj_once(&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2, &l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2_once, _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2);
v___x_778_ = l_Option_instBEq_beq___redArg(v___f_777_, v_source_x3f_751_, v_source_x3f_762_);
if (v___x_778_ == 0)
{
lean_dec(v_data_x3f_767_);
lean_dec(v_relatedInformation_x3f_766_);
lean_dec(v_leanTags_x3f_765_);
lean_dec(v_tags_x3f_764_);
lean_dec(v_message_763_);
lean_dec(v_data_x3f_756_);
lean_dec(v_relatedInformation_x3f_755_);
lean_dec(v_leanTags_x3f_754_);
lean_dec(v_tags_x3f_753_);
lean_dec(v_message_752_);
lean_dec_ref(v_inst_743_);
return v___x_778_;
}
else
{
lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_779_ = lean_apply_2(v_inst_743_, v_message_752_, v_message_763_);
v___x_780_ = lean_unbox(v___x_779_);
if (v___x_780_ == 0)
{
uint8_t v___x_781_; 
lean_dec(v_data_x3f_767_);
lean_dec(v_relatedInformation_x3f_766_);
lean_dec(v_leanTags_x3f_765_);
lean_dec(v_tags_x3f_764_);
lean_dec(v_data_x3f_756_);
lean_dec(v_relatedInformation_x3f_755_);
lean_dec(v_leanTags_x3f_754_);
lean_dec(v_tags_x3f_753_);
v___x_781_ = lean_unbox(v___x_779_);
return v___x_781_;
}
else
{
lean_object* v___f_782_; uint8_t v___x_783_; 
v___f_782_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3));
v___x_783_ = l_Option_instBEq_beq___redArg(v___f_782_, v_tags_x3f_753_, v_tags_x3f_764_);
if (v___x_783_ == 0)
{
lean_dec(v_data_x3f_767_);
lean_dec(v_relatedInformation_x3f_766_);
lean_dec(v_leanTags_x3f_765_);
lean_dec(v_data_x3f_756_);
lean_dec(v_relatedInformation_x3f_755_);
lean_dec(v_leanTags_x3f_754_);
return v___x_783_;
}
else
{
lean_object* v___f_784_; uint8_t v___x_785_; 
v___f_784_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4));
v___x_785_ = l_Option_instBEq_beq___redArg(v___f_784_, v_leanTags_x3f_754_, v_leanTags_x3f_765_);
if (v___x_785_ == 0)
{
lean_dec(v_data_x3f_767_);
lean_dec(v_relatedInformation_x3f_766_);
lean_dec(v_data_x3f_756_);
lean_dec(v_relatedInformation_x3f_755_);
return v___x_785_;
}
else
{
lean_object* v___f_786_; uint8_t v___x_787_; 
v___f_786_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5));
v___x_787_ = l_Option_instBEq_beq___redArg(v___f_786_, v_relatedInformation_x3f_755_, v_relatedInformation_x3f_766_);
if (v___x_787_ == 0)
{
lean_dec(v_data_x3f_767_);
lean_dec(v_data_x3f_756_);
return v___x_787_;
}
else
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6));
v___x_789_ = l_Option_instBEq_beq___redArg(v___x_788_, v_data_x3f_756_, v_data_x3f_767_);
return v___x_789_;
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
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___boxed(lean_object* v_inst_790_, lean_object* v_x_791_, lean_object* v_x_792_){
_start:
{
uint8_t v_res_793_; lean_object* v_r_794_; 
v_res_793_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(v_inst_790_, v_x_791_, v_x_792_);
v_r_794_ = lean_box(v_res_793_);
return v_r_794_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq(lean_object* v_00_u03b1_795_, lean_object* v_inst_796_, lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
uint8_t v___x_799_; 
v___x_799_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(v_inst_796_, v_x_797_, v_x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed(lean_object* v_00_u03b1_800_, lean_object* v_inst_801_, lean_object* v_x_802_, lean_object* v_x_803_){
_start:
{
uint8_t v_res_804_; lean_object* v_r_805_; 
v_res_804_ = l_Lean_Lsp_instBEqDiagnosticWith_beq(v_00_u03b1_800_, v_inst_801_, v_x_802_, v_x_803_);
v_r_805_ = lean_box(v_res_804_);
return v_r_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith___redArg(lean_object* v_inst_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = lean_alloc_closure((void*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed), 4, 2);
lean_closure_set(v___x_807_, 0, lean_box(0));
lean_closure_set(v___x_807_, 1, v_inst_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith(lean_object* v_00_u03b1_808_, lean_object* v_inst_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = lean_alloc_closure((void*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed), 4, 2);
lean_closure_set(v___x_810_, 0, lean_box(0));
lean_closure_set(v___x_810_, 1, v_inst_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg(lean_object* v_inst_831_, lean_object* v_x_832_){
_start:
{
lean_object* v_range_833_; lean_object* v_fullRange_x3f_834_; lean_object* v_severity_x3f_835_; lean_object* v_isSilent_x3f_836_; lean_object* v_code_x3f_837_; lean_object* v_source_x3f_838_; lean_object* v_message_839_; lean_object* v_tags_x3f_840_; lean_object* v_leanTags_x3f_841_; lean_object* v_relatedInformation_x3f_842_; lean_object* v_data_x3f_843_; lean_object* v___x_844_; lean_object* v___f_845_; lean_object* v___f_846_; lean_object* v___f_847_; lean_object* v___f_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_range_833_ = lean_ctor_get(v_x_832_, 0);
lean_inc_ref(v_range_833_);
v_fullRange_x3f_834_ = lean_ctor_get(v_x_832_, 1);
lean_inc(v_fullRange_x3f_834_);
v_severity_x3f_835_ = lean_ctor_get(v_x_832_, 2);
lean_inc(v_severity_x3f_835_);
v_isSilent_x3f_836_ = lean_ctor_get(v_x_832_, 3);
lean_inc(v_isSilent_x3f_836_);
v_code_x3f_837_ = lean_ctor_get(v_x_832_, 4);
lean_inc(v_code_x3f_837_);
v_source_x3f_838_ = lean_ctor_get(v_x_832_, 5);
lean_inc(v_source_x3f_838_);
v_message_839_ = lean_ctor_get(v_x_832_, 6);
lean_inc(v_message_839_);
v_tags_x3f_840_ = lean_ctor_get(v_x_832_, 7);
lean_inc(v_tags_x3f_840_);
v_leanTags_x3f_841_ = lean_ctor_get(v_x_832_, 8);
lean_inc(v_leanTags_x3f_841_);
v_relatedInformation_x3f_842_ = lean_ctor_get(v_x_832_, 9);
lean_inc(v_relatedInformation_x3f_842_);
v_data_x3f_843_ = lean_ctor_get(v_x_832_, 10);
lean_inc(v_data_x3f_843_);
lean_dec_ref(v_x_832_);
v___x_844_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0));
v___f_845_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0));
v___f_846_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1));
v___f_847_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticCode___closed__0));
v___f_848_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2));
v___x_849_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3));
v___x_850_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4));
v___x_851_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5));
v___x_852_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6));
v___x_853_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
v___x_854_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_833_);
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = lean_box(0);
v___x_857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_855_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
v___x_859_ = l_Lean_Json_opt___redArg(v___x_844_, v___x_858_, v_fullRange_x3f_834_);
v___x_860_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
v___x_861_ = l_Lean_Json_opt___redArg(v___f_845_, v___x_860_, v_severity_x3f_835_);
v___x_862_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
v___x_863_ = l_Lean_Json_opt___redArg(v___f_846_, v___x_862_, v_isSilent_x3f_836_);
v___x_864_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
v___x_865_ = l_Lean_Json_opt___redArg(v___f_847_, v___x_864_, v_code_x3f_837_);
v___x_866_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
v___x_867_ = l_Lean_Json_opt___redArg(v___f_848_, v___x_866_, v_source_x3f_838_);
v___x_868_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
v___x_869_ = lean_apply_1(v_inst_831_, v_message_839_);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_856_);
v___x_872_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
v___x_873_ = l_Lean_Json_opt___redArg(v___x_849_, v___x_872_, v_tags_x3f_840_);
v___x_874_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
v___x_875_ = l_Lean_Json_opt___redArg(v___x_850_, v___x_874_, v_leanTags_x3f_841_);
v___x_876_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
v___x_877_ = l_Lean_Json_opt___redArg(v___x_851_, v___x_876_, v_relatedInformation_x3f_842_);
v___x_878_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
v___x_879_ = l_Lean_Json_opt___redArg(v___x_852_, v___x_878_, v_data_x3f_843_);
v___x_880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v___x_856_);
v___x_881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_877_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_875_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_873_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_871_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_867_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_865_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_863_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_861_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_859_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_857_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2));
v___x_892_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_852_, v___x_890_, v___x_891_);
v___x_893_ = l_Lean_Json_mkObj(v___x_892_);
lean_dec(v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson(lean_object* v_00_u03b1_894_, lean_object* v_inst_895_, lean_object* v_x_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg(v_inst_895_, v_x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith___redArg(lean_object* v_inst_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson), 3, 2);
lean_closure_set(v___x_899_, 0, lean_box(0));
lean_closure_set(v___x_899_, 1, v_inst_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith(lean_object* v_00_u03b1_900_, lean_object* v_inst_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson), 3, 2);
lean_closure_set(v___x_902_, 0, lean_box(0));
lean_closure_set(v___x_902_, 1, v_inst_901_);
return v___x_902_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4(void){
_start:
{
uint8_t v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_911_ = 1;
v___x_912_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3));
v___x_913_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_912_, v___x_911_);
return v___x_913_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_914_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5));
v___x_915_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4);
v___x_916_ = lean_string_append(v___x_915_, v___x_914_);
return v___x_916_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = 1;
v___x_920_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6));
v___x_921_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_920_, v___x_919_);
return v___x_921_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7);
v___x_923_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_924_ = lean_string_append(v___x_923_, v___x_922_);
return v___x_924_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_926_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8);
v___x_927_ = lean_string_append(v___x_926_, v___x_925_);
return v___x_927_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12(void){
_start:
{
uint8_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = 1;
v___x_932_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11));
v___x_933_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_932_, v___x_931_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12);
v___x_935_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_936_ = lean_string_append(v___x_935_, v___x_934_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_938_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13);
v___x_939_ = lean_string_append(v___x_938_, v___x_937_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_945_ = 1;
v___x_946_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17));
v___x_947_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_946_, v___x_945_);
return v___x_947_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18);
v___x_949_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_950_ = lean_string_append(v___x_949_, v___x_948_);
return v___x_950_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_952_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19);
v___x_953_ = lean_string_append(v___x_952_, v___x_951_);
return v___x_953_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25(void){
_start:
{
uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = 1;
v___x_961_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24));
v___x_962_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_961_, v___x_960_);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_963_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25);
v___x_964_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_965_ = lean_string_append(v___x_964_, v___x_963_);
return v___x_965_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_966_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_967_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26);
v___x_968_ = lean_string_append(v___x_967_, v___x_966_);
return v___x_968_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = 1;
v___x_975_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30));
v___x_976_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_975_, v___x_974_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_977_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31);
v___x_978_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_979_ = lean_string_append(v___x_978_, v___x_977_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_981_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32);
v___x_982_ = lean_string_append(v___x_981_, v___x_980_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38(void){
_start:
{
uint8_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_989_ = 1;
v___x_990_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37));
v___x_991_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_990_, v___x_989_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_992_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38);
v___x_993_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_994_ = lean_string_append(v___x_993_, v___x_992_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_996_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39);
v___x_997_ = lean_string_append(v___x_996_, v___x_995_);
return v___x_997_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13);
v___x_999_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1000_ = lean_string_append(v___x_999_, v___x_998_);
return v___x_1000_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1002_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41);
v___x_1003_ = lean_string_append(v___x_1002_, v___x_1001_);
return v___x_1003_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47(void){
_start:
{
uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1011_ = 1;
v___x_1012_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46));
v___x_1013_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1012_, v___x_1011_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47);
v___x_1015_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1016_ = lean_string_append(v___x_1015_, v___x_1014_);
return v___x_1016_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1018_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48);
v___x_1019_ = lean_string_append(v___x_1018_, v___x_1017_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54(void){
_start:
{
uint8_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = 1;
v___x_1028_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53));
v___x_1029_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1028_, v___x_1027_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54);
v___x_1031_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1032_ = lean_string_append(v___x_1031_, v___x_1030_);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1033_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1034_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55);
v___x_1035_ = lean_string_append(v___x_1034_, v___x_1033_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61(void){
_start:
{
uint8_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = 1;
v___x_1044_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60));
v___x_1045_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1044_, v___x_1043_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61);
v___x_1047_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1048_ = lean_string_append(v___x_1047_, v___x_1046_);
return v___x_1048_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1050_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62);
v___x_1051_ = lean_string_append(v___x_1050_, v___x_1049_);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68(void){
_start:
{
uint8_t v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = 1;
v___x_1059_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67));
v___x_1060_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1059_, v___x_1058_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68);
v___x_1062_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1063_ = lean_string_append(v___x_1062_, v___x_1061_);
return v___x_1063_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1064_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1065_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69);
v___x_1066_ = lean_string_append(v___x_1065_, v___x_1064_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg(lean_object* v_inst_1067_, lean_object* v_json_1068_){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1069_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0));
v___x_1070_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1));
v___x_1071_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
lean_inc(v_json_1068_);
v___x_1072_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1068_, v___x_1069_, v___x_1071_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1082_; 
lean_dec(v_json_1068_);
lean_dec_ref(v_inst_1067_);
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1082_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1082_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1077_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9);
v___x_1078_ = lean_string_append(v___x_1077_, v_a_1073_);
lean_dec(v_a_1073_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1078_);
v___x_1080_ = v___x_1075_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
else
{
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec(v_json_1068_);
lean_dec_ref(v_inst_1067_);
v_a_1083_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1072_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1072_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 0);
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v_a_1091_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1092_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
lean_inc(v_json_1068_);
v___x_1093_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1068_, v___x_1070_, v___x_1092_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1103_; 
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
lean_dec_ref(v_inst_1067_);
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1096_ = v___x_1093_;
v_isShared_1097_ = v_isSharedCheck_1103_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1103_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1098_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14);
v___x_1099_ = lean_string_append(v___x_1098_, v_a_1094_);
lean_dec(v_a_1094_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v___x_1099_);
v___x_1101_ = v___x_1096_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
else
{
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
lean_dec_ref(v_inst_1067_);
v_a_1104_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1093_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1093_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set_tag(v___x_1106_, 0);
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v_a_1112_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1093_, 1);
v___x_1113_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15));
v___x_1114_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
lean_inc(v_json_1068_);
v___x_1115_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1068_, v___x_1113_, v___x_1114_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
lean_dec_ref(v_inst_1067_);
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1125_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1125_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1120_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20);
v___x_1121_ = lean_string_append(v___x_1120_, v_a_1116_);
lean_dec(v_a_1116_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1121_);
v___x_1123_ = v___x_1118_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
lean_dec_ref(v_inst_1067_);
v_a_1126_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1115_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1115_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set_tag(v___x_1128_, 0);
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v_a_1134_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1135_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22));
v___x_1136_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
lean_inc(v_json_1068_);
v___x_1137_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1068_, v___x_1135_, v___x_1136_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v_a_1134_);
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
lean_dec_ref(v_inst_1067_);
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1147_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1147_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1142_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27);
v___x_1143_ = lean_string_append(v___x_1142_, v_a_1138_);
lean_dec(v_a_1138_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1143_);
v___x_1145_ = v___x_1140_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
else
{
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec(v_a_1134_);
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
lean_dec_ref(v_inst_1067_);
v_a_1148_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1137_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1137_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set_tag(v___x_1150_, 0);
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_a_1156_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1156_);
lean_dec_ref_known(v___x_1137_, 1);
v___x_1157_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28));
v___x_1158_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
lean_inc(v_json_1068_);
v___x_1159_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1068_, v___x_1157_, v___x_1158_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1169_; 
lean_dec(v_a_1156_);
lean_dec(v_a_1134_);
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
lean_dec_ref(v_inst_1067_);
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1162_ = v___x_1159_;
v_isShared_1163_ = v_isSharedCheck_1169_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1159_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1169_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1164_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33);
v___x_1165_ = lean_string_append(v___x_1164_, v_a_1160_);
lean_dec(v_a_1160_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1165_);
v___x_1167_ = v___x_1162_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
else
{
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec(v_a_1156_);
lean_dec(v_a_1134_);
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
lean_dec_ref(v_inst_1067_);
v_a_1170_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1159_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1159_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set_tag(v___x_1172_, 0);
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_a_1178_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1159_, 1);
v___x_1179_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35));
v___x_1180_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
lean_inc(v_json_1068_);
v___x_1181_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1068_, v___x_1179_, v___x_1180_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v_a_1178_);
lean_dec(v_a_1156_);
lean_dec(v_a_1134_);
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
lean_dec_ref(v_inst_1067_);
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1191_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1191_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1186_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40);
v___x_1187_ = lean_string_append(v___x_1186_, v_a_1182_);
lean_dec(v_a_1182_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1187_);
v___x_1189_ = v___x_1184_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
else
{
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec(v_a_1178_);
lean_dec(v_a_1156_);
lean_dec(v_a_1134_);
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
lean_dec_ref(v_inst_1067_);
v_a_1192_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1181_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1181_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set_tag(v___x_1194_, 0);
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v_a_1200_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1200_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1201_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
lean_inc(v_json_1068_);
v___x_1202_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1068_, v_inst_1067_, v___x_1201_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1212_; 
lean_dec(v_a_1200_);
lean_dec(v_a_1178_);
lean_dec(v_a_1156_);
lean_dec(v_a_1134_);
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1212_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1212_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1207_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42);
v___x_1208_ = lean_string_append(v___x_1207_, v_a_1203_);
lean_dec(v_a_1203_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1208_);
v___x_1210_ = v___x_1205_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
else
{
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec(v_a_1200_);
lean_dec(v_a_1178_);
lean_dec(v_a_1156_);
lean_dec(v_a_1134_);
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
v_a_1213_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1202_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1202_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set_tag(v___x_1215_, 0);
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v_a_1221_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1202_, 1);
v___x_1222_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44));
v___x_1223_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
lean_inc(v_json_1068_);
v___x_1224_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1068_, v___x_1222_, v___x_1223_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1234_; 
lean_dec(v_a_1221_);
lean_dec(v_a_1200_);
lean_dec(v_a_1178_);
lean_dec(v_a_1156_);
lean_dec(v_a_1134_);
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1234_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1234_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1229_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49);
v___x_1230_ = lean_string_append(v___x_1229_, v_a_1225_);
lean_dec(v_a_1225_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1230_);
v___x_1232_ = v___x_1227_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
else
{
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec(v_a_1221_);
lean_dec(v_a_1200_);
lean_dec(v_a_1178_);
lean_dec(v_a_1156_);
lean_dec(v_a_1134_);
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
v_a_1235_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1224_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1224_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set_tag(v___x_1237_, 0);
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v_a_1243_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_1224_, 1);
v___x_1244_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51));
v___x_1245_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
lean_inc(v_json_1068_);
v___x_1246_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1068_, v___x_1244_, v___x_1245_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v_a_1243_);
lean_dec(v_a_1221_);
lean_dec(v_a_1200_);
lean_dec(v_a_1178_);
lean_dec(v_a_1156_);
lean_dec(v_a_1134_);
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1256_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1256_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1251_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56);
v___x_1252_ = lean_string_append(v___x_1251_, v_a_1247_);
lean_dec(v_a_1247_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1252_);
v___x_1254_ = v___x_1249_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
else
{
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v_a_1243_);
lean_dec(v_a_1221_);
lean_dec(v_a_1200_);
lean_dec(v_a_1178_);
lean_dec(v_a_1156_);
lean_dec(v_a_1134_);
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
v_a_1257_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1246_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1246_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set_tag(v___x_1259_, 0);
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v_a_1265_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v___x_1246_, 1);
v___x_1266_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58));
v___x_1267_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
lean_inc(v_json_1068_);
v___x_1268_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1068_, v___x_1266_, v___x_1267_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1278_; 
lean_dec(v_a_1265_);
lean_dec(v_a_1243_);
lean_dec(v_a_1221_);
lean_dec(v_a_1200_);
lean_dec(v_a_1178_);
lean_dec(v_a_1156_);
lean_dec(v_a_1134_);
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1278_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1278_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1273_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63);
v___x_1274_ = lean_string_append(v___x_1273_, v_a_1269_);
lean_dec(v_a_1269_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1274_);
v___x_1276_ = v___x_1271_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
else
{
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_dec(v_a_1265_);
lean_dec(v_a_1243_);
lean_dec(v_a_1221_);
lean_dec(v_a_1200_);
lean_dec(v_a_1178_);
lean_dec(v_a_1156_);
lean_dec(v_a_1134_);
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
lean_dec(v_json_1068_);
v_a_1279_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1268_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1268_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set_tag(v___x_1281_, 0);
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_a_1287_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1268_, 1);
v___x_1288_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65));
v___x_1289_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
v___x_1290_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1068_, v___x_1288_, v___x_1289_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1300_; 
lean_dec(v_a_1287_);
lean_dec(v_a_1265_);
lean_dec(v_a_1243_);
lean_dec(v_a_1221_);
lean_dec(v_a_1200_);
lean_dec(v_a_1178_);
lean_dec(v_a_1156_);
lean_dec(v_a_1134_);
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1300_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1300_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1295_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70);
v___x_1296_ = lean_string_append(v___x_1295_, v_a_1291_);
lean_dec(v_a_1291_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1296_);
v___x_1298_ = v___x_1293_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
else
{
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec(v_a_1287_);
lean_dec(v_a_1265_);
lean_dec(v_a_1243_);
lean_dec(v_a_1221_);
lean_dec(v_a_1200_);
lean_dec(v_a_1178_);
lean_dec(v_a_1156_);
lean_dec(v_a_1134_);
lean_dec(v_a_1112_);
lean_dec(v_a_1091_);
v_a_1301_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1290_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1290_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set_tag(v___x_1303_, 0);
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1317_; 
v_a_1309_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1311_ = v___x_1290_;
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1290_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1313_, 0, v_a_1091_);
lean_ctor_set(v___x_1313_, 1, v_a_1112_);
lean_ctor_set(v___x_1313_, 2, v_a_1134_);
lean_ctor_set(v___x_1313_, 3, v_a_1156_);
lean_ctor_set(v___x_1313_, 4, v_a_1178_);
lean_ctor_set(v___x_1313_, 5, v_a_1200_);
lean_ctor_set(v___x_1313_, 6, v_a_1221_);
lean_ctor_set(v___x_1313_, 7, v_a_1243_);
lean_ctor_set(v___x_1313_, 8, v_a_1265_);
lean_ctor_set(v___x_1313_, 9, v_a_1287_);
lean_ctor_set(v___x_1313_, 10, v_a_1309_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1313_);
v___x_1315_ = v___x_1311_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson(lean_object* v_00_u03b1_1318_, lean_object* v_inst_1319_, lean_object* v_json_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg(v_inst_1319_, v_json_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith___redArg(lean_object* v_inst_1322_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson), 3, 2);
lean_closure_set(v___x_1323_, 0, lean_box(0));
lean_closure_set(v___x_1323_, 1, v_inst_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith(lean_object* v_00_u03b1_1324_, lean_object* v_inst_1325_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson), 3, 2);
lean_closure_set(v___x_1326_, 0, lean_box(0));
lean_closure_set(v___x_1326_, 1, v_inst_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg(lean_object* v_d_1327_){
_start:
{
lean_object* v_fullRange_x3f_1328_; 
v_fullRange_x3f_1328_ = lean_ctor_get(v_d_1327_, 1);
if (lean_obj_tag(v_fullRange_x3f_1328_) == 0)
{
lean_object* v_range_1329_; 
v_range_1329_ = lean_ctor_get(v_d_1327_, 0);
lean_inc_ref(v_range_1329_);
return v_range_1329_;
}
else
{
lean_object* v_val_1330_; 
v_val_1330_ = lean_ctor_get(v_fullRange_x3f_1328_, 0);
lean_inc(v_val_1330_);
return v_val_1330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg___boxed(lean_object* v_d_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d_1331_);
lean_dec_ref(v_d_1331_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange(lean_object* v_00_u03b1_1333_, lean_object* v_d_1334_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___boxed(lean_object* v_00_u03b1_1336_, lean_object* v_d_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lean_Lsp_DiagnosticWith_fullRange(v_00_u03b1_1336_, v_d_1337_);
lean_dec_ref(v_d_1337_);
return v_res_1338_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(lean_object* v_x_1347_, lean_object* v_x_1348_){
_start:
{
if (lean_obj_tag(v_x_1347_) == 0)
{
if (lean_obj_tag(v_x_1348_) == 0)
{
uint8_t v___x_1349_; 
v___x_1349_ = 1;
return v___x_1349_;
}
else
{
uint8_t v___x_1350_; 
v___x_1350_ = 0;
return v___x_1350_;
}
}
else
{
if (lean_obj_tag(v_x_1348_) == 0)
{
uint8_t v___x_1351_; 
v___x_1351_ = 0;
return v___x_1351_;
}
else
{
lean_object* v_val_1352_; lean_object* v_val_1353_; uint8_t v___x_1354_; 
v_val_1352_ = lean_ctor_get(v_x_1347_, 0);
v_val_1353_ = lean_ctor_get(v_x_1348_, 0);
v___x_1354_ = lean_int_dec_eq(v_val_1352_, v_val_1353_);
return v___x_1354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0___boxed(lean_object* v_x_1355_, lean_object* v_x_1356_){
_start:
{
uint8_t v_res_1357_; lean_object* v_r_1358_; 
v_res_1357_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(v_x_1355_, v_x_1356_);
lean_dec(v_x_1356_);
lean_dec(v_x_1355_);
v_r_1358_ = lean_box(v_res_1357_);
return v_r_1358_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(lean_object* v_x_1359_, lean_object* v_x_1360_){
_start:
{
if (lean_obj_tag(v_x_1359_) == 0)
{
if (lean_obj_tag(v_x_1360_) == 0)
{
uint8_t v___x_1361_; 
v___x_1361_ = 1;
return v___x_1361_;
}
else
{
uint8_t v___x_1362_; 
v___x_1362_ = 0;
return v___x_1362_;
}
}
else
{
if (lean_obj_tag(v_x_1360_) == 0)
{
uint8_t v___x_1363_; 
v___x_1363_ = 0;
return v___x_1363_;
}
else
{
lean_object* v_val_1364_; uint8_t v___x_1365_; 
v_val_1364_ = lean_ctor_get(v_x_1359_, 0);
v___x_1365_ = lean_unbox(v_val_1364_);
if (v___x_1365_ == 0)
{
lean_object* v_val_1366_; uint8_t v___x_1367_; 
v_val_1366_ = lean_ctor_get(v_x_1360_, 0);
v___x_1367_ = lean_unbox(v_val_1366_);
if (v___x_1367_ == 0)
{
uint8_t v___x_1368_; 
v___x_1368_ = 1;
return v___x_1368_;
}
else
{
uint8_t v___x_1369_; 
v___x_1369_ = lean_unbox(v_val_1364_);
return v___x_1369_;
}
}
else
{
lean_object* v_val_1370_; uint8_t v___x_1371_; 
v_val_1370_ = lean_ctor_get(v_x_1360_, 0);
v___x_1371_ = lean_unbox(v_val_1370_);
return v___x_1371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1___boxed(lean_object* v_x_1372_, lean_object* v_x_1373_){
_start:
{
uint8_t v_res_1374_; lean_object* v_r_1375_; 
v_res_1374_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(v_x_1372_, v_x_1373_);
lean_dec(v_x_1373_);
lean_dec(v_x_1372_);
v_r_1375_ = lean_box(v_res_1374_);
return v_r_1375_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(lean_object* v_xs_1376_, lean_object* v_ys_1377_, lean_object* v_x_1378_){
_start:
{
lean_object* v_zero_1379_; uint8_t v_isZero_1380_; 
v_zero_1379_ = lean_unsigned_to_nat(0u);
v_isZero_1380_ = lean_nat_dec_eq(v_x_1378_, v_zero_1379_);
if (v_isZero_1380_ == 1)
{
lean_dec(v_x_1378_);
return v_isZero_1380_;
}
else
{
lean_object* v_one_1381_; lean_object* v_n_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v_one_1381_ = lean_unsigned_to_nat(1u);
v_n_1382_ = lean_nat_sub(v_x_1378_, v_one_1381_);
lean_dec(v_x_1378_);
v___x_1383_ = lean_array_fget_borrowed(v_xs_1376_, v_n_1382_);
v___x_1384_ = lean_array_fget_borrowed(v_ys_1377_, v_n_1382_);
v___x_1385_ = l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(v___x_1383_, v___x_1384_);
if (v___x_1385_ == 0)
{
lean_dec(v_n_1382_);
return v___x_1385_;
}
else
{
v_x_1378_ = v_n_1382_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg___boxed(lean_object* v_xs_1387_, lean_object* v_ys_1388_, lean_object* v_x_1389_){
_start:
{
uint8_t v_res_1390_; lean_object* v_r_1391_; 
v_res_1390_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(v_xs_1387_, v_ys_1388_, v_x_1389_);
lean_dec_ref(v_ys_1388_);
lean_dec_ref(v_xs_1387_);
v_r_1391_ = lean_box(v_res_1390_);
return v_r_1391_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(lean_object* v_x_1392_, lean_object* v_x_1393_){
_start:
{
if (lean_obj_tag(v_x_1392_) == 0)
{
if (lean_obj_tag(v_x_1393_) == 0)
{
uint8_t v___x_1394_; 
v___x_1394_ = 1;
return v___x_1394_;
}
else
{
uint8_t v___x_1395_; 
v___x_1395_ = 0;
return v___x_1395_;
}
}
else
{
if (lean_obj_tag(v_x_1393_) == 0)
{
uint8_t v___x_1396_; 
v___x_1396_ = 0;
return v___x_1396_;
}
else
{
lean_object* v_val_1397_; lean_object* v_val_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
v_val_1397_ = lean_ctor_get(v_x_1392_, 0);
v_val_1398_ = lean_ctor_get(v_x_1393_, 0);
v___x_1399_ = lean_array_get_size(v_val_1397_);
v___x_1400_ = lean_array_get_size(v_val_1398_);
v___x_1401_ = lean_nat_dec_eq(v___x_1399_, v___x_1400_);
if (v___x_1401_ == 0)
{
return v___x_1401_;
}
else
{
uint8_t v___x_1402_; 
v___x_1402_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(v_val_1397_, v_val_1398_, v___x_1399_);
return v___x_1402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8___boxed(lean_object* v_x_1403_, lean_object* v_x_1404_){
_start:
{
uint8_t v_res_1405_; lean_object* v_r_1406_; 
v_res_1405_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(v_x_1403_, v_x_1404_);
lean_dec(v_x_1404_);
lean_dec(v_x_1403_);
v_r_1406_ = lean_box(v_res_1405_);
return v_r_1406_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(lean_object* v_xs_1407_, lean_object* v_ys_1408_, lean_object* v_x_1409_){
_start:
{
lean_object* v_zero_1410_; uint8_t v_isZero_1411_; 
v_zero_1410_ = lean_unsigned_to_nat(0u);
v_isZero_1411_ = lean_nat_dec_eq(v_x_1409_, v_zero_1410_);
if (v_isZero_1411_ == 1)
{
lean_dec(v_x_1409_);
return v_isZero_1411_;
}
else
{
lean_object* v_one_1412_; lean_object* v_n_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; uint8_t v___x_1417_; uint8_t v___x_1418_; 
v_one_1412_ = lean_unsigned_to_nat(1u);
v_n_1413_ = lean_nat_sub(v_x_1409_, v_one_1412_);
lean_dec(v_x_1409_);
v___x_1414_ = lean_array_fget_borrowed(v_xs_1407_, v_n_1413_);
v___x_1415_ = lean_array_fget_borrowed(v_ys_1408_, v_n_1413_);
v___x_1416_ = lean_unbox(v___x_1414_);
v___x_1417_ = lean_unbox(v___x_1415_);
v___x_1418_ = l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(v___x_1416_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_dec(v_n_1413_);
return v___x_1418_;
}
else
{
v_x_1409_ = v_n_1413_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg___boxed(lean_object* v_xs_1420_, lean_object* v_ys_1421_, lean_object* v_x_1422_){
_start:
{
uint8_t v_res_1423_; lean_object* v_r_1424_; 
v_res_1423_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(v_xs_1420_, v_ys_1421_, v_x_1422_);
lean_dec_ref(v_ys_1421_);
lean_dec_ref(v_xs_1420_);
v_r_1424_ = lean_box(v_res_1423_);
return v_r_1424_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(lean_object* v_x_1425_, lean_object* v_x_1426_){
_start:
{
if (lean_obj_tag(v_x_1425_) == 0)
{
if (lean_obj_tag(v_x_1426_) == 0)
{
uint8_t v___x_1427_; 
v___x_1427_ = 1;
return v___x_1427_;
}
else
{
uint8_t v___x_1428_; 
v___x_1428_ = 0;
return v___x_1428_;
}
}
else
{
if (lean_obj_tag(v_x_1426_) == 0)
{
uint8_t v___x_1429_; 
v___x_1429_ = 0;
return v___x_1429_;
}
else
{
lean_object* v_val_1430_; lean_object* v_val_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v_val_1430_ = lean_ctor_get(v_x_1425_, 0);
v_val_1431_ = lean_ctor_get(v_x_1426_, 0);
v___x_1432_ = lean_array_get_size(v_val_1430_);
v___x_1433_ = lean_array_get_size(v_val_1431_);
v___x_1434_ = lean_nat_dec_eq(v___x_1432_, v___x_1433_);
if (v___x_1434_ == 0)
{
return v___x_1434_;
}
else
{
uint8_t v___x_1435_; 
v___x_1435_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(v_val_1430_, v_val_1431_, v___x_1432_);
return v___x_1435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7___boxed(lean_object* v_x_1436_, lean_object* v_x_1437_){
_start:
{
uint8_t v_res_1438_; lean_object* v_r_1439_; 
v_res_1438_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(v_x_1436_, v_x_1437_);
lean_dec(v_x_1437_);
lean_dec(v_x_1436_);
v_r_1439_ = lean_box(v_res_1438_);
return v_r_1439_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(lean_object* v_x_1440_, lean_object* v_x_1441_){
_start:
{
if (lean_obj_tag(v_x_1440_) == 0)
{
if (lean_obj_tag(v_x_1441_) == 0)
{
uint8_t v___x_1442_; 
v___x_1442_ = 1;
return v___x_1442_;
}
else
{
uint8_t v___x_1443_; 
v___x_1443_ = 0;
return v___x_1443_;
}
}
else
{
if (lean_obj_tag(v_x_1441_) == 0)
{
uint8_t v___x_1444_; 
v___x_1444_ = 0;
return v___x_1444_;
}
else
{
lean_object* v_val_1445_; lean_object* v_val_1446_; uint8_t v___x_1447_; 
v_val_1445_ = lean_ctor_get(v_x_1440_, 0);
v_val_1446_ = lean_ctor_get(v_x_1441_, 0);
v___x_1447_ = l_Lean_Lsp_instBEqDiagnosticCode_beq(v_val_1445_, v_val_1446_);
return v___x_1447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4___boxed(lean_object* v_x_1448_, lean_object* v_x_1449_){
_start:
{
uint8_t v_res_1450_; lean_object* v_r_1451_; 
v_res_1450_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(v_x_1448_, v_x_1449_);
lean_dec(v_x_1449_);
lean_dec(v_x_1448_);
v_r_1451_ = lean_box(v_res_1450_);
return v_r_1451_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(lean_object* v_x_1452_, lean_object* v_x_1453_){
_start:
{
if (lean_obj_tag(v_x_1452_) == 0)
{
if (lean_obj_tag(v_x_1453_) == 0)
{
uint8_t v___x_1454_; 
v___x_1454_ = 1;
return v___x_1454_;
}
else
{
uint8_t v___x_1455_; 
v___x_1455_ = 0;
return v___x_1455_;
}
}
else
{
if (lean_obj_tag(v_x_1453_) == 0)
{
uint8_t v___x_1456_; 
v___x_1456_ = 0;
return v___x_1456_;
}
else
{
lean_object* v_val_1457_; lean_object* v_val_1458_; uint8_t v___x_1459_; 
v_val_1457_ = lean_ctor_get(v_x_1452_, 0);
v_val_1458_ = lean_ctor_get(v_x_1453_, 0);
v___x_1459_ = l_Lean_Lsp_instBEqRange_beq(v_val_1457_, v_val_1458_);
return v___x_1459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2___boxed(lean_object* v_x_1460_, lean_object* v_x_1461_){
_start:
{
uint8_t v_res_1462_; lean_object* v_r_1463_; 
v_res_1462_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(v_x_1460_, v_x_1461_);
lean_dec(v_x_1461_);
lean_dec(v_x_1460_);
v_r_1463_ = lean_box(v_res_1462_);
return v_r_1463_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(lean_object* v_x_1464_, lean_object* v_x_1465_){
_start:
{
if (lean_obj_tag(v_x_1464_) == 0)
{
if (lean_obj_tag(v_x_1465_) == 0)
{
uint8_t v___x_1466_; 
v___x_1466_ = 1;
return v___x_1466_;
}
else
{
uint8_t v___x_1467_; 
v___x_1467_ = 0;
return v___x_1467_;
}
}
else
{
if (lean_obj_tag(v_x_1465_) == 0)
{
uint8_t v___x_1468_; 
v___x_1468_ = 0;
return v___x_1468_;
}
else
{
lean_object* v_val_1469_; lean_object* v_val_1470_; uint8_t v___x_1471_; 
v_val_1469_ = lean_ctor_get(v_x_1464_, 0);
v_val_1470_ = lean_ctor_get(v_x_1465_, 0);
v___x_1471_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_val_1469_, v_val_1470_);
return v___x_1471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9___boxed(lean_object* v_x_1472_, lean_object* v_x_1473_){
_start:
{
uint8_t v_res_1474_; lean_object* v_r_1475_; 
v_res_1474_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(v_x_1472_, v_x_1473_);
lean_dec(v_x_1473_);
lean_dec(v_x_1472_);
v_r_1475_ = lean_box(v_res_1474_);
return v_r_1475_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(lean_object* v_x_1476_, lean_object* v_x_1477_){
_start:
{
if (lean_obj_tag(v_x_1476_) == 0)
{
if (lean_obj_tag(v_x_1477_) == 0)
{
uint8_t v___x_1478_; 
v___x_1478_ = 1;
return v___x_1478_;
}
else
{
uint8_t v___x_1479_; 
v___x_1479_ = 0;
return v___x_1479_;
}
}
else
{
if (lean_obj_tag(v_x_1477_) == 0)
{
uint8_t v___x_1480_; 
v___x_1480_ = 0;
return v___x_1480_;
}
else
{
lean_object* v_val_1481_; lean_object* v_val_1482_; uint8_t v___x_1483_; 
v_val_1481_ = lean_ctor_get(v_x_1476_, 0);
v_val_1482_ = lean_ctor_get(v_x_1477_, 0);
v___x_1483_ = lean_string_dec_eq(v_val_1481_, v_val_1482_);
return v___x_1483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5___boxed(lean_object* v_x_1484_, lean_object* v_x_1485_){
_start:
{
uint8_t v_res_1486_; lean_object* v_r_1487_; 
v_res_1486_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(v_x_1484_, v_x_1485_);
lean_dec(v_x_1485_);
lean_dec(v_x_1484_);
v_r_1487_ = lean_box(v_res_1486_);
return v_r_1487_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(lean_object* v_xs_1488_, lean_object* v_ys_1489_, lean_object* v_x_1490_){
_start:
{
lean_object* v_zero_1491_; uint8_t v_isZero_1492_; 
v_zero_1491_ = lean_unsigned_to_nat(0u);
v_isZero_1492_ = lean_nat_dec_eq(v_x_1490_, v_zero_1491_);
if (v_isZero_1492_ == 1)
{
lean_dec(v_x_1490_);
return v_isZero_1492_;
}
else
{
lean_object* v_one_1493_; lean_object* v_n_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; uint8_t v___x_1498_; uint8_t v___x_1499_; 
v_one_1493_ = lean_unsigned_to_nat(1u);
v_n_1494_ = lean_nat_sub(v_x_1490_, v_one_1493_);
lean_dec(v_x_1490_);
v___x_1495_ = lean_array_fget_borrowed(v_xs_1488_, v_n_1494_);
v___x_1496_ = lean_array_fget_borrowed(v_ys_1489_, v_n_1494_);
v___x_1497_ = lean_unbox(v___x_1495_);
v___x_1498_ = lean_unbox(v___x_1496_);
v___x_1499_ = l_Lean_Lsp_instBEqDiagnosticTag_beq(v___x_1497_, v___x_1498_);
if (v___x_1499_ == 0)
{
lean_dec(v_n_1494_);
return v___x_1499_;
}
else
{
v_x_1490_ = v_n_1494_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg___boxed(lean_object* v_xs_1501_, lean_object* v_ys_1502_, lean_object* v_x_1503_){
_start:
{
uint8_t v_res_1504_; lean_object* v_r_1505_; 
v_res_1504_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(v_xs_1501_, v_ys_1502_, v_x_1503_);
lean_dec_ref(v_ys_1502_);
lean_dec_ref(v_xs_1501_);
v_r_1505_ = lean_box(v_res_1504_);
return v_r_1505_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(lean_object* v_x_1506_, lean_object* v_x_1507_){
_start:
{
if (lean_obj_tag(v_x_1506_) == 0)
{
if (lean_obj_tag(v_x_1507_) == 0)
{
uint8_t v___x_1508_; 
v___x_1508_ = 1;
return v___x_1508_;
}
else
{
uint8_t v___x_1509_; 
v___x_1509_ = 0;
return v___x_1509_;
}
}
else
{
if (lean_obj_tag(v_x_1507_) == 0)
{
uint8_t v___x_1510_; 
v___x_1510_ = 0;
return v___x_1510_;
}
else
{
lean_object* v_val_1511_; lean_object* v_val_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; 
v_val_1511_ = lean_ctor_get(v_x_1506_, 0);
v_val_1512_ = lean_ctor_get(v_x_1507_, 0);
v___x_1513_ = lean_array_get_size(v_val_1511_);
v___x_1514_ = lean_array_get_size(v_val_1512_);
v___x_1515_ = lean_nat_dec_eq(v___x_1513_, v___x_1514_);
if (v___x_1515_ == 0)
{
return v___x_1515_;
}
else
{
uint8_t v___x_1516_; 
v___x_1516_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(v_val_1511_, v_val_1512_, v___x_1513_);
return v___x_1516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6___boxed(lean_object* v_x_1517_, lean_object* v_x_1518_){
_start:
{
uint8_t v_res_1519_; lean_object* v_r_1520_; 
v_res_1519_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(v_x_1517_, v_x_1518_);
lean_dec(v_x_1518_);
lean_dec(v_x_1517_);
v_r_1520_ = lean_box(v_res_1519_);
return v_r_1520_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(lean_object* v_x_1521_, lean_object* v_x_1522_){
_start:
{
if (lean_obj_tag(v_x_1521_) == 0)
{
if (lean_obj_tag(v_x_1522_) == 0)
{
uint8_t v___x_1523_; 
v___x_1523_ = 1;
return v___x_1523_;
}
else
{
uint8_t v___x_1524_; 
v___x_1524_ = 0;
return v___x_1524_;
}
}
else
{
if (lean_obj_tag(v_x_1522_) == 0)
{
uint8_t v___x_1525_; 
v___x_1525_ = 0;
return v___x_1525_;
}
else
{
lean_object* v_val_1526_; lean_object* v_val_1527_; uint8_t v___x_1528_; uint8_t v___x_1529_; uint8_t v___x_1530_; 
v_val_1526_ = lean_ctor_get(v_x_1521_, 0);
v_val_1527_ = lean_ctor_get(v_x_1522_, 0);
v___x_1528_ = lean_unbox(v_val_1526_);
v___x_1529_ = lean_unbox(v_val_1527_);
v___x_1530_ = l_Lean_Lsp_instBEqDiagnosticSeverity_beq(v___x_1528_, v___x_1529_);
return v___x_1530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3___boxed(lean_object* v_x_1531_, lean_object* v_x_1532_){
_start:
{
uint8_t v_res_1533_; lean_object* v_r_1534_; 
v_res_1533_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(v_x_1531_, v_x_1532_);
lean_dec(v_x_1532_);
lean_dec(v_x_1531_);
v_r_1534_ = lean_box(v_res_1533_);
return v_r_1534_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(lean_object* v_x_1535_, lean_object* v_x_1536_){
_start:
{
lean_object* v_range_1537_; lean_object* v_fullRange_x3f_1538_; lean_object* v_severity_x3f_1539_; lean_object* v_isSilent_x3f_1540_; lean_object* v_code_x3f_1541_; lean_object* v_source_x3f_1542_; lean_object* v_message_1543_; lean_object* v_tags_x3f_1544_; lean_object* v_leanTags_x3f_1545_; lean_object* v_relatedInformation_x3f_1546_; lean_object* v_data_x3f_1547_; lean_object* v_range_1548_; lean_object* v_fullRange_x3f_1549_; lean_object* v_severity_x3f_1550_; lean_object* v_isSilent_x3f_1551_; lean_object* v_code_x3f_1552_; lean_object* v_source_x3f_1553_; lean_object* v_message_1554_; lean_object* v_tags_x3f_1555_; lean_object* v_leanTags_x3f_1556_; lean_object* v_relatedInformation_x3f_1557_; lean_object* v_data_x3f_1558_; uint8_t v___x_1559_; 
v_range_1537_ = lean_ctor_get(v_x_1535_, 0);
v_fullRange_x3f_1538_ = lean_ctor_get(v_x_1535_, 1);
v_severity_x3f_1539_ = lean_ctor_get(v_x_1535_, 2);
v_isSilent_x3f_1540_ = lean_ctor_get(v_x_1535_, 3);
v_code_x3f_1541_ = lean_ctor_get(v_x_1535_, 4);
v_source_x3f_1542_ = lean_ctor_get(v_x_1535_, 5);
v_message_1543_ = lean_ctor_get(v_x_1535_, 6);
v_tags_x3f_1544_ = lean_ctor_get(v_x_1535_, 7);
v_leanTags_x3f_1545_ = lean_ctor_get(v_x_1535_, 8);
v_relatedInformation_x3f_1546_ = lean_ctor_get(v_x_1535_, 9);
v_data_x3f_1547_ = lean_ctor_get(v_x_1535_, 10);
v_range_1548_ = lean_ctor_get(v_x_1536_, 0);
v_fullRange_x3f_1549_ = lean_ctor_get(v_x_1536_, 1);
v_severity_x3f_1550_ = lean_ctor_get(v_x_1536_, 2);
v_isSilent_x3f_1551_ = lean_ctor_get(v_x_1536_, 3);
v_code_x3f_1552_ = lean_ctor_get(v_x_1536_, 4);
v_source_x3f_1553_ = lean_ctor_get(v_x_1536_, 5);
v_message_1554_ = lean_ctor_get(v_x_1536_, 6);
v_tags_x3f_1555_ = lean_ctor_get(v_x_1536_, 7);
v_leanTags_x3f_1556_ = lean_ctor_get(v_x_1536_, 8);
v_relatedInformation_x3f_1557_ = lean_ctor_get(v_x_1536_, 9);
v_data_x3f_1558_ = lean_ctor_get(v_x_1536_, 10);
v___x_1559_ = l_Lean_Lsp_instBEqRange_beq(v_range_1537_, v_range_1548_);
if (v___x_1559_ == 0)
{
return v___x_1559_;
}
else
{
uint8_t v___x_1560_; 
v___x_1560_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(v_fullRange_x3f_1538_, v_fullRange_x3f_1549_);
if (v___x_1560_ == 0)
{
return v___x_1560_;
}
else
{
uint8_t v___x_1561_; 
v___x_1561_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(v_severity_x3f_1539_, v_severity_x3f_1550_);
if (v___x_1561_ == 0)
{
return v___x_1561_;
}
else
{
uint8_t v___x_1562_; 
v___x_1562_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(v_isSilent_x3f_1540_, v_isSilent_x3f_1551_);
if (v___x_1562_ == 0)
{
return v___x_1562_;
}
else
{
uint8_t v___x_1563_; 
v___x_1563_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(v_code_x3f_1541_, v_code_x3f_1552_);
if (v___x_1563_ == 0)
{
return v___x_1563_;
}
else
{
uint8_t v___x_1564_; 
v___x_1564_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(v_source_x3f_1542_, v_source_x3f_1553_);
if (v___x_1564_ == 0)
{
return v___x_1564_;
}
else
{
uint8_t v___x_1565_; 
v___x_1565_ = lean_string_dec_eq(v_message_1543_, v_message_1554_);
if (v___x_1565_ == 0)
{
return v___x_1565_;
}
else
{
uint8_t v___x_1566_; 
v___x_1566_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(v_tags_x3f_1544_, v_tags_x3f_1555_);
if (v___x_1566_ == 0)
{
return v___x_1566_;
}
else
{
uint8_t v___x_1567_; 
v___x_1567_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(v_leanTags_x3f_1545_, v_leanTags_x3f_1556_);
if (v___x_1567_ == 0)
{
return v___x_1567_;
}
else
{
uint8_t v___x_1568_; 
v___x_1568_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(v_relatedInformation_x3f_1546_, v_relatedInformation_x3f_1557_);
if (v___x_1568_ == 0)
{
return v___x_1568_;
}
else
{
uint8_t v___x_1569_; 
v___x_1569_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(v_data_x3f_1547_, v_data_x3f_1558_);
return v___x_1569_;
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
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2___boxed(lean_object* v_x_1570_, lean_object* v_x_1571_){
_start:
{
uint8_t v_res_1572_; lean_object* v_r_1573_; 
v_res_1572_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(v_x_1570_, v_x_1571_);
lean_dec_ref(v_x_1571_);
lean_dec_ref(v_x_1570_);
v_r_1573_ = lean_box(v_res_1572_);
return v_r_1573_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(lean_object* v_xs_1574_, lean_object* v_ys_1575_, lean_object* v_x_1576_){
_start:
{
lean_object* v_zero_1577_; uint8_t v_isZero_1578_; 
v_zero_1577_ = lean_unsigned_to_nat(0u);
v_isZero_1578_ = lean_nat_dec_eq(v_x_1576_, v_zero_1577_);
if (v_isZero_1578_ == 1)
{
lean_dec(v_x_1576_);
return v_isZero_1578_;
}
else
{
lean_object* v_one_1579_; lean_object* v_n_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v_one_1579_ = lean_unsigned_to_nat(1u);
v_n_1580_ = lean_nat_sub(v_x_1576_, v_one_1579_);
lean_dec(v_x_1576_);
v___x_1581_ = lean_array_fget_borrowed(v_xs_1574_, v_n_1580_);
v___x_1582_ = lean_array_fget_borrowed(v_ys_1575_, v_n_1580_);
v___x_1583_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(v___x_1581_, v___x_1582_);
if (v___x_1583_ == 0)
{
lean_dec(v_n_1580_);
return v___x_1583_;
}
else
{
v_x_1576_ = v_n_1580_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg___boxed(lean_object* v_xs_1585_, lean_object* v_ys_1586_, lean_object* v_x_1587_){
_start:
{
uint8_t v_res_1588_; lean_object* v_r_1589_; 
v_res_1588_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(v_xs_1585_, v_ys_1586_, v_x_1587_);
lean_dec_ref(v_ys_1586_);
lean_dec_ref(v_xs_1585_);
v_r_1589_ = lean_box(v_res_1588_);
return v_r_1589_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq(lean_object* v_x_1590_, lean_object* v_x_1591_){
_start:
{
lean_object* v_uri_1592_; lean_object* v_version_x3f_1593_; lean_object* v_isIncremental_x3f_1594_; lean_object* v_diagnostics_1595_; lean_object* v_uri_1596_; lean_object* v_version_x3f_1597_; lean_object* v_isIncremental_x3f_1598_; lean_object* v_diagnostics_1599_; uint8_t v___x_1600_; 
v_uri_1592_ = lean_ctor_get(v_x_1590_, 0);
v_version_x3f_1593_ = lean_ctor_get(v_x_1590_, 1);
v_isIncremental_x3f_1594_ = lean_ctor_get(v_x_1590_, 2);
v_diagnostics_1595_ = lean_ctor_get(v_x_1590_, 3);
v_uri_1596_ = lean_ctor_get(v_x_1591_, 0);
v_version_x3f_1597_ = lean_ctor_get(v_x_1591_, 1);
v_isIncremental_x3f_1598_ = lean_ctor_get(v_x_1591_, 2);
v_diagnostics_1599_ = lean_ctor_get(v_x_1591_, 3);
v___x_1600_ = lean_string_dec_eq(v_uri_1592_, v_uri_1596_);
if (v___x_1600_ == 0)
{
return v___x_1600_;
}
else
{
uint8_t v___x_1601_; 
v___x_1601_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(v_version_x3f_1593_, v_version_x3f_1597_);
if (v___x_1601_ == 0)
{
return v___x_1601_;
}
else
{
uint8_t v___x_1602_; 
v___x_1602_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(v_isIncremental_x3f_1594_, v_isIncremental_x3f_1598_);
if (v___x_1602_ == 0)
{
return v___x_1602_;
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v___x_1603_ = lean_array_get_size(v_diagnostics_1595_);
v___x_1604_ = lean_array_get_size(v_diagnostics_1599_);
v___x_1605_ = lean_nat_dec_eq(v___x_1603_, v___x_1604_);
if (v___x_1605_ == 0)
{
return v___x_1605_;
}
else
{
uint8_t v___x_1606_; 
v___x_1606_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(v_diagnostics_1595_, v_diagnostics_1599_, v___x_1603_);
return v___x_1606_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq___boxed(lean_object* v_x_1607_, lean_object* v_x_1608_){
_start:
{
uint8_t v_res_1609_; lean_object* v_r_1610_; 
v_res_1609_ = l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq(v_x_1607_, v_x_1608_);
lean_dec_ref(v_x_1608_);
lean_dec_ref(v_x_1607_);
v_r_1610_ = lean_box(v_res_1609_);
return v_r_1610_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3(lean_object* v_xs_1611_, lean_object* v_ys_1612_, lean_object* v_hsz_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_){
_start:
{
uint8_t v___x_1616_; 
v___x_1616_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(v_xs_1611_, v_ys_1612_, v_x_1614_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___boxed(lean_object* v_xs_1617_, lean_object* v_ys_1618_, lean_object* v_hsz_1619_, lean_object* v_x_1620_, lean_object* v_x_1621_){
_start:
{
uint8_t v_res_1622_; lean_object* v_r_1623_; 
v_res_1622_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3(v_xs_1617_, v_ys_1618_, v_hsz_1619_, v_x_1620_, v_x_1621_);
lean_dec_ref(v_ys_1618_);
lean_dec_ref(v_xs_1617_);
v_r_1623_ = lean_box(v_res_1622_);
return v_r_1623_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7(lean_object* v_xs_1624_, lean_object* v_ys_1625_, lean_object* v_hsz_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_){
_start:
{
uint8_t v___x_1629_; 
v___x_1629_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(v_xs_1624_, v_ys_1625_, v_x_1627_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___boxed(lean_object* v_xs_1630_, lean_object* v_ys_1631_, lean_object* v_hsz_1632_, lean_object* v_x_1633_, lean_object* v_x_1634_){
_start:
{
uint8_t v_res_1635_; lean_object* v_r_1636_; 
v_res_1635_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7(v_xs_1630_, v_ys_1631_, v_hsz_1632_, v_x_1633_, v_x_1634_);
lean_dec_ref(v_ys_1631_);
lean_dec_ref(v_xs_1630_);
v_r_1636_ = lean_box(v_res_1635_);
return v_r_1636_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9(lean_object* v_xs_1637_, lean_object* v_ys_1638_, lean_object* v_hsz_1639_, lean_object* v_x_1640_, lean_object* v_x_1641_){
_start:
{
uint8_t v___x_1642_; 
v___x_1642_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(v_xs_1637_, v_ys_1638_, v_x_1640_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___boxed(lean_object* v_xs_1643_, lean_object* v_ys_1644_, lean_object* v_hsz_1645_, lean_object* v_x_1646_, lean_object* v_x_1647_){
_start:
{
uint8_t v_res_1648_; lean_object* v_r_1649_; 
v_res_1648_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9(v_xs_1643_, v_ys_1644_, v_hsz_1645_, v_x_1646_, v_x_1647_);
lean_dec_ref(v_ys_1644_);
lean_dec_ref(v_xs_1643_);
v_r_1649_ = lean_box(v_res_1648_);
return v_r_1649_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11(lean_object* v_xs_1650_, lean_object* v_ys_1651_, lean_object* v_hsz_1652_, lean_object* v_x_1653_, lean_object* v_x_1654_){
_start:
{
uint8_t v___x_1655_; 
v___x_1655_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(v_xs_1650_, v_ys_1651_, v_x_1653_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___boxed(lean_object* v_xs_1656_, lean_object* v_ys_1657_, lean_object* v_hsz_1658_, lean_object* v_x_1659_, lean_object* v_x_1660_){
_start:
{
uint8_t v_res_1661_; lean_object* v_r_1662_; 
v_res_1661_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11(v_xs_1656_, v_ys_1657_, v_hsz_1658_, v_x_1659_, v_x_1660_);
lean_dec_ref(v_ys_1657_);
lean_dec_ref(v_xs_1656_);
v_r_1662_ = lean_box(v_res_1661_);
return v_r_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__0(lean_object* v_k_1665_, lean_object* v_x_1666_){
_start:
{
if (lean_obj_tag(v_x_1666_) == 0)
{
lean_object* v___x_1667_; 
lean_dec_ref(v_k_1665_);
v___x_1667_ = lean_box(0);
return v___x_1667_;
}
else
{
lean_object* v_val_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1679_; 
v_val_1668_ = lean_ctor_get(v_x_1666_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_x_1666_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1670_ = v_x_1666_;
v_isShared_1671_ = v_isSharedCheck_1679_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_val_1668_);
lean_dec(v_x_1666_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1679_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1672_ = l_Lean_JsonNumber_fromInt(v_val_1668_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set_tag(v___x_1670_, 2);
lean_ctor_set(v___x_1670_, 0, v___x_1672_);
v___x_1674_ = v___x_1670_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_k_1665_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = lean_box(0);
v___x_1677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1675_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
return v___x_1677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(lean_object* v_k_1680_, lean_object* v_x_1681_){
_start:
{
if (lean_obj_tag(v_x_1681_) == 0)
{
lean_object* v___x_1682_; 
lean_dec_ref(v_k_1680_);
v___x_1682_ = lean_box(0);
return v___x_1682_;
}
else
{
lean_object* v_val_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_val_1683_ = lean_ctor_get(v_x_1681_, 0);
v___x_1684_ = lean_alloc_ctor(1, 0, 1);
v___x_1685_ = lean_unbox(v_val_1683_);
lean_ctor_set_uint8(v___x_1684_, 0, v___x_1685_);
v___x_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1686_, 0, v_k_1680_);
lean_ctor_set(v___x_1686_, 1, v___x_1684_);
v___x_1687_ = lean_box(0);
v___x_1688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1686_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
return v___x_1688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1___boxed(lean_object* v_k_1689_, lean_object* v_x_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(v_k_1689_, v_x_1690_);
lean_dec(v_x_1690_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(lean_object* v_k_1692_, lean_object* v_x_1693_){
_start:
{
if (lean_obj_tag(v_x_1693_) == 0)
{
lean_object* v___x_1694_; 
lean_dec_ref(v_k_1692_);
v___x_1694_ = lean_box(0);
return v___x_1694_;
}
else
{
lean_object* v_val_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v_val_1695_ = lean_ctor_get(v_x_1693_, 0);
lean_inc(v_val_1695_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v_k_1692_);
lean_ctor_set(v___x_1696_, 1, v_val_1695_);
v___x_1697_ = lean_box(0);
v___x_1698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
return v___x_1698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10___boxed(lean_object* v_k_1699_, lean_object* v_x_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(v_k_1699_, v_x_1700_);
lean_dec(v_x_1700_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__5(lean_object* v_k_1702_, lean_object* v_x_1703_){
_start:
{
lean_object* v___y_1705_; 
if (lean_obj_tag(v_x_1703_) == 0)
{
lean_object* v___x_1709_; 
lean_dec_ref(v_k_1702_);
v___x_1709_ = lean_box(0);
return v___x_1709_;
}
else
{
lean_object* v_val_1710_; 
v_val_1710_ = lean_ctor_get(v_x_1703_, 0);
lean_inc(v_val_1710_);
lean_dec_ref_known(v_x_1703_, 1);
if (lean_obj_tag(v_val_1710_) == 0)
{
lean_object* v_i_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1719_; 
v_i_1711_ = lean_ctor_get(v_val_1710_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_val_1710_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1713_ = v_val_1710_;
v_isShared_1714_ = v_isSharedCheck_1719_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_i_1711_);
lean_dec(v_val_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1719_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1715_ = l_Lean_JsonNumber_fromInt(v_i_1711_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set_tag(v___x_1713_, 2);
lean_ctor_set(v___x_1713_, 0, v___x_1715_);
v___x_1717_ = v___x_1713_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
v___y_1705_ = v___x_1717_;
goto v___jp_1704_;
}
}
}
else
{
lean_object* v_s_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
v_s_1720_ = lean_ctor_get(v_val_1710_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_val_1710_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v_val_1710_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_s_1720_);
lean_dec(v_val_1710_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set_tag(v___x_1722_, 3);
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_s_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
v___y_1705_ = v___x_1725_;
goto v___jp_1704_;
}
}
}
}
v___jp_1704_:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v_k_1702_);
lean_ctor_set(v___x_1706_, 1, v___y_1705_);
v___x_1707_ = lean_box(0);
v___x_1708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1706_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
return v___x_1708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__6(lean_object* v_k_1728_, lean_object* v_x_1729_){
_start:
{
if (lean_obj_tag(v_x_1729_) == 0)
{
lean_object* v___x_1730_; 
lean_dec_ref(v_k_1728_);
v___x_1730_ = lean_box(0);
return v___x_1730_;
}
else
{
lean_object* v_val_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1741_; 
v_val_1731_ = lean_ctor_get(v_x_1729_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_x_1729_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1733_ = v_x_1729_;
v_isShared_1734_ = v_isSharedCheck_1741_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_val_1731_);
lean_dec(v_x_1729_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1741_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set_tag(v___x_1733_, 3);
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_val_1731_);
v___x_1736_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1737_, 0, v_k_1728_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v___x_1738_ = lean_box(0);
v___x_1739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1737_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
return v___x_1739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(size_t v_sz_1742_, size_t v_i_1743_, lean_object* v_bs_1744_){
_start:
{
uint8_t v___x_1745_; 
v___x_1745_ = lean_usize_dec_lt(v_i_1743_, v_sz_1742_);
if (v___x_1745_ == 0)
{
return v_bs_1744_;
}
else
{
lean_object* v_v_1746_; lean_object* v___x_1747_; lean_object* v_bs_x27_1748_; lean_object* v___y_1750_; uint8_t v___x_1755_; 
v_v_1746_ = lean_array_uget(v_bs_1744_, v_i_1743_);
v___x_1747_ = lean_unsigned_to_nat(0u);
v_bs_x27_1748_ = lean_array_uset(v_bs_1744_, v_i_1743_, v___x_1747_);
v___x_1755_ = lean_unbox(v_v_1746_);
lean_dec(v_v_1746_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; 
v___x_1756_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
v___y_1750_ = v___x_1756_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
v___y_1750_ = v___x_1757_;
goto v___jp_1749_;
}
v___jp_1749_:
{
size_t v___x_1751_; size_t v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = ((size_t)1ULL);
v___x_1752_ = lean_usize_add(v_i_1743_, v___x_1751_);
lean_inc(v___y_1750_);
v___x_1753_ = lean_array_uset(v_bs_x27_1748_, v_i_1743_, v___y_1750_);
v_i_1743_ = v___x_1752_;
v_bs_1744_ = v___x_1753_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14___boxed(lean_object* v_sz_1758_, lean_object* v_i_1759_, lean_object* v_bs_1760_){
_start:
{
size_t v_sz_boxed_1761_; size_t v_i_boxed_1762_; lean_object* v_res_1763_; 
v_sz_boxed_1761_ = lean_unbox_usize(v_sz_1758_);
lean_dec(v_sz_1758_);
v_i_boxed_1762_ = lean_unbox_usize(v_i_1759_);
lean_dec(v_i_1759_);
v_res_1763_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(v_sz_boxed_1761_, v_i_boxed_1762_, v_bs_1760_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10(lean_object* v_a_1764_){
_start:
{
size_t v_sz_1765_; size_t v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v_sz_1765_ = lean_array_size(v_a_1764_);
v___x_1766_ = ((size_t)0ULL);
v___x_1767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(v_sz_1765_, v___x_1766_, v_a_1764_);
v___x_1768_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8(lean_object* v_k_1769_, lean_object* v_x_1770_){
_start:
{
if (lean_obj_tag(v_x_1770_) == 0)
{
lean_object* v___x_1771_; 
lean_dec_ref(v_k_1769_);
v___x_1771_ = lean_box(0);
return v___x_1771_;
}
else
{
lean_object* v_val_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_val_1772_ = lean_ctor_get(v_x_1770_, 0);
lean_inc(v_val_1772_);
lean_dec_ref_known(v_x_1770_, 1);
v___x_1773_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10(v_val_1772_);
v___x_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1774_, 0, v_k_1769_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = lean_box(0);
v___x_1776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1774_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
return v___x_1776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(lean_object* v_k_1777_, lean_object* v_x_1778_){
_start:
{
lean_object* v___y_1780_; 
if (lean_obj_tag(v_x_1778_) == 0)
{
lean_object* v___x_1784_; 
lean_dec_ref(v_k_1777_);
v___x_1784_ = lean_box(0);
return v___x_1784_;
}
else
{
lean_object* v_val_1785_; uint8_t v___x_1786_; 
v_val_1785_ = lean_ctor_get(v_x_1778_, 0);
v___x_1786_ = lean_unbox(v_val_1785_);
switch(v___x_1786_)
{
case 0:
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
v___y_1780_ = v___x_1787_;
goto v___jp_1779_;
}
case 1:
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
v___y_1780_ = v___x_1788_;
goto v___jp_1779_;
}
case 2:
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5);
v___y_1780_ = v___x_1789_;
goto v___jp_1779_;
}
default: 
{
lean_object* v___x_1790_; 
v___x_1790_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7);
v___y_1780_ = v___x_1790_;
goto v___jp_1779_;
}
}
}
v___jp_1779_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
lean_inc(v___y_1780_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v_k_1777_);
lean_ctor_set(v___x_1781_, 1, v___y_1780_);
v___x_1782_ = lean_box(0);
v___x_1783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
return v___x_1783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4___boxed(lean_object* v_k_1791_, lean_object* v_x_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(v_k_1791_, v_x_1792_);
lean_dec(v_x_1792_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(size_t v_sz_1794_, size_t v_i_1795_, lean_object* v_bs_1796_){
_start:
{
uint8_t v___x_1797_; 
v___x_1797_ = lean_usize_dec_lt(v_i_1795_, v_sz_1794_);
if (v___x_1797_ == 0)
{
return v_bs_1796_;
}
else
{
lean_object* v_v_1798_; lean_object* v___x_1799_; lean_object* v_bs_x27_1800_; lean_object* v___x_1801_; size_t v___x_1802_; size_t v___x_1803_; lean_object* v___x_1804_; 
v_v_1798_ = lean_array_uget(v_bs_1796_, v_i_1795_);
v___x_1799_ = lean_unsigned_to_nat(0u);
v_bs_x27_1800_ = lean_array_uset(v_bs_1796_, v_i_1795_, v___x_1799_);
v___x_1801_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(v_v_1798_);
v___x_1802_ = ((size_t)1ULL);
v___x_1803_ = lean_usize_add(v_i_1795_, v___x_1802_);
v___x_1804_ = lean_array_uset(v_bs_x27_1800_, v_i_1795_, v___x_1801_);
v_i_1795_ = v___x_1803_;
v_bs_1796_ = v___x_1804_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17___boxed(lean_object* v_sz_1806_, lean_object* v_i_1807_, lean_object* v_bs_1808_){
_start:
{
size_t v_sz_boxed_1809_; size_t v_i_boxed_1810_; lean_object* v_res_1811_; 
v_sz_boxed_1809_ = lean_unbox_usize(v_sz_1806_);
lean_dec(v_sz_1806_);
v_i_boxed_1810_ = lean_unbox_usize(v_i_1807_);
lean_dec(v_i_1807_);
v_res_1811_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(v_sz_boxed_1809_, v_i_boxed_1810_, v_bs_1808_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12(lean_object* v_a_1812_){
_start:
{
size_t v_sz_1813_; size_t v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v_sz_1813_ = lean_array_size(v_a_1812_);
v___x_1814_ = ((size_t)0ULL);
v___x_1815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(v_sz_1813_, v___x_1814_, v_a_1812_);
v___x_1816_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9(lean_object* v_k_1817_, lean_object* v_x_1818_){
_start:
{
if (lean_obj_tag(v_x_1818_) == 0)
{
lean_object* v___x_1819_; 
lean_dec_ref(v_k_1817_);
v___x_1819_ = lean_box(0);
return v___x_1819_;
}
else
{
lean_object* v_val_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v_val_1820_ = lean_ctor_get(v_x_1818_, 0);
lean_inc(v_val_1820_);
lean_dec_ref_known(v_x_1818_, 1);
v___x_1821_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12(v_val_1820_);
v___x_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1822_, 0, v_k_1817_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = lean_box(0);
v___x_1824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1822_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
return v___x_1824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(size_t v_sz_1825_, size_t v_i_1826_, lean_object* v_bs_1827_){
_start:
{
uint8_t v___x_1828_; 
v___x_1828_ = lean_usize_dec_lt(v_i_1826_, v_sz_1825_);
if (v___x_1828_ == 0)
{
return v_bs_1827_;
}
else
{
lean_object* v_v_1829_; lean_object* v___x_1830_; lean_object* v_bs_x27_1831_; lean_object* v___y_1833_; uint8_t v___x_1838_; 
v_v_1829_ = lean_array_uget(v_bs_1827_, v_i_1826_);
v___x_1830_ = lean_unsigned_to_nat(0u);
v_bs_x27_1831_ = lean_array_uset(v_bs_1827_, v_i_1826_, v___x_1830_);
v___x_1838_ = lean_unbox(v_v_1829_);
lean_dec(v_v_1829_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; 
v___x_1839_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
v___y_1833_ = v___x_1839_;
goto v___jp_1832_;
}
else
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
v___y_1833_ = v___x_1840_;
goto v___jp_1832_;
}
v___jp_1832_:
{
size_t v___x_1834_; size_t v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = ((size_t)1ULL);
v___x_1835_ = lean_usize_add(v_i_1826_, v___x_1834_);
lean_inc(v___y_1833_);
v___x_1836_ = lean_array_uset(v_bs_x27_1831_, v_i_1826_, v___y_1833_);
v_i_1826_ = v___x_1835_;
v_bs_1827_ = v___x_1836_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11___boxed(lean_object* v_sz_1841_, lean_object* v_i_1842_, lean_object* v_bs_1843_){
_start:
{
size_t v_sz_boxed_1844_; size_t v_i_boxed_1845_; lean_object* v_res_1846_; 
v_sz_boxed_1844_ = lean_unbox_usize(v_sz_1841_);
lean_dec(v_sz_1841_);
v_i_boxed_1845_ = lean_unbox_usize(v_i_1842_);
lean_dec(v_i_1842_);
v_res_1846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(v_sz_boxed_1844_, v_i_boxed_1845_, v_bs_1843_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8(lean_object* v_a_1847_){
_start:
{
size_t v_sz_1848_; size_t v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v_sz_1848_ = lean_array_size(v_a_1847_);
v___x_1849_ = ((size_t)0ULL);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(v_sz_1848_, v___x_1849_, v_a_1847_);
v___x_1851_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7(lean_object* v_k_1852_, lean_object* v_x_1853_){
_start:
{
if (lean_obj_tag(v_x_1853_) == 0)
{
lean_object* v___x_1854_; 
lean_dec_ref(v_k_1852_);
v___x_1854_ = lean_box(0);
return v___x_1854_;
}
else
{
lean_object* v_val_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v_val_1855_ = lean_ctor_get(v_x_1853_, 0);
lean_inc(v_val_1855_);
lean_dec_ref_known(v_x_1853_, 1);
v___x_1856_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8(v_val_1855_);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v_k_1852_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_box(0);
v___x_1859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
return v___x_1859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__3(lean_object* v_k_1860_, lean_object* v_x_1861_){
_start:
{
if (lean_obj_tag(v_x_1861_) == 0)
{
lean_object* v___x_1862_; 
lean_dec_ref(v_k_1860_);
v___x_1862_ = lean_box(0);
return v___x_1862_;
}
else
{
lean_object* v_val_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_val_1863_ = lean_ctor_get(v_x_1861_, 0);
lean_inc(v_val_1863_);
lean_dec_ref_known(v_x_1861_, 1);
v___x_1864_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_1863_);
v___x_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1865_, 0, v_k_1860_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = lean_box(0);
v___x_1867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
return v___x_1867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2(lean_object* v_x_1868_){
_start:
{
lean_object* v_range_1869_; lean_object* v_fullRange_x3f_1870_; lean_object* v_severity_x3f_1871_; lean_object* v_isSilent_x3f_1872_; lean_object* v_code_x3f_1873_; lean_object* v_source_x3f_1874_; lean_object* v_message_1875_; lean_object* v_tags_x3f_1876_; lean_object* v_leanTags_x3f_1877_; lean_object* v_relatedInformation_x3f_1878_; lean_object* v_data_x3f_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v_range_1869_ = lean_ctor_get(v_x_1868_, 0);
lean_inc_ref(v_range_1869_);
v_fullRange_x3f_1870_ = lean_ctor_get(v_x_1868_, 1);
lean_inc(v_fullRange_x3f_1870_);
v_severity_x3f_1871_ = lean_ctor_get(v_x_1868_, 2);
lean_inc(v_severity_x3f_1871_);
v_isSilent_x3f_1872_ = lean_ctor_get(v_x_1868_, 3);
lean_inc(v_isSilent_x3f_1872_);
v_code_x3f_1873_ = lean_ctor_get(v_x_1868_, 4);
lean_inc(v_code_x3f_1873_);
v_source_x3f_1874_ = lean_ctor_get(v_x_1868_, 5);
lean_inc(v_source_x3f_1874_);
v_message_1875_ = lean_ctor_get(v_x_1868_, 6);
lean_inc(v_message_1875_);
v_tags_x3f_1876_ = lean_ctor_get(v_x_1868_, 7);
lean_inc(v_tags_x3f_1876_);
v_leanTags_x3f_1877_ = lean_ctor_get(v_x_1868_, 8);
lean_inc(v_leanTags_x3f_1877_);
v_relatedInformation_x3f_1878_ = lean_ctor_get(v_x_1868_, 9);
lean_inc(v_relatedInformation_x3f_1878_);
v_data_x3f_1879_ = lean_ctor_get(v_x_1868_, 10);
lean_inc(v_data_x3f_1879_);
lean_dec_ref(v_x_1868_);
v___x_1880_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
v___x_1881_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_1869_);
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1880_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = lean_box(0);
v___x_1884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1882_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
v___x_1886_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__3(v___x_1885_, v_fullRange_x3f_1870_);
v___x_1887_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
v___x_1888_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(v___x_1887_, v_severity_x3f_1871_);
lean_dec(v_severity_x3f_1871_);
v___x_1889_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
v___x_1890_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(v___x_1889_, v_isSilent_x3f_1872_);
lean_dec(v_isSilent_x3f_1872_);
v___x_1891_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
v___x_1892_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__5(v___x_1891_, v_code_x3f_1873_);
v___x_1893_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
v___x_1894_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__6(v___x_1893_, v_source_x3f_1874_);
v___x_1895_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
v___x_1896_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1896_, 0, v_message_1875_);
v___x_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1895_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
lean_ctor_set(v___x_1898_, 1, v___x_1883_);
v___x_1899_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
v___x_1900_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7(v___x_1899_, v_tags_x3f_1876_);
v___x_1901_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
v___x_1902_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8(v___x_1901_, v_leanTags_x3f_1877_);
v___x_1903_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
v___x_1904_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9(v___x_1903_, v_relatedInformation_x3f_1878_);
v___x_1905_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
v___x_1906_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(v___x_1905_, v_data_x3f_1879_);
lean_dec(v_data_x3f_1879_);
v___x_1907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v___x_1883_);
v___x_1908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1904_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1902_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1900_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1898_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1894_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1892_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1890_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1888_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1886_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1884_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2));
v___x_1919_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(v___x_1917_, v___x_1918_);
v___x_1920_ = l_Lean_Json_mkObj(v___x_1919_);
lean_dec(v___x_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(size_t v_sz_1921_, size_t v_i_1922_, lean_object* v_bs_1923_){
_start:
{
uint8_t v___x_1924_; 
v___x_1924_ = lean_usize_dec_lt(v_i_1922_, v_sz_1921_);
if (v___x_1924_ == 0)
{
return v_bs_1923_;
}
else
{
lean_object* v_v_1925_; lean_object* v___x_1926_; lean_object* v_bs_x27_1927_; lean_object* v___x_1928_; size_t v___x_1929_; size_t v___x_1930_; lean_object* v___x_1931_; 
v_v_1925_ = lean_array_uget(v_bs_1923_, v_i_1922_);
v___x_1926_ = lean_unsigned_to_nat(0u);
v_bs_x27_1927_ = lean_array_uset(v_bs_1923_, v_i_1922_, v___x_1926_);
v___x_1928_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2(v_v_1925_);
v___x_1929_ = ((size_t)1ULL);
v___x_1930_ = lean_usize_add(v_i_1922_, v___x_1929_);
v___x_1931_ = lean_array_uset(v_bs_x27_1927_, v_i_1922_, v___x_1928_);
v_i_1922_ = v___x_1930_;
v_bs_1923_ = v___x_1931_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3___boxed(lean_object* v_sz_1933_, lean_object* v_i_1934_, lean_object* v_bs_1935_){
_start:
{
size_t v_sz_boxed_1936_; size_t v_i_boxed_1937_; lean_object* v_res_1938_; 
v_sz_boxed_1936_ = lean_unbox_usize(v_sz_1933_);
lean_dec(v_sz_1933_);
v_i_boxed_1937_ = lean_unbox_usize(v_i_1934_);
lean_dec(v_i_1934_);
v_res_1938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(v_sz_boxed_1936_, v_i_boxed_1937_, v_bs_1935_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2(lean_object* v_a_1939_){
_start:
{
size_t v_sz_1940_; size_t v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v_sz_1940_ = lean_array_size(v_a_1939_);
v___x_1941_ = ((size_t)0ULL);
v___x_1942_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(v_sz_1940_, v___x_1941_, v_a_1939_);
v___x_1943_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson(lean_object* v_x_1948_){
_start:
{
lean_object* v_uri_1949_; lean_object* v_version_x3f_1950_; lean_object* v_isIncremental_x3f_1951_; lean_object* v_diagnostics_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v_uri_1949_ = lean_ctor_get(v_x_1948_, 0);
lean_inc_ref(v_uri_1949_);
v_version_x3f_1950_ = lean_ctor_get(v_x_1948_, 1);
lean_inc(v_version_x3f_1950_);
v_isIncremental_x3f_1951_ = lean_ctor_get(v_x_1948_, 2);
lean_inc(v_isIncremental_x3f_1951_);
v_diagnostics_1952_ = lean_ctor_get(v_x_1948_, 3);
lean_inc_ref(v_diagnostics_1952_);
lean_dec_ref(v_x_1948_);
v___x_1953_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0));
v___x_1954_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1954_, 0, v_uri_1949_);
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = lean_box(0);
v___x_1957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1));
v___x_1959_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__0(v___x_1958_, v_version_x3f_1950_);
v___x_1960_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2));
v___x_1961_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(v___x_1960_, v_isIncremental_x3f_1951_);
lean_dec(v_isIncremental_x3f_1951_);
v___x_1962_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3));
v___x_1963_ = l_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2(v_diagnostics_1952_);
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
lean_ctor_set(v___x_1965_, 1, v___x_1956_);
v___x_1966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
lean_ctor_set(v___x_1966_, 1, v___x_1956_);
v___x_1967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1961_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1959_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1957_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2));
v___x_1971_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(v___x_1969_, v___x_1970_);
v___x_1972_ = l_Lean_Json_mkObj(v___x_1971_);
lean_dec(v___x_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(lean_object* v_x_1977_){
_start:
{
if (lean_obj_tag(v_x_1977_) == 0)
{
lean_object* v___x_1978_; 
v___x_1978_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0));
return v___x_1978_;
}
else
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_Json_getBool_x3f(v_x_1977_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1996_; 
v_a_1988_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1990_ = v___x_1979_;
v_isShared_1991_ = v_isSharedCheck_1996_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1979_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1996_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1992_, 0, v_a_1988_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1992_);
v___x_1994_ = v___x_1990_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1992_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___boxed(lean_object* v_x_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(v_x_1997_);
lean_dec(v_x_1997_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(lean_object* v_j_1999_, lean_object* v_k_2000_){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = l_Lean_Json_getObjValD(v_j_1999_, v_k_2000_);
v___x_2002_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(v___x_2001_);
lean_dec(v___x_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1___boxed(lean_object* v_j_2003_, lean_object* v_k_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_j_2003_, v_k_2004_);
lean_dec_ref(v_k_2004_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0(lean_object* v_x_2008_){
_start:
{
if (lean_obj_tag(v_x_2008_) == 0)
{
lean_object* v___x_2009_; 
v___x_2009_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0));
return v___x_2009_;
}
else
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_Json_getInt_x3f(v_x_2008_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2027_; 
v_a_2019_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2021_ = v___x_2010_;
v_isShared_2022_ = v_isSharedCheck_2027_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2010_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2027_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2023_, 0, v_a_2019_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2023_);
v___x_2025_ = v___x_2021_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(lean_object* v_j_2028_, lean_object* v_k_2029_){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = l_Lean_Json_getObjValD(v_j_2028_, v_k_2029_);
v___x_2031_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0(v___x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0___boxed(lean_object* v_j_2032_, lean_object* v_k_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(v_j_2032_, v_k_2033_);
lean_dec_ref(v_k_2033_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22(lean_object* v_x_2037_){
_start:
{
if (lean_obj_tag(v_x_2037_) == 0)
{
lean_object* v___x_2038_; 
v___x_2038_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0));
return v___x_2038_;
}
else
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2039_, 0, v_x_2037_);
v___x_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
return v___x_2040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(lean_object* v_j_2041_, lean_object* v_k_2042_){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = l_Lean_Json_getObjValD(v_j_2041_, v_k_2042_);
v___x_2044_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22(v___x_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14___boxed(lean_object* v_j_2045_, lean_object* v_k_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(v_j_2045_, v_k_2046_);
lean_dec_ref(v_k_2046_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(size_t v_sz_2050_, size_t v_i_2051_, lean_object* v_bs_2052_){
_start:
{
uint8_t v___x_2055_; 
v___x_2055_ = lean_usize_dec_lt(v_i_2051_, v_sz_2050_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2056_, 0, v_bs_2052_);
return v___x_2056_;
}
else
{
lean_object* v_v_2057_; lean_object* v___x_2058_; 
v_v_2057_ = lean_array_uget_borrowed(v_bs_2052_, v_i_2051_);
lean_inc(v_v_2057_);
v___x_2058_ = l_Lean_Json_getNat_x3f(v_v_2057_);
if (lean_obj_tag(v___x_2058_) == 1)
{
lean_object* v_a_2059_; lean_object* v___x_2060_; lean_object* v_bs_x27_2061_; uint8_t v_a_2063_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = lean_unsigned_to_nat(0u);
v_bs_x27_2061_ = lean_array_uset(v_bs_2052_, v_i_2051_, v___x_2060_);
v___x_2069_ = lean_unsigned_to_nat(1u);
v___x_2070_ = lean_nat_dec_eq(v_a_2059_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = lean_unsigned_to_nat(2u);
v___x_2072_ = lean_nat_dec_eq(v_a_2059_, v___x_2071_);
lean_dec(v_a_2059_);
if (v___x_2072_ == 0)
{
lean_dec_ref(v_bs_x27_2061_);
goto v___jp_2053_;
}
else
{
uint8_t v___x_2073_; 
v___x_2073_ = 1;
v_a_2063_ = v___x_2073_;
goto v___jp_2062_;
}
}
else
{
uint8_t v___x_2074_; 
lean_dec(v_a_2059_);
v___x_2074_ = 0;
v_a_2063_ = v___x_2074_;
goto v___jp_2062_;
}
v___jp_2062_:
{
size_t v___x_2064_; size_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2064_ = ((size_t)1ULL);
v___x_2065_ = lean_usize_add(v_i_2051_, v___x_2064_);
v___x_2066_ = lean_box(v_a_2063_);
v___x_2067_ = lean_array_uset(v_bs_x27_2061_, v_i_2051_, v___x_2066_);
v_i_2051_ = v___x_2065_;
v_bs_2052_ = v___x_2067_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_2058_);
lean_dec_ref(v_bs_2052_);
goto v___jp_2053_;
}
}
v___jp_2053_:
{
lean_object* v___x_2054_; 
v___x_2054_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___closed__0));
return v___x_2054_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___boxed(lean_object* v_sz_2075_, lean_object* v_i_2076_, lean_object* v_bs_2077_){
_start:
{
size_t v_sz_boxed_2078_; size_t v_i_boxed_2079_; lean_object* v_res_2080_; 
v_sz_boxed_2078_ = lean_unbox_usize(v_sz_2075_);
lean_dec(v_sz_2075_);
v_i_boxed_2079_ = lean_unbox_usize(v_i_2076_);
lean_dec(v_i_2076_);
v_res_2080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(v_sz_boxed_2078_, v_i_boxed_2079_, v_bs_2077_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21(lean_object* v_x_2082_){
_start:
{
if (lean_obj_tag(v_x_2082_) == 4)
{
lean_object* v_elems_2083_; size_t v_sz_2084_; size_t v___x_2085_; lean_object* v___x_2086_; 
v_elems_2083_ = lean_ctor_get(v_x_2082_, 0);
lean_inc_ref(v_elems_2083_);
lean_dec_ref_known(v_x_2082_, 1);
v_sz_2084_ = lean_array_size(v_elems_2083_);
v___x_2085_ = ((size_t)0ULL);
v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(v_sz_2084_, v___x_2085_, v_elems_2083_);
return v___x_2086_;
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2087_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0));
v___x_2088_ = lean_unsigned_to_nat(80u);
v___x_2089_ = l_Lean_Json_pretty(v_x_2082_, v___x_2088_);
v___x_2090_ = lean_string_append(v___x_2087_, v___x_2089_);
lean_dec_ref(v___x_2089_);
v___x_2091_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2092_ = lean_string_append(v___x_2090_, v___x_2091_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
return v___x_2093_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18(lean_object* v_x_2096_){
_start:
{
if (lean_obj_tag(v_x_2096_) == 0)
{
lean_object* v___x_2097_; 
v___x_2097_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0));
return v___x_2097_;
}
else
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21(v_x_2096_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2115_; 
v_a_2107_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2109_ = v___x_2098_;
v_isShared_2110_ = v_isSharedCheck_2115_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2098_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2115_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2111_, 0, v_a_2107_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2111_);
v___x_2113_ = v___x_2109_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(lean_object* v_j_2116_, lean_object* v_k_2117_){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = l_Lean_Json_getObjValD(v_j_2116_, v_k_2117_);
v___x_2119_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18(v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12___boxed(lean_object* v_j_2120_, lean_object* v_k_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(v_j_2120_, v_k_2121_);
lean_dec_ref(v_k_2121_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12(lean_object* v_x_2125_){
_start:
{
lean_object* v_a_2127_; lean_object* v_j_2131_; 
if (lean_obj_tag(v_x_2125_) == 0)
{
lean_object* v___x_2139_; 
v___x_2139_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0));
return v___x_2139_;
}
else
{
switch(lean_obj_tag(v_x_2125_))
{
case 2:
{
lean_object* v_n_2140_; lean_object* v_mantissa_2141_; lean_object* v_exponent_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v_n_2140_ = lean_ctor_get(v_x_2125_, 0);
v_mantissa_2141_ = lean_ctor_get(v_n_2140_, 0);
v_exponent_2142_ = lean_ctor_get(v_n_2140_, 1);
v___x_2143_ = lean_unsigned_to_nat(0u);
v___x_2144_ = lean_nat_dec_eq(v_exponent_2142_, v___x_2143_);
if (v___x_2144_ == 0)
{
v_j_2131_ = v_x_2125_;
goto v___jp_2130_;
}
else
{
lean_object* v___x_2145_; 
lean_inc(v_mantissa_2141_);
lean_dec_ref_known(v_x_2125_, 1);
v___x_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2145_, 0, v_mantissa_2141_);
v_a_2127_ = v___x_2145_;
goto v___jp_2126_;
}
}
case 3:
{
lean_object* v_s_2146_; lean_object* v___x_2147_; 
v_s_2146_ = lean_ctor_get(v_x_2125_, 0);
lean_inc_ref(v_s_2146_);
lean_dec_ref_known(v_x_2125_, 1);
v___x_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2147_, 0, v_s_2146_);
v_a_2127_ = v___x_2147_;
goto v___jp_2126_;
}
default: 
{
v_j_2131_ = v_x_2125_;
goto v___jp_2130_;
}
}
}
v___jp_2126_:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2128_, 0, v_a_2127_);
v___x_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
return v___x_2129_;
}
v___jp_2130_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2132_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0));
v___x_2133_ = lean_unsigned_to_nat(80u);
v___x_2134_ = l_Lean_Json_pretty(v_j_2131_, v___x_2133_);
v___x_2135_ = lean_string_append(v___x_2132_, v___x_2134_);
lean_dec_ref(v___x_2134_);
v___x_2136_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2137_ = lean_string_append(v___x_2135_, v___x_2136_);
v___x_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
return v___x_2138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(lean_object* v_j_2148_, lean_object* v_k_2149_){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = l_Lean_Json_getObjValD(v_j_2148_, v_k_2149_);
v___x_2151_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12(v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9___boxed(lean_object* v_j_2152_, lean_object* v_k_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(v_j_2152_, v_k_2153_);
lean_dec_ref(v_k_2153_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(lean_object* v_j_2155_, lean_object* v_k_2156_){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = l_Lean_Json_getObjValD(v_j_2155_, v_k_2156_);
v___x_2158_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_j_2159_, lean_object* v_k_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(v_j_2159_, v_k_2160_);
lean_dec_ref(v_k_2160_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(size_t v_sz_2164_, size_t v_i_2165_, lean_object* v_bs_2166_){
_start:
{
uint8_t v___x_2169_; 
v___x_2169_ = lean_usize_dec_lt(v_i_2165_, v_sz_2164_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; 
v___x_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2170_, 0, v_bs_2166_);
return v___x_2170_;
}
else
{
lean_object* v_v_2171_; lean_object* v___x_2172_; 
v_v_2171_ = lean_array_uget_borrowed(v_bs_2166_, v_i_2165_);
lean_inc(v_v_2171_);
v___x_2172_ = l_Lean_Json_getNat_x3f(v_v_2171_);
if (lean_obj_tag(v___x_2172_) == 1)
{
lean_object* v_a_2173_; lean_object* v___x_2174_; lean_object* v_bs_x27_2175_; uint8_t v_a_2177_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2172_, 1);
v___x_2174_ = lean_unsigned_to_nat(0u);
v_bs_x27_2175_ = lean_array_uset(v_bs_2166_, v_i_2165_, v___x_2174_);
v___x_2183_ = lean_unsigned_to_nat(1u);
v___x_2184_ = lean_nat_dec_eq(v_a_2173_, v___x_2183_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; uint8_t v___x_2186_; 
v___x_2185_ = lean_unsigned_to_nat(2u);
v___x_2186_ = lean_nat_dec_eq(v_a_2173_, v___x_2185_);
lean_dec(v_a_2173_);
if (v___x_2186_ == 0)
{
lean_dec_ref(v_bs_x27_2175_);
goto v___jp_2167_;
}
else
{
uint8_t v___x_2187_; 
v___x_2187_ = 1;
v_a_2177_ = v___x_2187_;
goto v___jp_2176_;
}
}
else
{
uint8_t v___x_2188_; 
lean_dec(v_a_2173_);
v___x_2188_ = 0;
v_a_2177_ = v___x_2188_;
goto v___jp_2176_;
}
v___jp_2176_:
{
size_t v___x_2178_; size_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2178_ = ((size_t)1ULL);
v___x_2179_ = lean_usize_add(v_i_2165_, v___x_2178_);
v___x_2180_ = lean_box(v_a_2177_);
v___x_2181_ = lean_array_uset(v_bs_x27_2175_, v_i_2165_, v___x_2180_);
v_i_2165_ = v___x_2179_;
v_bs_2166_ = v___x_2181_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_2172_);
lean_dec_ref(v_bs_2166_);
goto v___jp_2167_;
}
}
v___jp_2167_:
{
lean_object* v___x_2168_; 
v___x_2168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___closed__0));
return v___x_2168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___boxed(lean_object* v_sz_2189_, lean_object* v_i_2190_, lean_object* v_bs_2191_){
_start:
{
size_t v_sz_boxed_2192_; size_t v_i_boxed_2193_; lean_object* v_res_2194_; 
v_sz_boxed_2192_ = lean_unbox_usize(v_sz_2189_);
lean_dec(v_sz_2189_);
v_i_boxed_2193_ = lean_unbox_usize(v_i_2190_);
lean_dec(v_i_2190_);
v_res_2194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(v_sz_boxed_2192_, v_i_boxed_2193_, v_bs_2191_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18(lean_object* v_x_2195_){
_start:
{
if (lean_obj_tag(v_x_2195_) == 4)
{
lean_object* v_elems_2196_; size_t v_sz_2197_; size_t v___x_2198_; lean_object* v___x_2199_; 
v_elems_2196_ = lean_ctor_get(v_x_2195_, 0);
lean_inc_ref(v_elems_2196_);
lean_dec_ref_known(v_x_2195_, 1);
v_sz_2197_ = lean_array_size(v_elems_2196_);
v___x_2198_ = ((size_t)0ULL);
v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(v_sz_2197_, v___x_2198_, v_elems_2196_);
return v___x_2199_;
}
else
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2200_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0));
v___x_2201_ = lean_unsigned_to_nat(80u);
v___x_2202_ = l_Lean_Json_pretty(v_x_2195_, v___x_2201_);
v___x_2203_ = lean_string_append(v___x_2200_, v___x_2202_);
lean_dec_ref(v___x_2202_);
v___x_2204_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2205_ = lean_string_append(v___x_2203_, v___x_2204_);
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
return v___x_2206_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16(lean_object* v_x_2209_){
_start:
{
if (lean_obj_tag(v_x_2209_) == 0)
{
lean_object* v___x_2210_; 
v___x_2210_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0));
return v___x_2210_;
}
else
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18(v_x_2209_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2228_; 
v_a_2220_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2222_ = v___x_2211_;
v_isShared_2223_ = v_isSharedCheck_2228_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2211_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2228_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2224_, 0, v_a_2220_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v___x_2224_);
v___x_2226_ = v___x_2222_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(lean_object* v_j_2229_, lean_object* v_k_2230_){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = l_Lean_Json_getObjValD(v_j_2229_, v_k_2230_);
v___x_2232_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16(v___x_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11___boxed(lean_object* v_j_2233_, lean_object* v_k_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(v_j_2233_, v_k_2234_);
lean_dec_ref(v_k_2234_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10(lean_object* v_x_2238_){
_start:
{
uint8_t v_a_2248_; 
if (lean_obj_tag(v_x_2238_) == 0)
{
lean_object* v___x_2252_; 
v___x_2252_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0));
return v___x_2252_;
}
else
{
lean_object* v___x_2253_; 
lean_inc(v_x_2238_);
v___x_2253_ = l_Lean_Json_getNat_x3f(v_x_2238_);
if (lean_obj_tag(v___x_2253_) == 1)
{
lean_object* v_a_2254_; lean_object* v___x_2255_; uint8_t v___x_2256_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref_known(v___x_2253_, 1);
v___x_2255_ = lean_unsigned_to_nat(1u);
v___x_2256_ = lean_nat_dec_eq(v_a_2254_, v___x_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; uint8_t v___x_2258_; 
v___x_2257_ = lean_unsigned_to_nat(2u);
v___x_2258_ = lean_nat_dec_eq(v_a_2254_, v___x_2257_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; uint8_t v___x_2260_; 
v___x_2259_ = lean_unsigned_to_nat(3u);
v___x_2260_ = lean_nat_dec_eq(v_a_2254_, v___x_2259_);
if (v___x_2260_ == 0)
{
lean_object* v___x_2261_; uint8_t v___x_2262_; 
v___x_2261_ = lean_unsigned_to_nat(4u);
v___x_2262_ = lean_nat_dec_eq(v_a_2254_, v___x_2261_);
lean_dec(v_a_2254_);
if (v___x_2262_ == 0)
{
goto v___jp_2239_;
}
else
{
uint8_t v___x_2263_; 
lean_dec(v_x_2238_);
v___x_2263_ = 3;
v_a_2248_ = v___x_2263_;
goto v___jp_2247_;
}
}
else
{
uint8_t v___x_2264_; 
lean_dec(v_a_2254_);
lean_dec(v_x_2238_);
v___x_2264_ = 2;
v_a_2248_ = v___x_2264_;
goto v___jp_2247_;
}
}
else
{
uint8_t v___x_2265_; 
lean_dec(v_a_2254_);
lean_dec(v_x_2238_);
v___x_2265_ = 1;
v_a_2248_ = v___x_2265_;
goto v___jp_2247_;
}
}
else
{
uint8_t v___x_2266_; 
lean_dec(v_a_2254_);
lean_dec(v_x_2238_);
v___x_2266_ = 0;
v_a_2248_ = v___x_2266_;
goto v___jp_2247_;
}
}
else
{
lean_dec_ref(v___x_2253_);
goto v___jp_2239_;
}
}
v___jp_2239_:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2240_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0));
v___x_2241_ = lean_unsigned_to_nat(80u);
v___x_2242_ = l_Lean_Json_pretty(v_x_2238_, v___x_2241_);
v___x_2243_ = lean_string_append(v___x_2240_, v___x_2242_);
lean_dec_ref(v___x_2242_);
v___x_2244_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2245_ = lean_string_append(v___x_2243_, v___x_2244_);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
return v___x_2246_;
}
v___jp_2247_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = lean_box(v_a_2248_);
v___x_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
v___x_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
return v___x_2251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(lean_object* v_j_2267_, lean_object* v_k_2268_){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = l_Lean_Json_getObjValD(v_j_2267_, v_k_2268_);
v___x_2270_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10(v___x_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8___boxed(lean_object* v_j_2271_, lean_object* v_k_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(v_j_2271_, v_k_2272_);
lean_dec_ref(v_k_2272_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8(lean_object* v_x_2276_){
_start:
{
if (lean_obj_tag(v_x_2276_) == 0)
{
lean_object* v___x_2277_; 
v___x_2277_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0));
return v___x_2277_;
}
else
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_2276_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2295_; 
v_a_2287_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2289_ = v___x_2278_;
v_isShared_2290_ = v_isSharedCheck_2295_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2278_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2295_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2291_, 0, v_a_2287_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v___x_2291_);
v___x_2293_ = v___x_2289_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2291_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(lean_object* v_j_2296_, lean_object* v_k_2297_){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = l_Lean_Json_getObjValD(v_j_2296_, v_k_2297_);
v___x_2299_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8(v___x_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_j_2300_, lean_object* v_k_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(v_j_2300_, v_k_2301_);
lean_dec_ref(v_k_2301_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(size_t v_sz_2303_, size_t v_i_2304_, lean_object* v_bs_2305_){
_start:
{
uint8_t v___x_2306_; 
v___x_2306_ = lean_usize_dec_lt(v_i_2304_, v_sz_2303_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; 
v___x_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2307_, 0, v_bs_2305_);
return v___x_2307_;
}
else
{
lean_object* v_v_2308_; lean_object* v___x_2309_; 
v_v_2308_ = lean_array_uget_borrowed(v_bs_2305_, v_i_2304_);
lean_inc(v_v_2308_);
v___x_2309_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(v_v_2308_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v_bs_2305_);
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2319_; lean_object* v_bs_x27_2320_; size_t v___x_2321_; size_t v___x_2322_; lean_object* v___x_2323_; 
v_a_2318_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2309_, 1);
v___x_2319_ = lean_unsigned_to_nat(0u);
v_bs_x27_2320_ = lean_array_uset(v_bs_2305_, v_i_2304_, v___x_2319_);
v___x_2321_ = ((size_t)1ULL);
v___x_2322_ = lean_usize_add(v_i_2304_, v___x_2321_);
v___x_2323_ = lean_array_uset(v_bs_x27_2320_, v_i_2304_, v_a_2318_);
v_i_2304_ = v___x_2322_;
v_bs_2305_ = v___x_2323_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29___boxed(lean_object* v_sz_2325_, lean_object* v_i_2326_, lean_object* v_bs_2327_){
_start:
{
size_t v_sz_boxed_2328_; size_t v_i_boxed_2329_; lean_object* v_res_2330_; 
v_sz_boxed_2328_ = lean_unbox_usize(v_sz_2325_);
lean_dec(v_sz_2325_);
v_i_boxed_2329_ = lean_unbox_usize(v_i_2326_);
lean_dec(v_i_2326_);
v_res_2330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(v_sz_boxed_2328_, v_i_boxed_2329_, v_bs_2327_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24(lean_object* v_x_2331_){
_start:
{
if (lean_obj_tag(v_x_2331_) == 4)
{
lean_object* v_elems_2332_; size_t v_sz_2333_; size_t v___x_2334_; lean_object* v___x_2335_; 
v_elems_2332_ = lean_ctor_get(v_x_2331_, 0);
lean_inc_ref(v_elems_2332_);
lean_dec_ref_known(v_x_2331_, 1);
v_sz_2333_ = lean_array_size(v_elems_2332_);
v___x_2334_ = ((size_t)0ULL);
v___x_2335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(v_sz_2333_, v___x_2334_, v_elems_2332_);
return v___x_2335_;
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2336_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0));
v___x_2337_ = lean_unsigned_to_nat(80u);
v___x_2338_ = l_Lean_Json_pretty(v_x_2331_, v___x_2337_);
v___x_2339_ = lean_string_append(v___x_2336_, v___x_2338_);
lean_dec_ref(v___x_2338_);
v___x_2340_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2341_ = lean_string_append(v___x_2339_, v___x_2340_);
v___x_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
return v___x_2342_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20(lean_object* v_x_2345_){
_start:
{
if (lean_obj_tag(v_x_2345_) == 0)
{
lean_object* v___x_2346_; 
v___x_2346_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0));
return v___x_2346_;
}
else
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24(v_x_2345_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2364_; 
v_a_2356_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2358_ = v___x_2347_;
v_isShared_2359_ = v_isSharedCheck_2364_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2347_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2364_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2360_; lean_object* v___x_2362_; 
v___x_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2360_, 0, v_a_2356_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v___x_2360_);
v___x_2362_ = v___x_2358_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(lean_object* v_j_2365_, lean_object* v_k_2366_){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = l_Lean_Json_getObjValD(v_j_2365_, v_k_2366_);
v___x_2368_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20(v___x_2367_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13___boxed(lean_object* v_j_2369_, lean_object* v_k_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(v_j_2369_, v_k_2370_);
lean_dec_ref(v_k_2370_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14(lean_object* v_x_2374_){
_start:
{
if (lean_obj_tag(v_x_2374_) == 0)
{
lean_object* v___x_2375_; 
v___x_2375_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0));
return v___x_2375_;
}
else
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Lean_Json_getStr_x3f(v_x_2374_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2393_; 
v_a_2385_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2387_ = v___x_2376_;
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2376_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2393_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2389_, 0, v_a_2385_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v___x_2389_);
v___x_2391_ = v___x_2387_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(lean_object* v_j_2394_, lean_object* v_k_2395_){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = l_Lean_Json_getObjValD(v_j_2394_, v_k_2395_);
v___x_2397_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14(v___x_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10___boxed(lean_object* v_j_2398_, lean_object* v_k_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(v_j_2398_, v_k_2399_);
lean_dec_ref(v_k_2399_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5(lean_object* v_json_2401_){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
lean_inc(v_json_2401_);
v___x_2403_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(v_json_2401_, v___x_2402_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2413_; 
lean_dec(v_json_2401_);
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2406_ = v___x_2403_;
v_isShared_2407_ = v_isSharedCheck_2413_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2403_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2413_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2411_; 
v___x_2408_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9);
v___x_2409_ = lean_string_append(v___x_2408_, v_a_2404_);
lean_dec(v_a_2404_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v___x_2409_);
v___x_2411_ = v___x_2406_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
else
{
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec(v_json_2401_);
v_a_2414_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2403_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2403_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
lean_ctor_set_tag(v___x_2416_, 0);
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v_a_2422_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2422_);
lean_dec_ref_known(v___x_2403_, 1);
v___x_2423_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
lean_inc(v_json_2401_);
v___x_2424_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(v_json_2401_, v___x_2423_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2434_; 
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2434_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2434_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2429_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14);
v___x_2430_ = lean_string_append(v___x_2429_, v_a_2425_);
lean_dec(v_a_2425_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2430_);
v___x_2432_ = v___x_2427_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
else
{
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2435_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2424_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2424_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
lean_ctor_set_tag(v___x_2437_, 0);
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v_a_2443_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2443_);
lean_dec_ref_known(v___x_2424_, 1);
v___x_2444_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
lean_inc(v_json_2401_);
v___x_2445_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(v_json_2401_, v___x_2444_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2455_; 
lean_dec(v_a_2443_);
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2448_ = v___x_2445_;
v_isShared_2449_ = v_isSharedCheck_2455_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2455_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2453_; 
v___x_2450_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20);
v___x_2451_ = lean_string_append(v___x_2450_, v_a_2446_);
lean_dec(v_a_2446_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2451_);
v___x_2453_ = v___x_2448_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
else
{
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec(v_a_2443_);
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2456_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2445_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2445_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
lean_ctor_set_tag(v___x_2458_, 0);
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v_a_2464_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___x_2445_, 1);
v___x_2465_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
lean_inc(v_json_2401_);
v___x_2466_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_json_2401_, v___x_2465_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2476_; 
lean_dec(v_a_2464_);
lean_dec(v_a_2443_);
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2476_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2476_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
v___x_2471_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27);
v___x_2472_ = lean_string_append(v___x_2471_, v_a_2467_);
lean_dec(v_a_2467_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 0, v___x_2472_);
v___x_2474_ = v___x_2469_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
else
{
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec(v_a_2464_);
lean_dec(v_a_2443_);
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2477_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2466_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2466_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
lean_ctor_set_tag(v___x_2479_, 0);
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v_a_2485_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2485_);
lean_dec_ref_known(v___x_2466_, 1);
v___x_2486_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
lean_inc(v_json_2401_);
v___x_2487_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(v_json_2401_, v___x_2486_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2497_; 
lean_dec(v_a_2485_);
lean_dec(v_a_2464_);
lean_dec(v_a_2443_);
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2490_ = v___x_2487_;
v_isShared_2491_ = v_isSharedCheck_2497_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2487_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2497_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2495_; 
v___x_2492_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33);
v___x_2493_ = lean_string_append(v___x_2492_, v_a_2488_);
lean_dec(v_a_2488_);
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 0, v___x_2493_);
v___x_2495_ = v___x_2490_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2493_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
else
{
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_dec(v_a_2485_);
lean_dec(v_a_2464_);
lean_dec(v_a_2443_);
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2498_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2487_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2487_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
lean_ctor_set_tag(v___x_2500_, 0);
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v_a_2506_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2487_, 1);
v___x_2507_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
lean_inc(v_json_2401_);
v___x_2508_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(v_json_2401_, v___x_2507_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2518_; 
lean_dec(v_a_2506_);
lean_dec(v_a_2485_);
lean_dec(v_a_2464_);
lean_dec(v_a_2443_);
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2518_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2518_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2516_; 
v___x_2513_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40);
v___x_2514_ = lean_string_append(v___x_2513_, v_a_2509_);
lean_dec(v_a_2509_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v___x_2514_);
v___x_2516_ = v___x_2511_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
else
{
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
lean_dec(v_a_2506_);
lean_dec(v_a_2485_);
lean_dec(v_a_2464_);
lean_dec(v_a_2443_);
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2519_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2508_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2508_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
lean_ctor_set_tag(v___x_2521_, 0);
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v_a_2527_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v___x_2508_, 1);
v___x_2528_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
lean_inc(v_json_2401_);
v___x_2529_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_2401_, v___x_2528_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2539_; 
lean_dec(v_a_2527_);
lean_dec(v_a_2506_);
lean_dec(v_a_2485_);
lean_dec(v_a_2464_);
lean_dec(v_a_2443_);
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2532_ = v___x_2529_;
v_isShared_2533_ = v_isSharedCheck_2539_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2539_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2534_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42);
v___x_2535_ = lean_string_append(v___x_2534_, v_a_2530_);
lean_dec(v_a_2530_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2535_);
v___x_2537_ = v___x_2532_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2535_);
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
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_dec(v_a_2527_);
lean_dec(v_a_2506_);
lean_dec(v_a_2485_);
lean_dec(v_a_2464_);
lean_dec(v_a_2443_);
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2540_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2529_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2529_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
lean_ctor_set_tag(v___x_2542_, 0);
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v_a_2548_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2548_);
lean_dec_ref_known(v___x_2529_, 1);
v___x_2549_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
lean_inc(v_json_2401_);
v___x_2550_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(v_json_2401_, v___x_2549_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2560_; 
lean_dec(v_a_2548_);
lean_dec(v_a_2527_);
lean_dec(v_a_2506_);
lean_dec(v_a_2485_);
lean_dec(v_a_2464_);
lean_dec(v_a_2443_);
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2553_ = v___x_2550_;
v_isShared_2554_ = v_isSharedCheck_2560_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2550_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2560_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2558_; 
v___x_2555_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49);
v___x_2556_ = lean_string_append(v___x_2555_, v_a_2551_);
lean_dec(v_a_2551_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 0, v___x_2556_);
v___x_2558_ = v___x_2553_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2556_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
else
{
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v_a_2548_);
lean_dec(v_a_2527_);
lean_dec(v_a_2506_);
lean_dec(v_a_2485_);
lean_dec(v_a_2464_);
lean_dec(v_a_2443_);
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2561_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2550_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2550_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
lean_ctor_set_tag(v___x_2563_, 0);
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v_a_2569_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2569_);
lean_dec_ref_known(v___x_2550_, 1);
v___x_2570_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
lean_inc(v_json_2401_);
v___x_2571_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(v_json_2401_, v___x_2570_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2581_; 
lean_dec(v_a_2569_);
lean_dec(v_a_2548_);
lean_dec(v_a_2527_);
lean_dec(v_a_2506_);
lean_dec(v_a_2485_);
lean_dec(v_a_2464_);
lean_dec(v_a_2443_);
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2581_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2581_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2576_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56);
v___x_2577_ = lean_string_append(v___x_2576_, v_a_2572_);
lean_dec(v_a_2572_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v___x_2577_);
v___x_2579_ = v___x_2574_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
else
{
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_dec(v_a_2569_);
lean_dec(v_a_2548_);
lean_dec(v_a_2527_);
lean_dec(v_a_2506_);
lean_dec(v_a_2485_);
lean_dec(v_a_2464_);
lean_dec(v_a_2443_);
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2582_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2571_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2571_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set_tag(v___x_2584_, 0);
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_a_2590_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v___x_2571_, 1);
v___x_2591_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
lean_inc(v_json_2401_);
v___x_2592_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(v_json_2401_, v___x_2591_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2602_; 
lean_dec(v_a_2590_);
lean_dec(v_a_2569_);
lean_dec(v_a_2548_);
lean_dec(v_a_2527_);
lean_dec(v_a_2506_);
lean_dec(v_a_2485_);
lean_dec(v_a_2464_);
lean_dec(v_a_2443_);
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2602_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2602_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2597_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63);
v___x_2598_ = lean_string_append(v___x_2597_, v_a_2593_);
lean_dec(v_a_2593_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2598_);
v___x_2600_ = v___x_2595_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
else
{
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_dec(v_a_2590_);
lean_dec(v_a_2569_);
lean_dec(v_a_2548_);
lean_dec(v_a_2527_);
lean_dec(v_a_2506_);
lean_dec(v_a_2485_);
lean_dec(v_a_2464_);
lean_dec(v_a_2443_);
lean_dec(v_a_2422_);
lean_dec(v_json_2401_);
v_a_2603_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2592_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2592_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
lean_ctor_set_tag(v___x_2605_, 0);
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2622_; 
v_a_2611_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2592_, 1);
v___x_2612_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
v___x_2613_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(v_json_2401_, v___x_2612_);
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2622_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2622_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; lean_object* v___x_2620_; 
v___x_2618_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2618_, 0, v_a_2422_);
lean_ctor_set(v___x_2618_, 1, v_a_2443_);
lean_ctor_set(v___x_2618_, 2, v_a_2464_);
lean_ctor_set(v___x_2618_, 3, v_a_2485_);
lean_ctor_set(v___x_2618_, 4, v_a_2506_);
lean_ctor_set(v___x_2618_, 5, v_a_2527_);
lean_ctor_set(v___x_2618_, 6, v_a_2548_);
lean_ctor_set(v___x_2618_, 7, v_a_2569_);
lean_ctor_set(v___x_2618_, 8, v_a_2590_);
lean_ctor_set(v___x_2618_, 9, v_a_2611_);
lean_ctor_set(v___x_2618_, 10, v_a_2614_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2618_);
v___x_2620_ = v___x_2616_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(size_t v_sz_2623_, size_t v_i_2624_, lean_object* v_bs_2625_){
_start:
{
uint8_t v___x_2626_; 
v___x_2626_ = lean_usize_dec_lt(v_i_2624_, v_sz_2623_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; 
v___x_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2627_, 0, v_bs_2625_);
return v___x_2627_;
}
else
{
lean_object* v_v_2628_; lean_object* v___x_2629_; 
v_v_2628_ = lean_array_uget_borrowed(v_bs_2625_, v_i_2624_);
lean_inc(v_v_2628_);
v___x_2629_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5(v_v_2628_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec_ref(v_bs_2625_);
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2629_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2629_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2639_; lean_object* v_bs_x27_2640_; size_t v___x_2641_; size_t v___x_2642_; lean_object* v___x_2643_; 
v_a_2638_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___x_2629_, 1);
v___x_2639_ = lean_unsigned_to_nat(0u);
v_bs_x27_2640_ = lean_array_uset(v_bs_2625_, v_i_2624_, v___x_2639_);
v___x_2641_ = ((size_t)1ULL);
v___x_2642_ = lean_usize_add(v_i_2624_, v___x_2641_);
v___x_2643_ = lean_array_uset(v_bs_x27_2640_, v_i_2624_, v_a_2638_);
v_i_2624_ = v___x_2642_;
v_bs_2625_ = v___x_2643_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2645_, lean_object* v_i_2646_, lean_object* v_bs_2647_){
_start:
{
size_t v_sz_boxed_2648_; size_t v_i_boxed_2649_; lean_object* v_res_2650_; 
v_sz_boxed_2648_ = lean_unbox_usize(v_sz_2645_);
lean_dec(v_sz_2645_);
v_i_boxed_2649_ = lean_unbox_usize(v_i_2646_);
lean_dec(v_i_2646_);
v_res_2650_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(v_sz_boxed_2648_, v_i_boxed_2649_, v_bs_2647_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4(lean_object* v_x_2651_){
_start:
{
if (lean_obj_tag(v_x_2651_) == 4)
{
lean_object* v_elems_2652_; size_t v_sz_2653_; size_t v___x_2654_; lean_object* v___x_2655_; 
v_elems_2652_ = lean_ctor_get(v_x_2651_, 0);
lean_inc_ref(v_elems_2652_);
lean_dec_ref_known(v_x_2651_, 1);
v_sz_2653_ = lean_array_size(v_elems_2652_);
v___x_2654_ = ((size_t)0ULL);
v___x_2655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(v_sz_2653_, v___x_2654_, v_elems_2652_);
return v___x_2655_;
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2656_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0));
v___x_2657_ = lean_unsigned_to_nat(80u);
v___x_2658_ = l_Lean_Json_pretty(v_x_2651_, v___x_2657_);
v___x_2659_ = lean_string_append(v___x_2656_, v___x_2658_);
lean_dec_ref(v___x_2658_);
v___x_2660_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2661_ = lean_string_append(v___x_2659_, v___x_2660_);
v___x_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
return v___x_2662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(lean_object* v_j_2663_, lean_object* v_k_2664_){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = l_Lean_Json_getObjValD(v_j_2663_, v_k_2664_);
v___x_2666_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4(v___x_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2___boxed(lean_object* v_j_2667_, lean_object* v_k_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(v_j_2667_, v_k_2668_);
lean_dec_ref(v_k_2668_);
return v_res_2669_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2675_ = 1;
v___x_2676_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1));
v___x_2677_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2676_, v___x_2675_);
return v___x_2677_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2678_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5));
v___x_2679_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2);
v___x_2680_ = lean_string_append(v___x_2679_, v___x_2678_);
return v___x_2680_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = 1;
v___x_2684_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4));
v___x_2685_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2684_, v___x_2683_);
return v___x_2685_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2686_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5);
v___x_2687_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
v___x_2688_ = lean_string_append(v___x_2687_, v___x_2686_);
return v___x_2688_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2689_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_2690_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6);
v___x_2691_ = lean_string_append(v___x_2690_, v___x_2689_);
return v___x_2691_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10(void){
_start:
{
uint8_t v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2695_ = 1;
v___x_2696_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9));
v___x_2697_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2696_, v___x_2695_);
return v___x_2697_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2698_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10);
v___x_2699_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
v___x_2700_ = lean_string_append(v___x_2699_, v___x_2698_);
return v___x_2700_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_2702_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11);
v___x_2703_ = lean_string_append(v___x_2702_, v___x_2701_);
return v___x_2703_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15(void){
_start:
{
uint8_t v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2707_ = 1;
v___x_2708_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14));
v___x_2709_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2708_, v___x_2707_);
return v___x_2709_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2710_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15);
v___x_2711_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
v___x_2712_ = lean_string_append(v___x_2711_, v___x_2710_);
return v___x_2712_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2713_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_2714_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16);
v___x_2715_ = lean_string_append(v___x_2714_, v___x_2713_);
return v___x_2715_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19(void){
_start:
{
uint8_t v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = 1;
v___x_2719_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18));
v___x_2720_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2719_, v___x_2718_);
return v___x_2720_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20(void){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2721_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19);
v___x_2722_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
v___x_2723_ = lean_string_append(v___x_2722_, v___x_2721_);
return v___x_2723_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21(void){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2724_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_2725_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20);
v___x_2726_ = lean_string_append(v___x_2725_, v___x_2724_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(lean_object* v_json_2727_){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0));
lean_inc(v_json_2727_);
v___x_2729_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_2727_, v___x_2728_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2739_; 
lean_dec(v_json_2727_);
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2732_ = v___x_2729_;
v_isShared_2733_ = v_isSharedCheck_2739_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2729_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2739_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2737_; 
v___x_2734_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7);
v___x_2735_ = lean_string_append(v___x_2734_, v_a_2730_);
lean_dec(v_a_2730_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2735_);
v___x_2737_ = v___x_2732_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
else
{
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec(v_json_2727_);
v_a_2740_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2729_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2729_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
lean_ctor_set_tag(v___x_2742_, 0);
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v_a_2748_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2748_);
lean_dec_ref_known(v___x_2729_, 1);
v___x_2749_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1));
lean_inc(v_json_2727_);
v___x_2750_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(v_json_2727_, v___x_2749_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2760_; 
lean_dec(v_a_2748_);
lean_dec(v_json_2727_);
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2760_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2760_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2755_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12);
v___x_2756_ = lean_string_append(v___x_2755_, v_a_2751_);
lean_dec(v_a_2751_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2756_);
v___x_2758_ = v___x_2753_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
else
{
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec(v_a_2748_);
lean_dec(v_json_2727_);
v_a_2761_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2750_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2750_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
lean_ctor_set_tag(v___x_2763_, 0);
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v_a_2769_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2769_);
lean_dec_ref_known(v___x_2750_, 1);
v___x_2770_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2));
lean_inc(v_json_2727_);
v___x_2771_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_json_2727_, v___x_2770_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2781_; 
lean_dec(v_a_2769_);
lean_dec(v_a_2748_);
lean_dec(v_json_2727_);
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2781_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2781_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2779_; 
v___x_2776_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17);
v___x_2777_ = lean_string_append(v___x_2776_, v_a_2772_);
lean_dec(v_a_2772_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2777_);
v___x_2779_ = v___x_2774_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
else
{
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec(v_a_2769_);
lean_dec(v_a_2748_);
lean_dec(v_json_2727_);
v_a_2782_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2771_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2771_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
lean_ctor_set_tag(v___x_2784_, 0);
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v_a_2790_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2771_, 1);
v___x_2791_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3));
v___x_2792_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(v_json_2727_, v___x_2791_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2802_; 
lean_dec(v_a_2790_);
lean_dec(v_a_2769_);
lean_dec(v_a_2748_);
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2795_ = v___x_2792_;
v_isShared_2796_ = v_isSharedCheck_2802_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2792_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2802_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2800_; 
v___x_2797_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21);
v___x_2798_ = lean_string_append(v___x_2797_, v_a_2793_);
lean_dec(v_a_2793_);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 0, v___x_2798_);
v___x_2800_ = v___x_2795_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2798_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
else
{
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec(v_a_2790_);
lean_dec(v_a_2769_);
lean_dec(v_a_2748_);
v_a_2803_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2792_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2792_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
lean_ctor_set_tag(v___x_2805_, 0);
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2819_; 
v_a_2811_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2813_ = v___x_2792_;
v_isShared_2814_ = v_isSharedCheck_2819_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2792_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2819_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2815_; lean_object* v___x_2817_; 
v___x_2815_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2815_, 0, v_a_2748_);
lean_ctor_set(v___x_2815_, 1, v_a_2769_);
lean_ctor_set(v___x_2815_, 2, v_a_2790_);
lean_ctor_set(v___x_2815_, 3, v_a_2811_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_2815_);
v___x_2817_ = v___x_2813_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2815_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
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
}
lean_object* runtime_initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Utf16(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Lsp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Utf16(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_instInhabitedDiagnosticSeverity_default = _init_l_Lean_Lsp_instInhabitedDiagnosticSeverity_default();
l_Lean_Lsp_instInhabitedDiagnosticSeverity = _init_l_Lean_Lsp_instInhabitedDiagnosticSeverity();
l_Lean_Lsp_instInhabitedDiagnosticCode_default = _init_l_Lean_Lsp_instInhabitedDiagnosticCode_default();
lean_mark_persistent(l_Lean_Lsp_instInhabitedDiagnosticCode_default);
l_Lean_Lsp_instInhabitedDiagnosticCode = _init_l_Lean_Lsp_instInhabitedDiagnosticCode();
lean_mark_persistent(l_Lean_Lsp_instInhabitedDiagnosticCode);
l_Lean_Lsp_instInhabitedDiagnosticTag_default = _init_l_Lean_Lsp_instInhabitedDiagnosticTag_default();
l_Lean_Lsp_instInhabitedDiagnosticTag = _init_l_Lean_Lsp_instInhabitedDiagnosticTag();
l_Lean_Lsp_instInhabitedLeanDiagnosticTag_default = _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag_default();
l_Lean_Lsp_instInhabitedLeanDiagnosticTag = _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag();
l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default = _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default();
lean_mark_persistent(l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default);
l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation = _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation();
lean_mark_persistent(l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Utf16(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Utf16(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_Diagnostics(builtin);
}
#ifdef __cplusplus
}
#endif
