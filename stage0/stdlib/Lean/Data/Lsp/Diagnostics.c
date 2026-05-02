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
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
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
lean_dec_ref(v___x_136_);
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
lean_dec_ref(v_t_183_);
v___x_186_ = lean_apply_1(v_k_184_, v_i_185_);
return v___x_186_;
}
else
{
lean_object* v_s_187_; lean_object* v___x_188_; 
v_s_187_ = lean_ctor_get(v_t_183_, 0);
lean_inc_ref(v_s_187_);
lean_dec_ref(v_t_183_);
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
v___x_252_ = lean_string_dec_lt(v_s_250_, v_s_251_);
if (v___x_252_ == 0)
{
uint8_t v___x_253_; 
v___x_253_ = lean_string_dec_eq(v_s_250_, v_s_251_);
if (v___x_253_ == 0)
{
uint8_t v___x_254_; 
v___x_254_ = 2;
return v___x_254_;
}
else
{
uint8_t v___x_255_; 
v___x_255_ = 1;
return v___x_255_;
}
}
else
{
uint8_t v___x_256_; 
v___x_256_ = 0;
return v___x_256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticCode_ord___boxed(lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Lean_Lsp_instOrdDiagnosticCode_ord(v_x_257_, v_x_258_);
lean_dec_ref(v_x_258_);
lean_dec_ref(v_x_257_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0(lean_object* v_x_264_){
_start:
{
switch(lean_obj_tag(v_x_264_))
{
case 2:
{
lean_object* v_n_273_; lean_object* v_mantissa_274_; lean_object* v_exponent_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v_n_273_ = lean_ctor_get(v_x_264_, 0);
v_mantissa_274_ = lean_ctor_get(v_n_273_, 0);
v_exponent_275_ = lean_ctor_get(v_n_273_, 1);
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_nat_dec_eq(v_exponent_275_, v___x_276_);
if (v___x_277_ == 0)
{
goto v___jp_265_;
}
else
{
lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_285_; 
lean_inc(v_mantissa_274_);
v_isSharedCheck_285_ = !lean_is_exclusive(v_x_264_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; 
v_unused_286_ = lean_ctor_get(v_x_264_, 0);
lean_dec(v_unused_286_);
v___x_279_ = v_x_264_;
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
else
{
lean_dec(v_x_264_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
lean_ctor_set_tag(v___x_279_, 0);
lean_ctor_set(v___x_279_, 0, v_mantissa_274_);
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_mantissa_274_);
v___x_282_ = v_reuseFailAlloc_284_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; 
v___x_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
}
}
}
case 3:
{
lean_object* v_s_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_295_; 
v_s_287_ = lean_ctor_get(v_x_264_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_x_264_);
if (v_isSharedCheck_295_ == 0)
{
v___x_289_ = v_x_264_;
v_isShared_290_ = v_isSharedCheck_295_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_s_287_);
lean_dec(v_x_264_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_295_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set_tag(v___x_289_, 1);
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_s_287_);
v___x_292_ = v_reuseFailAlloc_294_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_293_; 
v___x_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
}
}
default: 
{
goto v___jp_265_;
}
}
v___jp_265_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_266_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0));
v___x_267_ = lean_unsigned_to_nat(80u);
v___x_268_ = l_Lean_Json_pretty(v_x_264_, v___x_267_);
v___x_269_ = lean_string_append(v___x_266_, v___x_268_);
lean_dec_ref(v___x_268_);
v___x_270_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_271_ = lean_string_append(v___x_269_, v___x_270_);
v___x_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticCode___lam__0(lean_object* v_x_298_){
_start:
{
if (lean_obj_tag(v_x_298_) == 0)
{
lean_object* v_i_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_307_; 
v_i_299_ = lean_ctor_get(v_x_298_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v_x_298_);
if (v_isSharedCheck_307_ == 0)
{
v___x_301_ = v_x_298_;
v_isShared_302_ = v_isSharedCheck_307_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_i_299_);
lean_dec(v_x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_307_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_303_ = l_Lean_JsonNumber_fromInt(v_i_299_);
if (v_isShared_302_ == 0)
{
lean_ctor_set_tag(v___x_301_, 2);
lean_ctor_set(v___x_301_, 0, v___x_303_);
v___x_305_ = v___x_301_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(2, 1, 0);
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
else
{
lean_object* v_s_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
v_s_308_ = lean_ctor_get(v_x_298_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v_x_298_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v_x_298_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_s_308_);
lean_dec(v_x_298_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set_tag(v___x_310_, 3);
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_s_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorIdx(uint8_t v_x_318_){
_start:
{
if (v_x_318_ == 0)
{
lean_object* v___x_319_; 
v___x_319_ = lean_unsigned_to_nat(0u);
return v___x_319_;
}
else
{
lean_object* v___x_320_; 
v___x_320_ = lean_unsigned_to_nat(1u);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorIdx___boxed(lean_object* v_x_321_){
_start:
{
uint8_t v_x_boxed_322_; lean_object* v_res_323_; 
v_x_boxed_322_ = lean_unbox(v_x_321_);
v_res_323_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_x_boxed_322_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_toCtorIdx(uint8_t v_x_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_toCtorIdx___boxed(lean_object* v_x_326_){
_start:
{
uint8_t v_x_4__boxed_327_; lean_object* v_res_328_; 
v_x_4__boxed_327_ = lean_unbox(v_x_326_);
v_res_328_ = l_Lean_Lsp_DiagnosticTag_toCtorIdx(v_x_4__boxed_327_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___redArg(lean_object* v_k_329_){
_start:
{
lean_inc(v_k_329_);
return v_k_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___redArg___boxed(lean_object* v_k_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_Lsp_DiagnosticTag_ctorElim___redArg(v_k_330_);
lean_dec(v_k_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim(lean_object* v_motive_332_, lean_object* v_ctorIdx_333_, uint8_t v_t_334_, lean_object* v_h_335_, lean_object* v_k_336_){
_start:
{
lean_inc(v_k_336_);
return v_k_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_ctorElim___boxed(lean_object* v_motive_337_, lean_object* v_ctorIdx_338_, lean_object* v_t_339_, lean_object* v_h_340_, lean_object* v_k_341_){
_start:
{
uint8_t v_t_boxed_342_; lean_object* v_res_343_; 
v_t_boxed_342_ = lean_unbox(v_t_339_);
v_res_343_ = l_Lean_Lsp_DiagnosticTag_ctorElim(v_motive_337_, v_ctorIdx_338_, v_t_boxed_342_, v_h_340_, v_k_341_);
lean_dec(v_k_341_);
lean_dec(v_ctorIdx_338_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg(lean_object* v_unnecessary_344_){
_start:
{
lean_inc(v_unnecessary_344_);
return v_unnecessary_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg___boxed(lean_object* v_unnecessary_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Lsp_DiagnosticTag_unnecessary_elim___redArg(v_unnecessary_345_);
lean_dec(v_unnecessary_345_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim(lean_object* v_motive_347_, uint8_t v_t_348_, lean_object* v_h_349_, lean_object* v_unnecessary_350_){
_start:
{
lean_inc(v_unnecessary_350_);
return v_unnecessary_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_unnecessary_elim___boxed(lean_object* v_motive_351_, lean_object* v_t_352_, lean_object* v_h_353_, lean_object* v_unnecessary_354_){
_start:
{
uint8_t v_t_boxed_355_; lean_object* v_res_356_; 
v_t_boxed_355_ = lean_unbox(v_t_352_);
v_res_356_ = l_Lean_Lsp_DiagnosticTag_unnecessary_elim(v_motive_351_, v_t_boxed_355_, v_h_353_, v_unnecessary_354_);
lean_dec(v_unnecessary_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg(lean_object* v_deprecated_357_){
_start:
{
lean_inc(v_deprecated_357_);
return v_deprecated_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg___boxed(lean_object* v_deprecated_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Lsp_DiagnosticTag_deprecated_elim___redArg(v_deprecated_358_);
lean_dec(v_deprecated_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim(lean_object* v_motive_360_, uint8_t v_t_361_, lean_object* v_h_362_, lean_object* v_deprecated_363_){
_start:
{
lean_inc(v_deprecated_363_);
return v_deprecated_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticTag_deprecated_elim___boxed(lean_object* v_motive_364_, lean_object* v_t_365_, lean_object* v_h_366_, lean_object* v_deprecated_367_){
_start:
{
uint8_t v_t_boxed_368_; lean_object* v_res_369_; 
v_t_boxed_368_ = lean_unbox(v_t_365_);
v_res_369_ = l_Lean_Lsp_DiagnosticTag_deprecated_elim(v_motive_364_, v_t_boxed_368_, v_h_366_, v_deprecated_367_);
lean_dec(v_deprecated_367_);
return v_res_369_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDiagnosticTag_default(void){
_start:
{
uint8_t v___x_370_; 
v___x_370_ = 0;
return v___x_370_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedDiagnosticTag(void){
_start:
{
uint8_t v___x_371_; 
v___x_371_ = 0;
return v___x_371_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticTag_beq(uint8_t v_x_372_, uint8_t v_y_373_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_374_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_x_372_);
v___x_375_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_y_373_);
v___x_376_ = lean_nat_dec_eq(v___x_374_, v___x_375_);
lean_dec(v___x_375_);
lean_dec(v___x_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticTag_beq___boxed(lean_object* v_x_377_, lean_object* v_y_378_){
_start:
{
uint8_t v_x_17__boxed_379_; uint8_t v_y_18__boxed_380_; uint8_t v_res_381_; lean_object* v_r_382_; 
v_x_17__boxed_379_ = lean_unbox(v_x_377_);
v_y_18__boxed_380_ = lean_unbox(v_y_378_);
v_res_381_ = l_Lean_Lsp_instBEqDiagnosticTag_beq(v_x_17__boxed_379_, v_y_18__boxed_380_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticTag_ord(uint8_t v_x_385_, uint8_t v_y_386_){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_387_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_x_385_);
v___x_388_ = l_Lean_Lsp_DiagnosticTag_ctorIdx(v_y_386_);
v___x_389_ = lean_nat_dec_lt(v___x_387_, v___x_388_);
if (v___x_389_ == 0)
{
uint8_t v___x_390_; 
v___x_390_ = lean_nat_dec_eq(v___x_387_, v___x_388_);
lean_dec(v___x_388_);
lean_dec(v___x_387_);
if (v___x_390_ == 0)
{
uint8_t v___x_391_; 
v___x_391_ = 2;
return v___x_391_;
}
else
{
uint8_t v___x_392_; 
v___x_392_ = 1;
return v___x_392_;
}
}
else
{
uint8_t v___x_393_; 
lean_dec(v___x_388_);
lean_dec(v___x_387_);
v___x_393_ = 0;
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticTag_ord___boxed(lean_object* v_x_394_, lean_object* v_y_395_){
_start:
{
uint8_t v_x_30__boxed_396_; uint8_t v_y_31__boxed_397_; uint8_t v_res_398_; lean_object* v_r_399_; 
v_x_30__boxed_396_ = lean_unbox(v_x_394_);
v_y_31__boxed_397_ = lean_unbox(v_y_395_);
v_res_398_ = l_Lean_Lsp_instOrdDiagnosticTag_ord(v_x_30__boxed_396_, v_y_31__boxed_397_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0(lean_object* v_j_411_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Json_getNat_x3f(v_j_411_);
if (lean_obj_tag(v___x_414_) == 1)
{
lean_object* v_a_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref(v___x_414_);
v___x_416_ = lean_unsigned_to_nat(1u);
v___x_417_ = lean_nat_dec_eq(v_a_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = lean_unsigned_to_nat(2u);
v___x_419_ = lean_nat_dec_eq(v_a_415_, v___x_418_);
lean_dec(v_a_415_);
if (v___x_419_ == 0)
{
goto v___jp_412_;
}
else
{
lean_object* v___x_420_; 
v___x_420_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__2));
return v___x_420_;
}
}
else
{
lean_object* v___x_421_; 
lean_dec(v_a_415_);
v___x_421_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__3));
return v___x_421_;
}
}
else
{
lean_dec_ref(v___x_414_);
goto v___jp_412_;
}
v___jp_412_:
{
lean_object* v___x_413_; 
v___x_413_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticTag___lam__0___closed__1));
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticTag___lam__0(uint8_t v_x_424_){
_start:
{
if (v_x_424_ == 0)
{
lean_object* v___x_425_; 
v___x_425_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
return v___x_425_;
}
else
{
lean_object* v___x_426_; 
v___x_426_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticTag___lam__0___boxed(lean_object* v_x_427_){
_start:
{
uint8_t v_x_48__boxed_428_; lean_object* v_res_429_; 
v_x_48__boxed_428_ = lean_unbox(v_x_427_);
v_res_429_ = l_Lean_Lsp_instToJsonDiagnosticTag___lam__0(v_x_48__boxed_428_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(uint8_t v_x_432_){
_start:
{
if (v_x_432_ == 0)
{
lean_object* v___x_433_; 
v___x_433_ = lean_unsigned_to_nat(0u);
return v___x_433_;
}
else
{
lean_object* v___x_434_; 
v___x_434_ = lean_unsigned_to_nat(1u);
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorIdx___boxed(lean_object* v_x_435_){
_start:
{
uint8_t v_x_boxed_436_; lean_object* v_res_437_; 
v_x_boxed_436_ = lean_unbox(v_x_435_);
v_res_437_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_x_boxed_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx(uint8_t v_x_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx___boxed(lean_object* v_x_440_){
_start:
{
uint8_t v_x_4__boxed_441_; lean_object* v_res_442_; 
v_x_4__boxed_441_ = lean_unbox(v_x_440_);
v_res_442_ = l_Lean_Lsp_LeanDiagnosticTag_toCtorIdx(v_x_4__boxed_441_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg(lean_object* v_k_443_){
_start:
{
lean_inc(v_k_443_);
return v_k_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg___boxed(lean_object* v_k_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Lsp_LeanDiagnosticTag_ctorElim___redArg(v_k_444_);
lean_dec(v_k_444_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim(lean_object* v_motive_446_, lean_object* v_ctorIdx_447_, uint8_t v_t_448_, lean_object* v_h_449_, lean_object* v_k_450_){
_start:
{
lean_inc(v_k_450_);
return v_k_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_ctorElim___boxed(lean_object* v_motive_451_, lean_object* v_ctorIdx_452_, lean_object* v_t_453_, lean_object* v_h_454_, lean_object* v_k_455_){
_start:
{
uint8_t v_t_boxed_456_; lean_object* v_res_457_; 
v_t_boxed_456_ = lean_unbox(v_t_453_);
v_res_457_ = l_Lean_Lsp_LeanDiagnosticTag_ctorElim(v_motive_451_, v_ctorIdx_452_, v_t_boxed_456_, v_h_454_, v_k_455_);
lean_dec(v_k_455_);
lean_dec(v_ctorIdx_452_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg(lean_object* v_unsolvedGoals_458_){
_start:
{
lean_inc(v_unsolvedGoals_458_);
return v_unsolvedGoals_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg___boxed(lean_object* v_unsolvedGoals_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___redArg(v_unsolvedGoals_459_);
lean_dec(v_unsolvedGoals_459_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim(lean_object* v_motive_461_, uint8_t v_t_462_, lean_object* v_h_463_, lean_object* v_unsolvedGoals_464_){
_start:
{
lean_inc(v_unsolvedGoals_464_);
return v_unsolvedGoals_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim___boxed(lean_object* v_motive_465_, lean_object* v_t_466_, lean_object* v_h_467_, lean_object* v_unsolvedGoals_468_){
_start:
{
uint8_t v_t_boxed_469_; lean_object* v_res_470_; 
v_t_boxed_469_ = lean_unbox(v_t_466_);
v_res_470_ = l_Lean_Lsp_LeanDiagnosticTag_unsolvedGoals_elim(v_motive_465_, v_t_boxed_469_, v_h_467_, v_unsolvedGoals_468_);
lean_dec(v_unsolvedGoals_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg(lean_object* v_goalsAccomplished_471_){
_start:
{
lean_inc(v_goalsAccomplished_471_);
return v_goalsAccomplished_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg___boxed(lean_object* v_goalsAccomplished_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___redArg(v_goalsAccomplished_472_);
lean_dec(v_goalsAccomplished_472_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim(lean_object* v_motive_474_, uint8_t v_t_475_, lean_object* v_h_476_, lean_object* v_goalsAccomplished_477_){
_start:
{
lean_inc(v_goalsAccomplished_477_);
return v_goalsAccomplished_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim___boxed(lean_object* v_motive_478_, lean_object* v_t_479_, lean_object* v_h_480_, lean_object* v_goalsAccomplished_481_){
_start:
{
uint8_t v_t_boxed_482_; lean_object* v_res_483_; 
v_t_boxed_482_ = lean_unbox(v_t_479_);
v_res_483_ = l_Lean_Lsp_LeanDiagnosticTag_goalsAccomplished_elim(v_motive_478_, v_t_boxed_482_, v_h_480_, v_goalsAccomplished_481_);
lean_dec(v_goalsAccomplished_481_);
return v_res_483_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag_default(void){
_start:
{
uint8_t v___x_484_; 
v___x_484_ = 0;
return v___x_484_;
}
}
static uint8_t _init_l_Lean_Lsp_instInhabitedLeanDiagnosticTag(void){
_start:
{
uint8_t v___x_485_; 
v___x_485_ = 0;
return v___x_485_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(uint8_t v_x_486_, uint8_t v_y_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_488_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_x_486_);
v___x_489_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_y_487_);
v___x_490_ = lean_nat_dec_eq(v___x_488_, v___x_489_);
lean_dec(v___x_489_);
lean_dec(v___x_488_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqLeanDiagnosticTag_beq___boxed(lean_object* v_x_491_, lean_object* v_y_492_){
_start:
{
uint8_t v_x_17__boxed_493_; uint8_t v_y_18__boxed_494_; uint8_t v_res_495_; lean_object* v_r_496_; 
v_x_17__boxed_493_ = lean_unbox(v_x_491_);
v_y_18__boxed_494_ = lean_unbox(v_y_492_);
v_res_495_ = l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(v_x_17__boxed_493_, v_y_18__boxed_494_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdLeanDiagnosticTag_ord(uint8_t v_x_499_, uint8_t v_y_500_){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_501_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_x_499_);
v___x_502_ = l_Lean_Lsp_LeanDiagnosticTag_ctorIdx(v_y_500_);
v___x_503_ = lean_nat_dec_lt(v___x_501_, v___x_502_);
if (v___x_503_ == 0)
{
uint8_t v___x_504_; 
v___x_504_ = lean_nat_dec_eq(v___x_501_, v___x_502_);
lean_dec(v___x_502_);
lean_dec(v___x_501_);
if (v___x_504_ == 0)
{
uint8_t v___x_505_; 
v___x_505_ = 2;
return v___x_505_;
}
else
{
uint8_t v___x_506_; 
v___x_506_ = 1;
return v___x_506_;
}
}
else
{
uint8_t v___x_507_; 
lean_dec(v___x_502_);
lean_dec(v___x_501_);
v___x_507_ = 0;
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdLeanDiagnosticTag_ord___boxed(lean_object* v_x_508_, lean_object* v_y_509_){
_start:
{
uint8_t v_x_30__boxed_510_; uint8_t v_y_31__boxed_511_; uint8_t v_res_512_; lean_object* v_r_513_; 
v_x_30__boxed_510_ = lean_unbox(v_x_508_);
v_y_31__boxed_511_ = lean_unbox(v_y_509_);
v_res_512_ = l_Lean_Lsp_instOrdLeanDiagnosticTag_ord(v_x_30__boxed_510_, v_y_31__boxed_511_);
v_r_513_ = lean_box(v_res_512_);
return v_r_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0(lean_object* v_j_525_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_Json_getNat_x3f(v_j_525_);
if (lean_obj_tag(v___x_528_) == 1)
{
lean_object* v_a_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
lean_dec_ref(v___x_528_);
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = lean_nat_dec_eq(v_a_529_, v___x_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_532_ = lean_unsigned_to_nat(2u);
v___x_533_ = lean_nat_dec_eq(v_a_529_, v___x_532_);
lean_dec(v_a_529_);
if (v___x_533_ == 0)
{
goto v___jp_526_;
}
else
{
lean_object* v___x_534_; 
v___x_534_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__2));
return v___x_534_;
}
}
else
{
lean_object* v___x_535_; 
lean_dec(v_a_529_);
v___x_535_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__3));
return v___x_535_;
}
}
else
{
lean_dec_ref(v___x_528_);
goto v___jp_526_;
}
v___jp_526_:
{
lean_object* v___x_527_; 
v___x_527_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanDiagnosticTag___lam__0___closed__1));
return v___x_527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0(uint8_t v_x_538_){
_start:
{
if (v_x_538_ == 0)
{
lean_object* v___x_539_; 
v___x_539_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
return v___x_539_;
}
else
{
lean_object* v___x_540_; 
v___x_540_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0___boxed(lean_object* v_x_541_){
_start:
{
uint8_t v_x_48__boxed_542_; lean_object* v_res_543_; 
v_x_48__boxed_542_ = lean_unbox(v_x_541_);
v_res_543_ = l_Lean_Lsp_instToJsonLeanDiagnosticTag___lam__0(v_x_48__boxed_542_);
return v_res_543_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = ((lean_object*)(l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__0));
v___x_548_ = l_Lean_Lsp_instInhabitedLocation_default;
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v___x_547_);
return v___x_549_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default(void){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = lean_obj_once(&l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1, &l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1_once, _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default___closed__1);
return v___x_550_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation(void){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Lsp_instInhabitedDiagnosticRelatedInformation_default;
return v___x_551_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
lean_object* v_location_554_; lean_object* v_message_555_; lean_object* v_location_556_; lean_object* v_message_557_; uint8_t v___x_558_; 
v_location_554_ = lean_ctor_get(v_x_552_, 0);
v_message_555_ = lean_ctor_get(v_x_552_, 1);
v_location_556_ = lean_ctor_get(v_x_553_, 0);
v_message_557_ = lean_ctor_get(v_x_553_, 1);
v___x_558_ = l_Lean_Lsp_instBEqLocation_beq(v_location_554_, v_location_556_);
if (v___x_558_ == 0)
{
return v___x_558_;
}
else
{
uint8_t v___x_559_; 
v___x_559_ = lean_string_dec_eq(v_message_555_, v_message_557_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq___boxed(lean_object* v_x_560_, lean_object* v_x_561_){
_start:
{
uint8_t v_res_562_; lean_object* v_r_563_; 
v_res_562_ = l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(v_x_560_, v_x_561_);
lean_dec_ref(v_x_561_);
lean_dec_ref(v_x_560_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
if (lean_obj_tag(v_a_566_) == 0)
{
lean_object* v___x_568_; 
v___x_568_ = lean_array_to_list(v_a_567_);
return v___x_568_;
}
else
{
lean_object* v_head_569_; lean_object* v_tail_570_; lean_object* v___x_571_; 
v_head_569_ = lean_ctor_get(v_a_566_, 0);
lean_inc(v_head_569_);
v_tail_570_ = lean_ctor_get(v_a_566_, 1);
lean_inc(v_tail_570_);
lean_dec_ref(v_a_566_);
v___x_571_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_567_, v_head_569_);
v_a_566_ = v_tail_570_;
v_a_567_ = v___x_571_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(lean_object* v_x_577_){
_start:
{
lean_object* v_location_578_; lean_object* v_message_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_599_; 
v_location_578_ = lean_ctor_get(v_x_577_, 0);
v_message_579_ = lean_ctor_get(v_x_577_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v_x_577_);
if (v_isSharedCheck_599_ == 0)
{
v___x_581_ = v_x_577_;
v_isShared_582_ = v_isSharedCheck_599_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_message_579_);
lean_inc(v_location_578_);
lean_dec(v_x_577_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_599_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_583_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0));
v___x_584_ = l_Lean_Lsp_instToJsonLocation_toJson(v_location_578_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v___x_584_);
lean_ctor_set(v___x_581_, 0, v___x_583_);
v___x_586_ = v___x_581_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v___x_584_);
v___x_586_ = v_reuseFailAlloc_598_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_587_ = lean_box(0);
v___x_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
v___x_590_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_590_, 0, v_message_579_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v___x_587_);
v___x_593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v___x_587_);
v___x_594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_588_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2));
v___x_596_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(v___x_594_, v___x_595_);
v___x_597_ = l_Lean_Json_mkObj(v___x_596_);
lean_dec(v___x_596_);
return v___x_597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(lean_object* v_j_602_, lean_object* v_k_603_){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = l_Lean_Json_getObjValD(v_j_602_, v_k_603_);
v___x_605_ = l_Lean_Lsp_instFromJsonLocation_fromJson(v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0___boxed(lean_object* v_j_606_, lean_object* v_k_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(v_j_606_, v_k_607_);
lean_dec_ref(v_k_607_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(lean_object* v_j_609_, lean_object* v_k_610_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = l_Lean_Json_getObjValD(v_j_609_, v_k_610_);
v___x_612_ = l_Lean_Json_getStr_x3f(v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1___boxed(lean_object* v_j_613_, lean_object* v_k_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_j_613_, v_k_614_);
lean_dec_ref(v_k_614_);
return v_res_615_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4(void){
_start:
{
uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = 1;
v___x_624_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__3));
v___x_625_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_624_, v___x_623_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5));
v___x_628_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__4);
v___x_629_ = lean_string_append(v___x_628_, v___x_627_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8(void){
_start:
{
uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = 1;
v___x_633_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__7));
v___x_634_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_633_, v___x_632_);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__8);
v___x_636_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6);
v___x_637_ = lean_string_append(v___x_636_, v___x_635_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_640_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__9);
v___x_641_ = lean_string_append(v___x_640_, v___x_639_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13(void){
_start:
{
uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = 1;
v___x_645_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__12));
v___x_646_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_645_, v___x_644_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13);
v___x_648_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__6);
v___x_649_ = lean_string_append(v___x_648_, v___x_647_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_651_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__14);
v___x_652_ = lean_string_append(v___x_651_, v___x_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(lean_object* v_json_653_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__0));
lean_inc(v_json_653_);
v___x_655_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__0(v_json_653_, v___x_654_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_665_; 
lean_dec(v_json_653_);
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_665_ == 0)
{
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_665_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_665_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_660_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__11);
v___x_661_ = lean_string_append(v___x_660_, v_a_656_);
lean_dec(v_a_656_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_661_);
v___x_663_ = v___x_658_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
else
{
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec(v_json_653_);
v_a_666_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_655_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_655_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
lean_ctor_set_tag(v___x_668_, 0);
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_a_674_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_674_);
lean_dec_ref(v___x_655_);
v___x_675_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
v___x_676_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_653_, v___x_675_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_686_; 
lean_dec(v_a_674_);
v_a_677_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_686_ == 0)
{
v___x_679_ = v___x_676_;
v_isShared_680_ = v_isSharedCheck_686_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_676_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_686_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_681_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__15);
v___x_682_ = lean_string_append(v___x_681_, v_a_677_);
lean_dec(v_a_677_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v___x_682_);
v___x_684_ = v___x_679_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
else
{
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec(v_a_674_);
v_a_687_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_676_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_676_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set_tag(v___x_689_, 0);
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_703_; 
v_a_695_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_703_ == 0)
{
v___x_697_ = v___x_676_;
v_isShared_698_ = v_isSharedCheck_703_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_676_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_703_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v_a_674_);
lean_ctor_set(v___x_699_, 1, v_a_695_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_699_);
v___x_701_ = v___x_697_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
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
}
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord(lean_object* v_x_706_, lean_object* v_x_707_){
_start:
{
lean_object* v_location_708_; lean_object* v_message_709_; lean_object* v_location_710_; lean_object* v_message_711_; uint8_t v___x_712_; 
v_location_708_ = lean_ctor_get(v_x_706_, 0);
v_message_709_ = lean_ctor_get(v_x_706_, 1);
v_location_710_ = lean_ctor_get(v_x_707_, 0);
v_message_711_ = lean_ctor_get(v_x_707_, 1);
v___x_712_ = l_Lean_Lsp_instOrdLocation_ord(v_location_708_, v_location_710_);
if (v___x_712_ == 1)
{
uint8_t v___x_713_; 
v___x_713_ = lean_string_dec_lt(v_message_709_, v_message_711_);
if (v___x_713_ == 0)
{
uint8_t v___x_714_; 
v___x_714_ = lean_string_dec_eq(v_message_709_, v_message_711_);
if (v___x_714_ == 0)
{
uint8_t v___x_715_; 
v___x_715_ = 2;
return v___x_715_;
}
else
{
return v___x_712_;
}
}
else
{
uint8_t v___x_716_; 
v___x_716_ = 0;
return v___x_716_;
}
}
else
{
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord___boxed(lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
uint8_t v_res_719_; lean_object* v_r_720_; 
v_res_719_ = l_Lean_Lsp_instOrdDiagnosticRelatedInformation_ord(v_x_717_, v_x_718_);
lean_dec_ref(v_x_718_);
lean_dec_ref(v_x_717_);
v_r_720_ = lean_box(v_res_719_);
return v_r_720_;
}
}
static lean_object* _init_l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = l_Lean_Lsp_instInhabitedRange_default;
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(lean_object* v_inst_725_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_726_ = l_Lean_Lsp_instInhabitedRange_default;
v___x_727_ = lean_obj_once(&l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0, &l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0_once, _init_l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg___closed__0);
v___x_728_ = lean_box(0);
v___x_729_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_729_, 0, v___x_726_);
lean_ctor_set(v___x_729_, 1, v___x_727_);
lean_ctor_set(v___x_729_, 2, v___x_728_);
lean_ctor_set(v___x_729_, 3, v___x_728_);
lean_ctor_set(v___x_729_, 4, v___x_728_);
lean_ctor_set(v___x_729_, 5, v___x_728_);
lean_ctor_set(v___x_729_, 6, v_inst_725_);
lean_ctor_set(v___x_729_, 7, v___x_728_);
lean_ctor_set(v___x_729_, 8, v___x_728_);
lean_ctor_set(v___x_729_, 9, v___x_728_);
lean_ctor_set(v___x_729_, 10, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith_default(lean_object* v_00_u03b1_730_, lean_object* v_inst_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith___redArg(lean_object* v_inst_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instInhabitedDiagnosticWith(lean_object* v_a_735_, lean_object* v_inst_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Lsp_instInhabitedDiagnosticWith_default___redArg(v_inst_736_);
return v___x_737_;
}
}
static lean_object* _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1(void){
_start:
{
lean_object* v___x_739_; lean_object* v___f_740_; 
v___x_739_ = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
v___f_740_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_740_, 0, v___x_739_);
return v___f_740_;
}
}
static lean_object* _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2(void){
_start:
{
lean_object* v___x_741_; lean_object* v___f_742_; 
v___x_741_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_742_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_742_, 0, v___x_741_);
return v___f_742_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(lean_object* v_inst_750_, lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
lean_object* v_range_753_; lean_object* v_fullRange_x3f_754_; lean_object* v_severity_x3f_755_; lean_object* v_isSilent_x3f_756_; lean_object* v_code_x3f_757_; lean_object* v_source_x3f_758_; lean_object* v_message_759_; lean_object* v_tags_x3f_760_; lean_object* v_leanTags_x3f_761_; lean_object* v_relatedInformation_x3f_762_; lean_object* v_data_x3f_763_; lean_object* v_range_764_; lean_object* v_fullRange_x3f_765_; lean_object* v_severity_x3f_766_; lean_object* v_isSilent_x3f_767_; lean_object* v_code_x3f_768_; lean_object* v_source_x3f_769_; lean_object* v_message_770_; lean_object* v_tags_x3f_771_; lean_object* v_leanTags_x3f_772_; lean_object* v_relatedInformation_x3f_773_; lean_object* v_data_x3f_774_; uint8_t v___x_775_; 
v_range_753_ = lean_ctor_get(v_x_751_, 0);
lean_inc_ref(v_range_753_);
v_fullRange_x3f_754_ = lean_ctor_get(v_x_751_, 1);
lean_inc(v_fullRange_x3f_754_);
v_severity_x3f_755_ = lean_ctor_get(v_x_751_, 2);
lean_inc(v_severity_x3f_755_);
v_isSilent_x3f_756_ = lean_ctor_get(v_x_751_, 3);
lean_inc(v_isSilent_x3f_756_);
v_code_x3f_757_ = lean_ctor_get(v_x_751_, 4);
lean_inc(v_code_x3f_757_);
v_source_x3f_758_ = lean_ctor_get(v_x_751_, 5);
lean_inc(v_source_x3f_758_);
v_message_759_ = lean_ctor_get(v_x_751_, 6);
lean_inc(v_message_759_);
v_tags_x3f_760_ = lean_ctor_get(v_x_751_, 7);
lean_inc(v_tags_x3f_760_);
v_leanTags_x3f_761_ = lean_ctor_get(v_x_751_, 8);
lean_inc(v_leanTags_x3f_761_);
v_relatedInformation_x3f_762_ = lean_ctor_get(v_x_751_, 9);
lean_inc(v_relatedInformation_x3f_762_);
v_data_x3f_763_ = lean_ctor_get(v_x_751_, 10);
lean_inc(v_data_x3f_763_);
lean_dec_ref(v_x_751_);
v_range_764_ = lean_ctor_get(v_x_752_, 0);
lean_inc_ref(v_range_764_);
v_fullRange_x3f_765_ = lean_ctor_get(v_x_752_, 1);
lean_inc(v_fullRange_x3f_765_);
v_severity_x3f_766_ = lean_ctor_get(v_x_752_, 2);
lean_inc(v_severity_x3f_766_);
v_isSilent_x3f_767_ = lean_ctor_get(v_x_752_, 3);
lean_inc(v_isSilent_x3f_767_);
v_code_x3f_768_ = lean_ctor_get(v_x_752_, 4);
lean_inc(v_code_x3f_768_);
v_source_x3f_769_ = lean_ctor_get(v_x_752_, 5);
lean_inc(v_source_x3f_769_);
v_message_770_ = lean_ctor_get(v_x_752_, 6);
lean_inc(v_message_770_);
v_tags_x3f_771_ = lean_ctor_get(v_x_752_, 7);
lean_inc(v_tags_x3f_771_);
v_leanTags_x3f_772_ = lean_ctor_get(v_x_752_, 8);
lean_inc(v_leanTags_x3f_772_);
v_relatedInformation_x3f_773_ = lean_ctor_get(v_x_752_, 9);
lean_inc(v_relatedInformation_x3f_773_);
v_data_x3f_774_ = lean_ctor_get(v_x_752_, 10);
lean_inc(v_data_x3f_774_);
lean_dec_ref(v_x_752_);
v___x_775_ = l_Lean_Lsp_instBEqRange_beq(v_range_753_, v_range_764_);
lean_dec_ref(v_range_764_);
lean_dec_ref(v_range_753_);
if (v___x_775_ == 0)
{
lean_dec(v_data_x3f_774_);
lean_dec(v_relatedInformation_x3f_773_);
lean_dec(v_leanTags_x3f_772_);
lean_dec(v_tags_x3f_771_);
lean_dec(v_message_770_);
lean_dec(v_source_x3f_769_);
lean_dec(v_code_x3f_768_);
lean_dec(v_isSilent_x3f_767_);
lean_dec(v_severity_x3f_766_);
lean_dec(v_fullRange_x3f_765_);
lean_dec(v_data_x3f_763_);
lean_dec(v_relatedInformation_x3f_762_);
lean_dec(v_leanTags_x3f_761_);
lean_dec(v_tags_x3f_760_);
lean_dec(v_message_759_);
lean_dec(v_source_x3f_758_);
lean_dec(v_code_x3f_757_);
lean_dec(v_isSilent_x3f_756_);
lean_dec(v_severity_x3f_755_);
lean_dec(v_fullRange_x3f_754_);
lean_dec_ref(v_inst_750_);
return v___x_775_;
}
else
{
lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_776_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__0));
v___x_777_ = l_Option_instBEq_beq___redArg(v___x_776_, v_fullRange_x3f_754_, v_fullRange_x3f_765_);
if (v___x_777_ == 0)
{
lean_dec(v_data_x3f_774_);
lean_dec(v_relatedInformation_x3f_773_);
lean_dec(v_leanTags_x3f_772_);
lean_dec(v_tags_x3f_771_);
lean_dec(v_message_770_);
lean_dec(v_source_x3f_769_);
lean_dec(v_code_x3f_768_);
lean_dec(v_isSilent_x3f_767_);
lean_dec(v_severity_x3f_766_);
lean_dec(v_data_x3f_763_);
lean_dec(v_relatedInformation_x3f_762_);
lean_dec(v_leanTags_x3f_761_);
lean_dec(v_tags_x3f_760_);
lean_dec(v_message_759_);
lean_dec(v_source_x3f_758_);
lean_dec(v_code_x3f_757_);
lean_dec(v_isSilent_x3f_756_);
lean_dec(v_severity_x3f_755_);
lean_dec_ref(v_inst_750_);
return v___x_777_;
}
else
{
lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_778_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticSeverity___closed__0));
v___x_779_ = l_Option_instBEq_beq___redArg(v___x_778_, v_severity_x3f_755_, v_severity_x3f_766_);
if (v___x_779_ == 0)
{
lean_dec(v_data_x3f_774_);
lean_dec(v_relatedInformation_x3f_773_);
lean_dec(v_leanTags_x3f_772_);
lean_dec(v_tags_x3f_771_);
lean_dec(v_message_770_);
lean_dec(v_source_x3f_769_);
lean_dec(v_code_x3f_768_);
lean_dec(v_isSilent_x3f_767_);
lean_dec(v_data_x3f_763_);
lean_dec(v_relatedInformation_x3f_762_);
lean_dec(v_leanTags_x3f_761_);
lean_dec(v_tags_x3f_760_);
lean_dec(v_message_759_);
lean_dec(v_source_x3f_758_);
lean_dec(v_code_x3f_757_);
lean_dec(v_isSilent_x3f_756_);
lean_dec_ref(v_inst_750_);
return v___x_779_;
}
else
{
lean_object* v___f_780_; uint8_t v___x_781_; 
v___f_780_ = lean_obj_once(&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1, &l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1_once, _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__1);
v___x_781_ = l_Option_instBEq_beq___redArg(v___f_780_, v_isSilent_x3f_756_, v_isSilent_x3f_767_);
if (v___x_781_ == 0)
{
lean_dec(v_data_x3f_774_);
lean_dec(v_relatedInformation_x3f_773_);
lean_dec(v_leanTags_x3f_772_);
lean_dec(v_tags_x3f_771_);
lean_dec(v_message_770_);
lean_dec(v_source_x3f_769_);
lean_dec(v_code_x3f_768_);
lean_dec(v_data_x3f_763_);
lean_dec(v_relatedInformation_x3f_762_);
lean_dec(v_leanTags_x3f_761_);
lean_dec(v_tags_x3f_760_);
lean_dec(v_message_759_);
lean_dec(v_source_x3f_758_);
lean_dec(v_code_x3f_757_);
lean_dec_ref(v_inst_750_);
return v___x_781_;
}
else
{
lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_782_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticCode___closed__0));
v___x_783_ = l_Option_instBEq_beq___redArg(v___x_782_, v_code_x3f_757_, v_code_x3f_768_);
if (v___x_783_ == 0)
{
lean_dec(v_data_x3f_774_);
lean_dec(v_relatedInformation_x3f_773_);
lean_dec(v_leanTags_x3f_772_);
lean_dec(v_tags_x3f_771_);
lean_dec(v_message_770_);
lean_dec(v_source_x3f_769_);
lean_dec(v_data_x3f_763_);
lean_dec(v_relatedInformation_x3f_762_);
lean_dec(v_leanTags_x3f_761_);
lean_dec(v_tags_x3f_760_);
lean_dec(v_message_759_);
lean_dec(v_source_x3f_758_);
lean_dec_ref(v_inst_750_);
return v___x_783_;
}
else
{
lean_object* v___f_784_; uint8_t v___x_785_; 
v___f_784_ = lean_obj_once(&l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2, &l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2_once, _init_l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__2);
v___x_785_ = l_Option_instBEq_beq___redArg(v___f_784_, v_source_x3f_758_, v_source_x3f_769_);
if (v___x_785_ == 0)
{
lean_dec(v_data_x3f_774_);
lean_dec(v_relatedInformation_x3f_773_);
lean_dec(v_leanTags_x3f_772_);
lean_dec(v_tags_x3f_771_);
lean_dec(v_message_770_);
lean_dec(v_data_x3f_763_);
lean_dec(v_relatedInformation_x3f_762_);
lean_dec(v_leanTags_x3f_761_);
lean_dec(v_tags_x3f_760_);
lean_dec(v_message_759_);
lean_dec_ref(v_inst_750_);
return v___x_785_;
}
else
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = lean_apply_2(v_inst_750_, v_message_759_, v_message_770_);
v___x_787_ = lean_unbox(v___x_786_);
if (v___x_787_ == 0)
{
uint8_t v___x_788_; 
lean_dec(v_data_x3f_774_);
lean_dec(v_relatedInformation_x3f_773_);
lean_dec(v_leanTags_x3f_772_);
lean_dec(v_tags_x3f_771_);
lean_dec(v_data_x3f_763_);
lean_dec(v_relatedInformation_x3f_762_);
lean_dec(v_leanTags_x3f_761_);
lean_dec(v_tags_x3f_760_);
v___x_788_ = lean_unbox(v___x_786_);
return v___x_788_;
}
else
{
lean_object* v___f_789_; uint8_t v___x_790_; 
v___f_789_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__3));
v___x_790_ = l_Option_instBEq_beq___redArg(v___f_789_, v_tags_x3f_760_, v_tags_x3f_771_);
if (v___x_790_ == 0)
{
lean_dec(v_data_x3f_774_);
lean_dec(v_relatedInformation_x3f_773_);
lean_dec(v_leanTags_x3f_772_);
lean_dec(v_data_x3f_763_);
lean_dec(v_relatedInformation_x3f_762_);
lean_dec(v_leanTags_x3f_761_);
return v___x_790_;
}
else
{
lean_object* v___f_791_; uint8_t v___x_792_; 
v___f_791_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__4));
v___x_792_ = l_Option_instBEq_beq___redArg(v___f_791_, v_leanTags_x3f_761_, v_leanTags_x3f_772_);
if (v___x_792_ == 0)
{
lean_dec(v_data_x3f_774_);
lean_dec(v_relatedInformation_x3f_773_);
lean_dec(v_data_x3f_763_);
lean_dec(v_relatedInformation_x3f_762_);
return v___x_792_;
}
else
{
lean_object* v___f_793_; uint8_t v___x_794_; 
v___f_793_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__5));
v___x_794_ = l_Option_instBEq_beq___redArg(v___f_793_, v_relatedInformation_x3f_762_, v_relatedInformation_x3f_773_);
if (v___x_794_ == 0)
{
lean_dec(v_data_x3f_774_);
lean_dec(v_data_x3f_763_);
return v___x_794_;
}
else
{
lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_795_ = ((lean_object*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___closed__6));
v___x_796_ = l_Option_instBEq_beq___redArg(v___x_795_, v_data_x3f_763_, v_data_x3f_774_);
return v___x_796_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg___boxed(lean_object* v_inst_797_, lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
uint8_t v_res_800_; lean_object* v_r_801_; 
v_res_800_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(v_inst_797_, v_x_798_, v_x_799_);
v_r_801_ = lean_box(v_res_800_);
return v_r_801_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq(lean_object* v_00_u03b1_802_, lean_object* v_inst_803_, lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
uint8_t v___x_806_; 
v___x_806_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___redArg(v_inst_803_, v_x_804_, v_x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed(lean_object* v_00_u03b1_807_, lean_object* v_inst_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
uint8_t v_res_811_; lean_object* v_r_812_; 
v_res_811_ = l_Lean_Lsp_instBEqDiagnosticWith_beq(v_00_u03b1_807_, v_inst_808_, v_x_809_, v_x_810_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith___redArg(lean_object* v_inst_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = lean_alloc_closure((void*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed), 4, 2);
lean_closure_set(v___x_814_, 0, lean_box(0));
lean_closure_set(v___x_814_, 1, v_inst_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith(lean_object* v_00_u03b1_815_, lean_object* v_inst_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = lean_alloc_closure((void*)(l_Lean_Lsp_instBEqDiagnosticWith_beq___boxed), 4, 2);
lean_closure_set(v___x_817_, 0, lean_box(0));
lean_closure_set(v___x_817_, 1, v_inst_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg(lean_object* v_inst_838_, lean_object* v_x_839_){
_start:
{
lean_object* v_range_840_; lean_object* v_fullRange_x3f_841_; lean_object* v_severity_x3f_842_; lean_object* v_isSilent_x3f_843_; lean_object* v_code_x3f_844_; lean_object* v_source_x3f_845_; lean_object* v_message_846_; lean_object* v_tags_x3f_847_; lean_object* v_leanTags_x3f_848_; lean_object* v_relatedInformation_x3f_849_; lean_object* v_data_x3f_850_; lean_object* v___x_851_; lean_object* v___f_852_; lean_object* v___f_853_; lean_object* v___f_854_; lean_object* v___f_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_range_840_ = lean_ctor_get(v_x_839_, 0);
lean_inc_ref(v_range_840_);
v_fullRange_x3f_841_ = lean_ctor_get(v_x_839_, 1);
lean_inc(v_fullRange_x3f_841_);
v_severity_x3f_842_ = lean_ctor_get(v_x_839_, 2);
lean_inc(v_severity_x3f_842_);
v_isSilent_x3f_843_ = lean_ctor_get(v_x_839_, 3);
lean_inc(v_isSilent_x3f_843_);
v_code_x3f_844_ = lean_ctor_get(v_x_839_, 4);
lean_inc(v_code_x3f_844_);
v_source_x3f_845_ = lean_ctor_get(v_x_839_, 5);
lean_inc(v_source_x3f_845_);
v_message_846_ = lean_ctor_get(v_x_839_, 6);
lean_inc(v_message_846_);
v_tags_x3f_847_ = lean_ctor_get(v_x_839_, 7);
lean_inc(v_tags_x3f_847_);
v_leanTags_x3f_848_ = lean_ctor_get(v_x_839_, 8);
lean_inc(v_leanTags_x3f_848_);
v_relatedInformation_x3f_849_ = lean_ctor_get(v_x_839_, 9);
lean_inc(v_relatedInformation_x3f_849_);
v_data_x3f_850_ = lean_ctor_get(v_x_839_, 10);
lean_inc(v_data_x3f_850_);
lean_dec_ref(v_x_839_);
v___x_851_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__0));
v___f_852_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticSeverity___closed__0));
v___f_853_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__1));
v___f_854_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticCode___closed__0));
v___f_855_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__2));
v___x_856_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__3));
v___x_857_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__4));
v___x_858_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__5));
v___x_859_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__6));
v___x_860_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
v___x_861_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_840_);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = lean_box(0);
v___x_864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
v___x_866_ = l_Lean_Json_opt___redArg(v___x_851_, v___x_865_, v_fullRange_x3f_841_);
v___x_867_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
v___x_868_ = l_Lean_Json_opt___redArg(v___f_852_, v___x_867_, v_severity_x3f_842_);
v___x_869_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
v___x_870_ = l_Lean_Json_opt___redArg(v___f_853_, v___x_869_, v_isSilent_x3f_843_);
v___x_871_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
v___x_872_ = l_Lean_Json_opt___redArg(v___f_854_, v___x_871_, v_code_x3f_844_);
v___x_873_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
v___x_874_ = l_Lean_Json_opt___redArg(v___f_855_, v___x_873_, v_source_x3f_845_);
v___x_875_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
v___x_876_ = lean_apply_1(v_inst_838_, v_message_846_);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_875_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set(v___x_878_, 1, v___x_863_);
v___x_879_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
v___x_880_ = l_Lean_Json_opt___redArg(v___x_856_, v___x_879_, v_tags_x3f_847_);
v___x_881_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
v___x_882_ = l_Lean_Json_opt___redArg(v___x_857_, v___x_881_, v_leanTags_x3f_848_);
v___x_883_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
v___x_884_ = l_Lean_Json_opt___redArg(v___x_858_, v___x_883_, v_relatedInformation_x3f_849_);
v___x_885_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
v___x_886_ = l_Lean_Json_opt___redArg(v___x_859_, v___x_885_, v_data_x3f_850_);
v___x_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v___x_863_);
v___x_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_884_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_882_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_880_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_878_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_874_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_872_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_870_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_868_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_866_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_864_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2));
v___x_899_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_859_, v___x_897_, v___x_898_);
v___x_900_ = l_Lean_Json_mkObj(v___x_899_);
lean_dec(v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson(lean_object* v_00_u03b1_901_, lean_object* v_inst_902_, lean_object* v_x_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg(v_inst_902_, v_x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith___redArg(lean_object* v_inst_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson), 3, 2);
lean_closure_set(v___x_906_, 0, lean_box(0));
lean_closure_set(v___x_906_, 1, v_inst_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith(lean_object* v_00_u03b1_907_, lean_object* v_inst_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = lean_alloc_closure((void*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson), 3, 2);
lean_closure_set(v___x_909_, 0, lean_box(0));
lean_closure_set(v___x_909_, 1, v_inst_908_);
return v___x_909_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4(void){
_start:
{
uint8_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_918_ = 1;
v___x_919_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__3));
v___x_920_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_919_, v___x_918_);
return v___x_920_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5));
v___x_922_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__4);
v___x_923_ = lean_string_append(v___x_922_, v___x_921_);
return v___x_923_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = 1;
v___x_927_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__6));
v___x_928_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_927_, v___x_926_);
return v___x_928_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__7);
v___x_930_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_931_ = lean_string_append(v___x_930_, v___x_929_);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_933_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__8);
v___x_934_ = lean_string_append(v___x_933_, v___x_932_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12(void){
_start:
{
uint8_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_938_ = 1;
v___x_939_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__11));
v___x_940_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_939_, v___x_938_);
return v___x_940_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__12);
v___x_942_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_943_ = lean_string_append(v___x_942_, v___x_941_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_945_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__13);
v___x_946_ = lean_string_append(v___x_945_, v___x_944_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = 1;
v___x_953_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__17));
v___x_954_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_953_, v___x_952_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_955_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__18);
v___x_956_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_957_ = lean_string_append(v___x_956_, v___x_955_);
return v___x_957_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_958_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_959_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__19);
v___x_960_ = lean_string_append(v___x_959_, v___x_958_);
return v___x_960_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25(void){
_start:
{
uint8_t v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = 1;
v___x_968_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__24));
v___x_969_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_968_, v___x_967_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_970_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__25);
v___x_971_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_972_ = lean_string_append(v___x_971_, v___x_970_);
return v___x_972_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_974_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__26);
v___x_975_ = lean_string_append(v___x_974_, v___x_973_);
return v___x_975_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_981_ = 1;
v___x_982_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__30));
v___x_983_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_982_, v___x_981_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_984_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__31);
v___x_985_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_986_ = lean_string_append(v___x_985_, v___x_984_);
return v___x_986_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_988_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__32);
v___x_989_ = lean_string_append(v___x_988_, v___x_987_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38(void){
_start:
{
uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = 1;
v___x_997_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__37));
v___x_998_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_997_, v___x_996_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__38);
v___x_1000_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1001_ = lean_string_append(v___x_1000_, v___x_999_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1003_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__39);
v___x_1004_ = lean_string_append(v___x_1003_, v___x_1002_);
return v___x_1004_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13, &l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__13);
v___x_1006_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1007_ = lean_string_append(v___x_1006_, v___x_1005_);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1009_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__41);
v___x_1010_ = lean_string_append(v___x_1009_, v___x_1008_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47(void){
_start:
{
uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = 1;
v___x_1019_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__46));
v___x_1020_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1019_, v___x_1018_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1021_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__47);
v___x_1022_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1023_ = lean_string_append(v___x_1022_, v___x_1021_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1025_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__48);
v___x_1026_ = lean_string_append(v___x_1025_, v___x_1024_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54(void){
_start:
{
uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = 1;
v___x_1035_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__53));
v___x_1036_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1035_, v___x_1034_);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__54);
v___x_1038_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1039_ = lean_string_append(v___x_1038_, v___x_1037_);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1040_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1041_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__55);
v___x_1042_ = lean_string_append(v___x_1041_, v___x_1040_);
return v___x_1042_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61(void){
_start:
{
uint8_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = 1;
v___x_1051_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__60));
v___x_1052_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1051_, v___x_1050_);
return v___x_1052_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1053_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__61);
v___x_1054_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1055_ = lean_string_append(v___x_1054_, v___x_1053_);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1056_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1057_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__62);
v___x_1058_ = lean_string_append(v___x_1057_, v___x_1056_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68(void){
_start:
{
uint8_t v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = 1;
v___x_1066_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__67));
v___x_1067_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1066_, v___x_1065_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__68);
v___x_1069_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__5);
v___x_1070_ = lean_string_append(v___x_1069_, v___x_1068_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_1072_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__69);
v___x_1073_ = lean_string_append(v___x_1072_, v___x_1071_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg(lean_object* v_inst_1074_, lean_object* v_json_1075_){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1076_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__0));
v___x_1077_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__1));
v___x_1078_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
lean_inc(v_json_1075_);
v___x_1079_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1075_, v___x_1076_, v___x_1078_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v_json_1075_);
lean_dec_ref(v_inst_1074_);
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1089_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1089_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1084_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9);
v___x_1085_ = lean_string_append(v___x_1084_, v_a_1080_);
lean_dec(v_a_1080_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1085_);
v___x_1087_ = v___x_1082_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
else
{
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec(v_json_1075_);
lean_dec_ref(v_inst_1074_);
v_a_1090_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1079_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1079_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set_tag(v___x_1092_, 0);
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v_a_1098_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1098_);
lean_dec_ref(v___x_1079_);
v___x_1099_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
lean_inc(v_json_1075_);
v___x_1100_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1075_, v___x_1077_, v___x_1099_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1110_; 
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
lean_dec_ref(v_inst_1074_);
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1103_ = v___x_1100_;
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1100_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1105_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14);
v___x_1106_ = lean_string_append(v___x_1105_, v_a_1101_);
lean_dec(v_a_1101_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___x_1106_);
v___x_1108_ = v___x_1103_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
else
{
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
lean_dec_ref(v_inst_1074_);
v_a_1111_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1100_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1100_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set_tag(v___x_1113_, 0);
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v_a_1119_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1119_);
lean_dec_ref(v___x_1100_);
v___x_1120_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__15));
v___x_1121_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
lean_inc(v_json_1075_);
v___x_1122_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1075_, v___x_1120_, v___x_1121_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1132_; 
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
lean_dec_ref(v_inst_1074_);
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1125_ = v___x_1122_;
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1127_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20);
v___x_1128_ = lean_string_append(v___x_1127_, v_a_1123_);
lean_dec(v_a_1123_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1128_);
v___x_1130_ = v___x_1125_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
else
{
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
lean_dec_ref(v_inst_1074_);
v_a_1133_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1122_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1122_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 0);
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_a_1141_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1141_);
lean_dec_ref(v___x_1122_);
v___x_1142_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__22));
v___x_1143_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
lean_inc(v_json_1075_);
v___x_1144_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1075_, v___x_1142_, v___x_1143_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v_a_1141_);
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
lean_dec_ref(v_inst_1074_);
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1154_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1154_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1149_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27);
v___x_1150_ = lean_string_append(v___x_1149_, v_a_1145_);
lean_dec(v_a_1145_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1150_);
v___x_1152_ = v___x_1147_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
else
{
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec(v_a_1141_);
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
lean_dec_ref(v_inst_1074_);
v_a_1155_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1144_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1144_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set_tag(v___x_1157_, 0);
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_a_1163_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1163_);
lean_dec_ref(v___x_1144_);
v___x_1164_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__28));
v___x_1165_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
lean_inc(v_json_1075_);
v___x_1166_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1075_, v___x_1164_, v___x_1165_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1176_; 
lean_dec(v_a_1163_);
lean_dec(v_a_1141_);
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
lean_dec_ref(v_inst_1074_);
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1176_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1176_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1171_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33);
v___x_1172_ = lean_string_append(v___x_1171_, v_a_1167_);
lean_dec(v_a_1167_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1172_);
v___x_1174_ = v___x_1169_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
else
{
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec(v_a_1163_);
lean_dec(v_a_1141_);
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
lean_dec_ref(v_inst_1074_);
v_a_1177_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1166_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1166_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set_tag(v___x_1179_, 0);
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_a_1185_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1185_);
lean_dec_ref(v___x_1166_);
v___x_1186_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__35));
v___x_1187_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
lean_inc(v_json_1075_);
v___x_1188_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1075_, v___x_1186_, v___x_1187_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1198_; 
lean_dec(v_a_1185_);
lean_dec(v_a_1163_);
lean_dec(v_a_1141_);
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
lean_dec_ref(v_inst_1074_);
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1191_ = v___x_1188_;
v_isShared_1192_ = v_isSharedCheck_1198_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1198_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1193_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40);
v___x_1194_ = lean_string_append(v___x_1193_, v_a_1189_);
lean_dec(v_a_1189_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1194_);
v___x_1196_ = v___x_1191_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
else
{
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec(v_a_1185_);
lean_dec(v_a_1163_);
lean_dec(v_a_1141_);
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
lean_dec_ref(v_inst_1074_);
v_a_1199_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1188_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1188_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set_tag(v___x_1201_, 0);
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_a_1207_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1207_);
lean_dec_ref(v___x_1188_);
v___x_1208_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
lean_inc(v_json_1075_);
v___x_1209_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1075_, v_inst_1074_, v___x_1208_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1219_; 
lean_dec(v_a_1207_);
lean_dec(v_a_1185_);
lean_dec(v_a_1163_);
lean_dec(v_a_1141_);
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1219_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1219_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1214_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42);
v___x_1215_ = lean_string_append(v___x_1214_, v_a_1210_);
lean_dec(v_a_1210_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___x_1215_);
v___x_1217_ = v___x_1212_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
else
{
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec(v_a_1207_);
lean_dec(v_a_1185_);
lean_dec(v_a_1163_);
lean_dec(v_a_1141_);
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
v_a_1220_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1209_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1209_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
lean_ctor_set_tag(v___x_1222_, 0);
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v_a_1228_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1228_);
lean_dec_ref(v___x_1209_);
v___x_1229_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__44));
v___x_1230_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
lean_inc(v_json_1075_);
v___x_1231_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1075_, v___x_1229_, v___x_1230_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1241_; 
lean_dec(v_a_1228_);
lean_dec(v_a_1207_);
lean_dec(v_a_1185_);
lean_dec(v_a_1163_);
lean_dec(v_a_1141_);
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1234_ = v___x_1231_;
v_isShared_1235_ = v_isSharedCheck_1241_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1231_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1241_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1236_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49);
v___x_1237_ = lean_string_append(v___x_1236_, v_a_1232_);
lean_dec(v_a_1232_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1237_);
v___x_1239_ = v___x_1234_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
else
{
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec(v_a_1228_);
lean_dec(v_a_1207_);
lean_dec(v_a_1185_);
lean_dec(v_a_1163_);
lean_dec(v_a_1141_);
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
v_a_1242_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1231_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1231_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
lean_ctor_set_tag(v___x_1244_, 0);
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v_a_1250_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1250_);
lean_dec_ref(v___x_1231_);
v___x_1251_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__51));
v___x_1252_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
lean_inc(v_json_1075_);
v___x_1253_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1075_, v___x_1251_, v___x_1252_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v_a_1250_);
lean_dec(v_a_1228_);
lean_dec(v_a_1207_);
lean_dec(v_a_1185_);
lean_dec(v_a_1163_);
lean_dec(v_a_1141_);
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1256_ = v___x_1253_;
v_isShared_1257_ = v_isSharedCheck_1263_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1253_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1263_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1258_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56);
v___x_1259_ = lean_string_append(v___x_1258_, v_a_1254_);
lean_dec(v_a_1254_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1259_);
v___x_1261_ = v___x_1256_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
else
{
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v_a_1250_);
lean_dec(v_a_1228_);
lean_dec(v_a_1207_);
lean_dec(v_a_1185_);
lean_dec(v_a_1163_);
lean_dec(v_a_1141_);
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
v_a_1264_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1253_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1253_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set_tag(v___x_1266_, 0);
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_a_1272_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1272_);
lean_dec_ref(v___x_1253_);
v___x_1273_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__58));
v___x_1274_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
lean_inc(v_json_1075_);
v___x_1275_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1075_, v___x_1273_, v___x_1274_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1285_; 
lean_dec(v_a_1272_);
lean_dec(v_a_1250_);
lean_dec(v_a_1228_);
lean_dec(v_a_1207_);
lean_dec(v_a_1185_);
lean_dec(v_a_1163_);
lean_dec(v_a_1141_);
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1280_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63);
v___x_1281_ = lean_string_append(v___x_1280_, v_a_1276_);
lean_dec(v_a_1276_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1281_);
v___x_1283_ = v___x_1278_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
else
{
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec(v_a_1272_);
lean_dec(v_a_1250_);
lean_dec(v_a_1228_);
lean_dec(v_a_1207_);
lean_dec(v_a_1185_);
lean_dec(v_a_1163_);
lean_dec(v_a_1141_);
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
lean_dec(v_json_1075_);
v_a_1286_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1275_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1275_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
lean_ctor_set_tag(v___x_1288_, 0);
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_a_1294_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1294_);
lean_dec_ref(v___x_1275_);
v___x_1295_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__65));
v___x_1296_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
v___x_1297_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_1075_, v___x_1295_, v___x_1296_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v_a_1294_);
lean_dec(v_a_1272_);
lean_dec(v_a_1250_);
lean_dec(v_a_1228_);
lean_dec(v_a_1207_);
lean_dec(v_a_1185_);
lean_dec(v_a_1163_);
lean_dec(v_a_1141_);
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1307_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1307_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1302_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__70);
v___x_1303_ = lean_string_append(v___x_1302_, v_a_1298_);
lean_dec(v_a_1298_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1303_);
v___x_1305_ = v___x_1300_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
else
{
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec(v_a_1294_);
lean_dec(v_a_1272_);
lean_dec(v_a_1250_);
lean_dec(v_a_1228_);
lean_dec(v_a_1207_);
lean_dec(v_a_1185_);
lean_dec(v_a_1163_);
lean_dec(v_a_1141_);
lean_dec(v_a_1119_);
lean_dec(v_a_1098_);
v_a_1308_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1297_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1297_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set_tag(v___x_1310_, 0);
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1324_; 
v_a_1316_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1318_ = v___x_1297_;
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1297_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1320_, 0, v_a_1098_);
lean_ctor_set(v___x_1320_, 1, v_a_1119_);
lean_ctor_set(v___x_1320_, 2, v_a_1141_);
lean_ctor_set(v___x_1320_, 3, v_a_1163_);
lean_ctor_set(v___x_1320_, 4, v_a_1185_);
lean_ctor_set(v___x_1320_, 5, v_a_1207_);
lean_ctor_set(v___x_1320_, 6, v_a_1228_);
lean_ctor_set(v___x_1320_, 7, v_a_1250_);
lean_ctor_set(v___x_1320_, 8, v_a_1272_);
lean_ctor_set(v___x_1320_, 9, v_a_1294_);
lean_ctor_set(v___x_1320_, 10, v_a_1316_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1320_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson(lean_object* v_00_u03b1_1325_, lean_object* v_inst_1326_, lean_object* v_json_1327_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg(v_inst_1326_, v_json_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith___redArg(lean_object* v_inst_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson), 3, 2);
lean_closure_set(v___x_1330_, 0, lean_box(0));
lean_closure_set(v___x_1330_, 1, v_inst_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith(lean_object* v_00_u03b1_1331_, lean_object* v_inst_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_alloc_closure((void*)(l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson), 3, 2);
lean_closure_set(v___x_1333_, 0, lean_box(0));
lean_closure_set(v___x_1333_, 1, v_inst_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg(lean_object* v_d_1334_){
_start:
{
lean_object* v_fullRange_x3f_1335_; 
v_fullRange_x3f_1335_ = lean_ctor_get(v_d_1334_, 1);
if (lean_obj_tag(v_fullRange_x3f_1335_) == 0)
{
lean_object* v_range_1336_; 
v_range_1336_ = lean_ctor_get(v_d_1334_, 0);
lean_inc_ref(v_range_1336_);
return v_range_1336_;
}
else
{
lean_object* v_val_1337_; 
v_val_1337_ = lean_ctor_get(v_fullRange_x3f_1335_, 0);
lean_inc(v_val_1337_);
return v_val_1337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg___boxed(lean_object* v_d_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d_1338_);
lean_dec_ref(v_d_1338_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange(lean_object* v_00_u03b1_1340_, lean_object* v_d_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(v_d_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___boxed(lean_object* v_00_u03b1_1343_, lean_object* v_d_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_Lsp_DiagnosticWith_fullRange(v_00_u03b1_1343_, v_d_1344_);
lean_dec_ref(v_d_1344_);
return v_res_1345_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(lean_object* v_x_1354_, lean_object* v_x_1355_){
_start:
{
if (lean_obj_tag(v_x_1354_) == 0)
{
if (lean_obj_tag(v_x_1355_) == 0)
{
uint8_t v___x_1356_; 
v___x_1356_ = 1;
return v___x_1356_;
}
else
{
uint8_t v___x_1357_; 
v___x_1357_ = 0;
return v___x_1357_;
}
}
else
{
if (lean_obj_tag(v_x_1355_) == 0)
{
uint8_t v___x_1358_; 
v___x_1358_ = 0;
return v___x_1358_;
}
else
{
lean_object* v_val_1359_; lean_object* v_val_1360_; uint8_t v___x_1361_; 
v_val_1359_ = lean_ctor_get(v_x_1354_, 0);
v_val_1360_ = lean_ctor_get(v_x_1355_, 0);
v___x_1361_ = lean_int_dec_eq(v_val_1359_, v_val_1360_);
return v___x_1361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0___boxed(lean_object* v_x_1362_, lean_object* v_x_1363_){
_start:
{
uint8_t v_res_1364_; lean_object* v_r_1365_; 
v_res_1364_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(v_x_1362_, v_x_1363_);
lean_dec(v_x_1363_);
lean_dec(v_x_1362_);
v_r_1365_ = lean_box(v_res_1364_);
return v_r_1365_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(lean_object* v_x_1366_, lean_object* v_x_1367_){
_start:
{
if (lean_obj_tag(v_x_1366_) == 0)
{
if (lean_obj_tag(v_x_1367_) == 0)
{
uint8_t v___x_1368_; 
v___x_1368_ = 1;
return v___x_1368_;
}
else
{
uint8_t v___x_1369_; 
v___x_1369_ = 0;
return v___x_1369_;
}
}
else
{
if (lean_obj_tag(v_x_1367_) == 0)
{
uint8_t v___x_1370_; 
v___x_1370_ = 0;
return v___x_1370_;
}
else
{
lean_object* v_val_1371_; uint8_t v___x_1372_; 
v_val_1371_ = lean_ctor_get(v_x_1366_, 0);
v___x_1372_ = lean_unbox(v_val_1371_);
if (v___x_1372_ == 0)
{
lean_object* v_val_1373_; uint8_t v___x_1374_; 
v_val_1373_ = lean_ctor_get(v_x_1367_, 0);
v___x_1374_ = lean_unbox(v_val_1373_);
if (v___x_1374_ == 0)
{
uint8_t v___x_1375_; 
v___x_1375_ = 1;
return v___x_1375_;
}
else
{
uint8_t v___x_1376_; 
v___x_1376_ = lean_unbox(v_val_1371_);
return v___x_1376_;
}
}
else
{
lean_object* v_val_1377_; uint8_t v___x_1378_; 
v_val_1377_ = lean_ctor_get(v_x_1367_, 0);
v___x_1378_ = lean_unbox(v_val_1377_);
return v___x_1378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1___boxed(lean_object* v_x_1379_, lean_object* v_x_1380_){
_start:
{
uint8_t v_res_1381_; lean_object* v_r_1382_; 
v_res_1381_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(v_x_1379_, v_x_1380_);
lean_dec(v_x_1380_);
lean_dec(v_x_1379_);
v_r_1382_ = lean_box(v_res_1381_);
return v_r_1382_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(lean_object* v_xs_1383_, lean_object* v_ys_1384_, lean_object* v_x_1385_){
_start:
{
lean_object* v_zero_1386_; uint8_t v_isZero_1387_; 
v_zero_1386_ = lean_unsigned_to_nat(0u);
v_isZero_1387_ = lean_nat_dec_eq(v_x_1385_, v_zero_1386_);
if (v_isZero_1387_ == 1)
{
lean_dec(v_x_1385_);
return v_isZero_1387_;
}
else
{
lean_object* v_one_1388_; lean_object* v_n_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v_one_1388_ = lean_unsigned_to_nat(1u);
v_n_1389_ = lean_nat_sub(v_x_1385_, v_one_1388_);
lean_dec(v_x_1385_);
v___x_1390_ = lean_array_fget_borrowed(v_xs_1383_, v_n_1389_);
v___x_1391_ = lean_array_fget_borrowed(v_ys_1384_, v_n_1389_);
v___x_1392_ = l_Lean_Lsp_instBEqDiagnosticRelatedInformation_beq(v___x_1390_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_dec(v_n_1389_);
return v___x_1392_;
}
else
{
v_x_1385_ = v_n_1389_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg___boxed(lean_object* v_xs_1394_, lean_object* v_ys_1395_, lean_object* v_x_1396_){
_start:
{
uint8_t v_res_1397_; lean_object* v_r_1398_; 
v_res_1397_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(v_xs_1394_, v_ys_1395_, v_x_1396_);
lean_dec_ref(v_ys_1395_);
lean_dec_ref(v_xs_1394_);
v_r_1398_ = lean_box(v_res_1397_);
return v_r_1398_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(lean_object* v_x_1399_, lean_object* v_x_1400_){
_start:
{
if (lean_obj_tag(v_x_1399_) == 0)
{
if (lean_obj_tag(v_x_1400_) == 0)
{
uint8_t v___x_1401_; 
v___x_1401_ = 1;
return v___x_1401_;
}
else
{
uint8_t v___x_1402_; 
v___x_1402_ = 0;
return v___x_1402_;
}
}
else
{
if (lean_obj_tag(v_x_1400_) == 0)
{
uint8_t v___x_1403_; 
v___x_1403_ = 0;
return v___x_1403_;
}
else
{
lean_object* v_val_1404_; lean_object* v_val_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v_val_1404_ = lean_ctor_get(v_x_1399_, 0);
v_val_1405_ = lean_ctor_get(v_x_1400_, 0);
v___x_1406_ = lean_array_get_size(v_val_1404_);
v___x_1407_ = lean_array_get_size(v_val_1405_);
v___x_1408_ = lean_nat_dec_eq(v___x_1406_, v___x_1407_);
if (v___x_1408_ == 0)
{
return v___x_1408_;
}
else
{
uint8_t v___x_1409_; 
v___x_1409_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(v_val_1404_, v_val_1405_, v___x_1406_);
return v___x_1409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8___boxed(lean_object* v_x_1410_, lean_object* v_x_1411_){
_start:
{
uint8_t v_res_1412_; lean_object* v_r_1413_; 
v_res_1412_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(v_x_1410_, v_x_1411_);
lean_dec(v_x_1411_);
lean_dec(v_x_1410_);
v_r_1413_ = lean_box(v_res_1412_);
return v_r_1413_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(lean_object* v_xs_1414_, lean_object* v_ys_1415_, lean_object* v_x_1416_){
_start:
{
lean_object* v_zero_1417_; uint8_t v_isZero_1418_; 
v_zero_1417_ = lean_unsigned_to_nat(0u);
v_isZero_1418_ = lean_nat_dec_eq(v_x_1416_, v_zero_1417_);
if (v_isZero_1418_ == 1)
{
lean_dec(v_x_1416_);
return v_isZero_1418_;
}
else
{
lean_object* v_one_1419_; lean_object* v_n_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; uint8_t v___x_1424_; uint8_t v___x_1425_; 
v_one_1419_ = lean_unsigned_to_nat(1u);
v_n_1420_ = lean_nat_sub(v_x_1416_, v_one_1419_);
lean_dec(v_x_1416_);
v___x_1421_ = lean_array_fget_borrowed(v_xs_1414_, v_n_1420_);
v___x_1422_ = lean_array_fget_borrowed(v_ys_1415_, v_n_1420_);
v___x_1423_ = lean_unbox(v___x_1421_);
v___x_1424_ = lean_unbox(v___x_1422_);
v___x_1425_ = l_Lean_Lsp_instBEqLeanDiagnosticTag_beq(v___x_1423_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_dec(v_n_1420_);
return v___x_1425_;
}
else
{
v_x_1416_ = v_n_1420_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg___boxed(lean_object* v_xs_1427_, lean_object* v_ys_1428_, lean_object* v_x_1429_){
_start:
{
uint8_t v_res_1430_; lean_object* v_r_1431_; 
v_res_1430_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(v_xs_1427_, v_ys_1428_, v_x_1429_);
lean_dec_ref(v_ys_1428_);
lean_dec_ref(v_xs_1427_);
v_r_1431_ = lean_box(v_res_1430_);
return v_r_1431_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(lean_object* v_x_1432_, lean_object* v_x_1433_){
_start:
{
if (lean_obj_tag(v_x_1432_) == 0)
{
if (lean_obj_tag(v_x_1433_) == 0)
{
uint8_t v___x_1434_; 
v___x_1434_ = 1;
return v___x_1434_;
}
else
{
uint8_t v___x_1435_; 
v___x_1435_ = 0;
return v___x_1435_;
}
}
else
{
if (lean_obj_tag(v_x_1433_) == 0)
{
uint8_t v___x_1436_; 
v___x_1436_ = 0;
return v___x_1436_;
}
else
{
lean_object* v_val_1437_; lean_object* v_val_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v_val_1437_ = lean_ctor_get(v_x_1432_, 0);
v_val_1438_ = lean_ctor_get(v_x_1433_, 0);
v___x_1439_ = lean_array_get_size(v_val_1437_);
v___x_1440_ = lean_array_get_size(v_val_1438_);
v___x_1441_ = lean_nat_dec_eq(v___x_1439_, v___x_1440_);
if (v___x_1441_ == 0)
{
return v___x_1441_;
}
else
{
uint8_t v___x_1442_; 
v___x_1442_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(v_val_1437_, v_val_1438_, v___x_1439_);
return v___x_1442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7___boxed(lean_object* v_x_1443_, lean_object* v_x_1444_){
_start:
{
uint8_t v_res_1445_; lean_object* v_r_1446_; 
v_res_1445_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(v_x_1443_, v_x_1444_);
lean_dec(v_x_1444_);
lean_dec(v_x_1443_);
v_r_1446_ = lean_box(v_res_1445_);
return v_r_1446_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(lean_object* v_x_1447_, lean_object* v_x_1448_){
_start:
{
if (lean_obj_tag(v_x_1447_) == 0)
{
if (lean_obj_tag(v_x_1448_) == 0)
{
uint8_t v___x_1449_; 
v___x_1449_ = 1;
return v___x_1449_;
}
else
{
uint8_t v___x_1450_; 
v___x_1450_ = 0;
return v___x_1450_;
}
}
else
{
if (lean_obj_tag(v_x_1448_) == 0)
{
uint8_t v___x_1451_; 
v___x_1451_ = 0;
return v___x_1451_;
}
else
{
lean_object* v_val_1452_; lean_object* v_val_1453_; uint8_t v___x_1454_; 
v_val_1452_ = lean_ctor_get(v_x_1447_, 0);
v_val_1453_ = lean_ctor_get(v_x_1448_, 0);
v___x_1454_ = l_Lean_Lsp_instBEqDiagnosticCode_beq(v_val_1452_, v_val_1453_);
return v___x_1454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4___boxed(lean_object* v_x_1455_, lean_object* v_x_1456_){
_start:
{
uint8_t v_res_1457_; lean_object* v_r_1458_; 
v_res_1457_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(v_x_1455_, v_x_1456_);
lean_dec(v_x_1456_);
lean_dec(v_x_1455_);
v_r_1458_ = lean_box(v_res_1457_);
return v_r_1458_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(lean_object* v_x_1459_, lean_object* v_x_1460_){
_start:
{
if (lean_obj_tag(v_x_1459_) == 0)
{
if (lean_obj_tag(v_x_1460_) == 0)
{
uint8_t v___x_1461_; 
v___x_1461_ = 1;
return v___x_1461_;
}
else
{
uint8_t v___x_1462_; 
v___x_1462_ = 0;
return v___x_1462_;
}
}
else
{
if (lean_obj_tag(v_x_1460_) == 0)
{
uint8_t v___x_1463_; 
v___x_1463_ = 0;
return v___x_1463_;
}
else
{
lean_object* v_val_1464_; lean_object* v_val_1465_; uint8_t v___x_1466_; 
v_val_1464_ = lean_ctor_get(v_x_1459_, 0);
v_val_1465_ = lean_ctor_get(v_x_1460_, 0);
v___x_1466_ = l_Lean_Lsp_instBEqRange_beq(v_val_1464_, v_val_1465_);
return v___x_1466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2___boxed(lean_object* v_x_1467_, lean_object* v_x_1468_){
_start:
{
uint8_t v_res_1469_; lean_object* v_r_1470_; 
v_res_1469_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(v_x_1467_, v_x_1468_);
lean_dec(v_x_1468_);
lean_dec(v_x_1467_);
v_r_1470_ = lean_box(v_res_1469_);
return v_r_1470_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(lean_object* v_x_1471_, lean_object* v_x_1472_){
_start:
{
if (lean_obj_tag(v_x_1471_) == 0)
{
if (lean_obj_tag(v_x_1472_) == 0)
{
uint8_t v___x_1473_; 
v___x_1473_ = 1;
return v___x_1473_;
}
else
{
uint8_t v___x_1474_; 
v___x_1474_ = 0;
return v___x_1474_;
}
}
else
{
if (lean_obj_tag(v_x_1472_) == 0)
{
uint8_t v___x_1475_; 
v___x_1475_ = 0;
return v___x_1475_;
}
else
{
lean_object* v_val_1476_; lean_object* v_val_1477_; uint8_t v___x_1478_; 
v_val_1476_ = lean_ctor_get(v_x_1471_, 0);
v_val_1477_ = lean_ctor_get(v_x_1472_, 0);
v___x_1478_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_val_1476_, v_val_1477_);
return v___x_1478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9___boxed(lean_object* v_x_1479_, lean_object* v_x_1480_){
_start:
{
uint8_t v_res_1481_; lean_object* v_r_1482_; 
v_res_1481_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(v_x_1479_, v_x_1480_);
lean_dec(v_x_1480_);
lean_dec(v_x_1479_);
v_r_1482_ = lean_box(v_res_1481_);
return v_r_1482_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(lean_object* v_x_1483_, lean_object* v_x_1484_){
_start:
{
if (lean_obj_tag(v_x_1483_) == 0)
{
if (lean_obj_tag(v_x_1484_) == 0)
{
uint8_t v___x_1485_; 
v___x_1485_ = 1;
return v___x_1485_;
}
else
{
uint8_t v___x_1486_; 
v___x_1486_ = 0;
return v___x_1486_;
}
}
else
{
if (lean_obj_tag(v_x_1484_) == 0)
{
uint8_t v___x_1487_; 
v___x_1487_ = 0;
return v___x_1487_;
}
else
{
lean_object* v_val_1488_; lean_object* v_val_1489_; uint8_t v___x_1490_; 
v_val_1488_ = lean_ctor_get(v_x_1483_, 0);
v_val_1489_ = lean_ctor_get(v_x_1484_, 0);
v___x_1490_ = lean_string_dec_eq(v_val_1488_, v_val_1489_);
return v___x_1490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5___boxed(lean_object* v_x_1491_, lean_object* v_x_1492_){
_start:
{
uint8_t v_res_1493_; lean_object* v_r_1494_; 
v_res_1493_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(v_x_1491_, v_x_1492_);
lean_dec(v_x_1492_);
lean_dec(v_x_1491_);
v_r_1494_ = lean_box(v_res_1493_);
return v_r_1494_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(lean_object* v_xs_1495_, lean_object* v_ys_1496_, lean_object* v_x_1497_){
_start:
{
lean_object* v_zero_1498_; uint8_t v_isZero_1499_; 
v_zero_1498_ = lean_unsigned_to_nat(0u);
v_isZero_1499_ = lean_nat_dec_eq(v_x_1497_, v_zero_1498_);
if (v_isZero_1499_ == 1)
{
lean_dec(v_x_1497_);
return v_isZero_1499_;
}
else
{
lean_object* v_one_1500_; lean_object* v_n_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; uint8_t v___x_1505_; uint8_t v___x_1506_; 
v_one_1500_ = lean_unsigned_to_nat(1u);
v_n_1501_ = lean_nat_sub(v_x_1497_, v_one_1500_);
lean_dec(v_x_1497_);
v___x_1502_ = lean_array_fget_borrowed(v_xs_1495_, v_n_1501_);
v___x_1503_ = lean_array_fget_borrowed(v_ys_1496_, v_n_1501_);
v___x_1504_ = lean_unbox(v___x_1502_);
v___x_1505_ = lean_unbox(v___x_1503_);
v___x_1506_ = l_Lean_Lsp_instBEqDiagnosticTag_beq(v___x_1504_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_dec(v_n_1501_);
return v___x_1506_;
}
else
{
v_x_1497_ = v_n_1501_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg___boxed(lean_object* v_xs_1508_, lean_object* v_ys_1509_, lean_object* v_x_1510_){
_start:
{
uint8_t v_res_1511_; lean_object* v_r_1512_; 
v_res_1511_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(v_xs_1508_, v_ys_1509_, v_x_1510_);
lean_dec_ref(v_ys_1509_);
lean_dec_ref(v_xs_1508_);
v_r_1512_ = lean_box(v_res_1511_);
return v_r_1512_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(lean_object* v_x_1513_, lean_object* v_x_1514_){
_start:
{
if (lean_obj_tag(v_x_1513_) == 0)
{
if (lean_obj_tag(v_x_1514_) == 0)
{
uint8_t v___x_1515_; 
v___x_1515_ = 1;
return v___x_1515_;
}
else
{
uint8_t v___x_1516_; 
v___x_1516_ = 0;
return v___x_1516_;
}
}
else
{
if (lean_obj_tag(v_x_1514_) == 0)
{
uint8_t v___x_1517_; 
v___x_1517_ = 0;
return v___x_1517_;
}
else
{
lean_object* v_val_1518_; lean_object* v_val_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; 
v_val_1518_ = lean_ctor_get(v_x_1513_, 0);
v_val_1519_ = lean_ctor_get(v_x_1514_, 0);
v___x_1520_ = lean_array_get_size(v_val_1518_);
v___x_1521_ = lean_array_get_size(v_val_1519_);
v___x_1522_ = lean_nat_dec_eq(v___x_1520_, v___x_1521_);
if (v___x_1522_ == 0)
{
return v___x_1522_;
}
else
{
uint8_t v___x_1523_; 
v___x_1523_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(v_val_1518_, v_val_1519_, v___x_1520_);
return v___x_1523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6___boxed(lean_object* v_x_1524_, lean_object* v_x_1525_){
_start:
{
uint8_t v_res_1526_; lean_object* v_r_1527_; 
v_res_1526_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(v_x_1524_, v_x_1525_);
lean_dec(v_x_1525_);
lean_dec(v_x_1524_);
v_r_1527_ = lean_box(v_res_1526_);
return v_r_1527_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(lean_object* v_x_1528_, lean_object* v_x_1529_){
_start:
{
if (lean_obj_tag(v_x_1528_) == 0)
{
if (lean_obj_tag(v_x_1529_) == 0)
{
uint8_t v___x_1530_; 
v___x_1530_ = 1;
return v___x_1530_;
}
else
{
uint8_t v___x_1531_; 
v___x_1531_ = 0;
return v___x_1531_;
}
}
else
{
if (lean_obj_tag(v_x_1529_) == 0)
{
uint8_t v___x_1532_; 
v___x_1532_ = 0;
return v___x_1532_;
}
else
{
lean_object* v_val_1533_; lean_object* v_val_1534_; uint8_t v___x_1535_; uint8_t v___x_1536_; uint8_t v___x_1537_; 
v_val_1533_ = lean_ctor_get(v_x_1528_, 0);
v_val_1534_ = lean_ctor_get(v_x_1529_, 0);
v___x_1535_ = lean_unbox(v_val_1533_);
v___x_1536_ = lean_unbox(v_val_1534_);
v___x_1537_ = l_Lean_Lsp_instBEqDiagnosticSeverity_beq(v___x_1535_, v___x_1536_);
return v___x_1537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3___boxed(lean_object* v_x_1538_, lean_object* v_x_1539_){
_start:
{
uint8_t v_res_1540_; lean_object* v_r_1541_; 
v_res_1540_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(v_x_1538_, v_x_1539_);
lean_dec(v_x_1539_);
lean_dec(v_x_1538_);
v_r_1541_ = lean_box(v_res_1540_);
return v_r_1541_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(lean_object* v_x_1542_, lean_object* v_x_1543_){
_start:
{
lean_object* v_range_1544_; lean_object* v_fullRange_x3f_1545_; lean_object* v_severity_x3f_1546_; lean_object* v_isSilent_x3f_1547_; lean_object* v_code_x3f_1548_; lean_object* v_source_x3f_1549_; lean_object* v_message_1550_; lean_object* v_tags_x3f_1551_; lean_object* v_leanTags_x3f_1552_; lean_object* v_relatedInformation_x3f_1553_; lean_object* v_data_x3f_1554_; lean_object* v_range_1555_; lean_object* v_fullRange_x3f_1556_; lean_object* v_severity_x3f_1557_; lean_object* v_isSilent_x3f_1558_; lean_object* v_code_x3f_1559_; lean_object* v_source_x3f_1560_; lean_object* v_message_1561_; lean_object* v_tags_x3f_1562_; lean_object* v_leanTags_x3f_1563_; lean_object* v_relatedInformation_x3f_1564_; lean_object* v_data_x3f_1565_; uint8_t v___x_1566_; 
v_range_1544_ = lean_ctor_get(v_x_1542_, 0);
v_fullRange_x3f_1545_ = lean_ctor_get(v_x_1542_, 1);
v_severity_x3f_1546_ = lean_ctor_get(v_x_1542_, 2);
v_isSilent_x3f_1547_ = lean_ctor_get(v_x_1542_, 3);
v_code_x3f_1548_ = lean_ctor_get(v_x_1542_, 4);
v_source_x3f_1549_ = lean_ctor_get(v_x_1542_, 5);
v_message_1550_ = lean_ctor_get(v_x_1542_, 6);
v_tags_x3f_1551_ = lean_ctor_get(v_x_1542_, 7);
v_leanTags_x3f_1552_ = lean_ctor_get(v_x_1542_, 8);
v_relatedInformation_x3f_1553_ = lean_ctor_get(v_x_1542_, 9);
v_data_x3f_1554_ = lean_ctor_get(v_x_1542_, 10);
v_range_1555_ = lean_ctor_get(v_x_1543_, 0);
v_fullRange_x3f_1556_ = lean_ctor_get(v_x_1543_, 1);
v_severity_x3f_1557_ = lean_ctor_get(v_x_1543_, 2);
v_isSilent_x3f_1558_ = lean_ctor_get(v_x_1543_, 3);
v_code_x3f_1559_ = lean_ctor_get(v_x_1543_, 4);
v_source_x3f_1560_ = lean_ctor_get(v_x_1543_, 5);
v_message_1561_ = lean_ctor_get(v_x_1543_, 6);
v_tags_x3f_1562_ = lean_ctor_get(v_x_1543_, 7);
v_leanTags_x3f_1563_ = lean_ctor_get(v_x_1543_, 8);
v_relatedInformation_x3f_1564_ = lean_ctor_get(v_x_1543_, 9);
v_data_x3f_1565_ = lean_ctor_get(v_x_1543_, 10);
v___x_1566_ = l_Lean_Lsp_instBEqRange_beq(v_range_1544_, v_range_1555_);
if (v___x_1566_ == 0)
{
return v___x_1566_;
}
else
{
uint8_t v___x_1567_; 
v___x_1567_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__2(v_fullRange_x3f_1545_, v_fullRange_x3f_1556_);
if (v___x_1567_ == 0)
{
return v___x_1567_;
}
else
{
uint8_t v___x_1568_; 
v___x_1568_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__3(v_severity_x3f_1546_, v_severity_x3f_1557_);
if (v___x_1568_ == 0)
{
return v___x_1568_;
}
else
{
uint8_t v___x_1569_; 
v___x_1569_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(v_isSilent_x3f_1547_, v_isSilent_x3f_1558_);
if (v___x_1569_ == 0)
{
return v___x_1569_;
}
else
{
uint8_t v___x_1570_; 
v___x_1570_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__4(v_code_x3f_1548_, v_code_x3f_1559_);
if (v___x_1570_ == 0)
{
return v___x_1570_;
}
else
{
uint8_t v___x_1571_; 
v___x_1571_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__5(v_source_x3f_1549_, v_source_x3f_1560_);
if (v___x_1571_ == 0)
{
return v___x_1571_;
}
else
{
uint8_t v___x_1572_; 
v___x_1572_ = lean_string_dec_eq(v_message_1550_, v_message_1561_);
if (v___x_1572_ == 0)
{
return v___x_1572_;
}
else
{
uint8_t v___x_1573_; 
v___x_1573_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6(v_tags_x3f_1551_, v_tags_x3f_1562_);
if (v___x_1573_ == 0)
{
return v___x_1573_;
}
else
{
uint8_t v___x_1574_; 
v___x_1574_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7(v_leanTags_x3f_1552_, v_leanTags_x3f_1563_);
if (v___x_1574_ == 0)
{
return v___x_1574_;
}
else
{
uint8_t v___x_1575_; 
v___x_1575_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8(v_relatedInformation_x3f_1553_, v_relatedInformation_x3f_1564_);
if (v___x_1575_ == 0)
{
return v___x_1575_;
}
else
{
uint8_t v___x_1576_; 
v___x_1576_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__9(v_data_x3f_1554_, v_data_x3f_1565_);
return v___x_1576_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2___boxed(lean_object* v_x_1577_, lean_object* v_x_1578_){
_start:
{
uint8_t v_res_1579_; lean_object* v_r_1580_; 
v_res_1579_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(v_x_1577_, v_x_1578_);
lean_dec_ref(v_x_1578_);
lean_dec_ref(v_x_1577_);
v_r_1580_ = lean_box(v_res_1579_);
return v_r_1580_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(lean_object* v_xs_1581_, lean_object* v_ys_1582_, lean_object* v_x_1583_){
_start:
{
lean_object* v_zero_1584_; uint8_t v_isZero_1585_; 
v_zero_1584_ = lean_unsigned_to_nat(0u);
v_isZero_1585_ = lean_nat_dec_eq(v_x_1583_, v_zero_1584_);
if (v_isZero_1585_ == 1)
{
lean_dec(v_x_1583_);
return v_isZero_1585_;
}
else
{
lean_object* v_one_1586_; lean_object* v_n_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v_one_1586_ = lean_unsigned_to_nat(1u);
v_n_1587_ = lean_nat_sub(v_x_1583_, v_one_1586_);
lean_dec(v_x_1583_);
v___x_1588_ = lean_array_fget_borrowed(v_xs_1581_, v_n_1587_);
v___x_1589_ = lean_array_fget_borrowed(v_ys_1582_, v_n_1587_);
v___x_1590_ = l_Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2(v___x_1588_, v___x_1589_);
if (v___x_1590_ == 0)
{
lean_dec(v_n_1587_);
return v___x_1590_;
}
else
{
v_x_1583_ = v_n_1587_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg___boxed(lean_object* v_xs_1592_, lean_object* v_ys_1593_, lean_object* v_x_1594_){
_start:
{
uint8_t v_res_1595_; lean_object* v_r_1596_; 
v_res_1595_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(v_xs_1592_, v_ys_1593_, v_x_1594_);
lean_dec_ref(v_ys_1593_);
lean_dec_ref(v_xs_1592_);
v_r_1596_ = lean_box(v_res_1595_);
return v_r_1596_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq(lean_object* v_x_1597_, lean_object* v_x_1598_){
_start:
{
lean_object* v_uri_1599_; lean_object* v_version_x3f_1600_; lean_object* v_isIncremental_x3f_1601_; lean_object* v_diagnostics_1602_; lean_object* v_uri_1603_; lean_object* v_version_x3f_1604_; lean_object* v_isIncremental_x3f_1605_; lean_object* v_diagnostics_1606_; uint8_t v___x_1607_; 
v_uri_1599_ = lean_ctor_get(v_x_1597_, 0);
v_version_x3f_1600_ = lean_ctor_get(v_x_1597_, 1);
v_isIncremental_x3f_1601_ = lean_ctor_get(v_x_1597_, 2);
v_diagnostics_1602_ = lean_ctor_get(v_x_1597_, 3);
v_uri_1603_ = lean_ctor_get(v_x_1598_, 0);
v_version_x3f_1604_ = lean_ctor_get(v_x_1598_, 1);
v_isIncremental_x3f_1605_ = lean_ctor_get(v_x_1598_, 2);
v_diagnostics_1606_ = lean_ctor_get(v_x_1598_, 3);
v___x_1607_ = lean_string_dec_eq(v_uri_1599_, v_uri_1603_);
if (v___x_1607_ == 0)
{
return v___x_1607_;
}
else
{
uint8_t v___x_1608_; 
v___x_1608_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__0(v_version_x3f_1600_, v_version_x3f_1604_);
if (v___x_1608_ == 0)
{
return v___x_1608_;
}
else
{
uint8_t v___x_1609_; 
v___x_1609_ = l_Option_instBEq_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__1(v_isIncremental_x3f_1601_, v_isIncremental_x3f_1605_);
if (v___x_1609_ == 0)
{
return v___x_1609_;
}
else
{
lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1610_ = lean_array_get_size(v_diagnostics_1602_);
v___x_1611_ = lean_array_get_size(v_diagnostics_1606_);
v___x_1612_ = lean_nat_dec_eq(v___x_1610_, v___x_1611_);
if (v___x_1612_ == 0)
{
return v___x_1612_;
}
else
{
uint8_t v___x_1613_; 
v___x_1613_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(v_diagnostics_1602_, v_diagnostics_1606_, v___x_1610_);
return v___x_1613_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq___boxed(lean_object* v_x_1614_, lean_object* v_x_1615_){
_start:
{
uint8_t v_res_1616_; lean_object* v_r_1617_; 
v_res_1616_ = l_Lean_Lsp_instBEqPublishDiagnosticsParams_beq(v_x_1614_, v_x_1615_);
lean_dec_ref(v_x_1615_);
lean_dec_ref(v_x_1614_);
v_r_1617_ = lean_box(v_res_1616_);
return v_r_1617_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3(lean_object* v_xs_1618_, lean_object* v_ys_1619_, lean_object* v_hsz_1620_, lean_object* v_x_1621_, lean_object* v_x_1622_){
_start:
{
uint8_t v___x_1623_; 
v___x_1623_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___redArg(v_xs_1618_, v_ys_1619_, v_x_1621_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3___boxed(lean_object* v_xs_1624_, lean_object* v_ys_1625_, lean_object* v_hsz_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_){
_start:
{
uint8_t v_res_1629_; lean_object* v_r_1630_; 
v_res_1629_ = l_Array_isEqvAux___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__3(v_xs_1624_, v_ys_1625_, v_hsz_1626_, v_x_1627_, v_x_1628_);
lean_dec_ref(v_ys_1625_);
lean_dec_ref(v_xs_1624_);
v_r_1630_ = lean_box(v_res_1629_);
return v_r_1630_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7(lean_object* v_xs_1631_, lean_object* v_ys_1632_, lean_object* v_hsz_1633_, lean_object* v_x_1634_, lean_object* v_x_1635_){
_start:
{
uint8_t v___x_1636_; 
v___x_1636_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___redArg(v_xs_1631_, v_ys_1632_, v_x_1634_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7___boxed(lean_object* v_xs_1637_, lean_object* v_ys_1638_, lean_object* v_hsz_1639_, lean_object* v_x_1640_, lean_object* v_x_1641_){
_start:
{
uint8_t v_res_1642_; lean_object* v_r_1643_; 
v_res_1642_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__6_spec__7(v_xs_1637_, v_ys_1638_, v_hsz_1639_, v_x_1640_, v_x_1641_);
lean_dec_ref(v_ys_1638_);
lean_dec_ref(v_xs_1637_);
v_r_1643_ = lean_box(v_res_1642_);
return v_r_1643_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9(lean_object* v_xs_1644_, lean_object* v_ys_1645_, lean_object* v_hsz_1646_, lean_object* v_x_1647_, lean_object* v_x_1648_){
_start:
{
uint8_t v___x_1649_; 
v___x_1649_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___redArg(v_xs_1644_, v_ys_1645_, v_x_1647_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9___boxed(lean_object* v_xs_1650_, lean_object* v_ys_1651_, lean_object* v_hsz_1652_, lean_object* v_x_1653_, lean_object* v_x_1654_){
_start:
{
uint8_t v_res_1655_; lean_object* v_r_1656_; 
v_res_1655_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__7_spec__9(v_xs_1650_, v_ys_1651_, v_hsz_1652_, v_x_1653_, v_x_1654_);
lean_dec_ref(v_ys_1651_);
lean_dec_ref(v_xs_1650_);
v_r_1656_ = lean_box(v_res_1655_);
return v_r_1656_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11(lean_object* v_xs_1657_, lean_object* v_ys_1658_, lean_object* v_hsz_1659_, lean_object* v_x_1660_, lean_object* v_x_1661_){
_start:
{
uint8_t v___x_1662_; 
v___x_1662_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___redArg(v_xs_1657_, v_ys_1658_, v_x_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11___boxed(lean_object* v_xs_1663_, lean_object* v_ys_1664_, lean_object* v_hsz_1665_, lean_object* v_x_1666_, lean_object* v_x_1667_){
_start:
{
uint8_t v_res_1668_; lean_object* v_r_1669_; 
v_res_1668_ = l_Array_isEqvAux___at___00Option_instBEq_beq___at___00Lean_Lsp_instBEqDiagnosticWith_beq___at___00Lean_Lsp_instBEqPublishDiagnosticsParams_beq_spec__2_spec__8_spec__11(v_xs_1663_, v_ys_1664_, v_hsz_1665_, v_x_1666_, v_x_1667_);
lean_dec_ref(v_ys_1664_);
lean_dec_ref(v_xs_1663_);
v_r_1669_ = lean_box(v_res_1668_);
return v_r_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__0(lean_object* v_k_1672_, lean_object* v_x_1673_){
_start:
{
if (lean_obj_tag(v_x_1673_) == 0)
{
lean_object* v___x_1674_; 
lean_dec_ref(v_k_1672_);
v___x_1674_ = lean_box(0);
return v___x_1674_;
}
else
{
lean_object* v_val_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1686_; 
v_val_1675_ = lean_ctor_get(v_x_1673_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_x_1673_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1677_ = v_x_1673_;
v_isShared_1678_ = v_isSharedCheck_1686_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_val_1675_);
lean_dec(v_x_1673_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1686_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = l_Lean_JsonNumber_fromInt(v_val_1675_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set_tag(v___x_1677_, 2);
lean_ctor_set(v___x_1677_, 0, v___x_1679_);
v___x_1681_ = v___x_1677_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v_k_1672_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = lean_box(0);
v___x_1684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1682_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
return v___x_1684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(lean_object* v_k_1687_, lean_object* v_x_1688_){
_start:
{
if (lean_obj_tag(v_x_1688_) == 0)
{
lean_object* v___x_1689_; 
lean_dec_ref(v_k_1687_);
v___x_1689_ = lean_box(0);
return v___x_1689_;
}
else
{
lean_object* v_val_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v_val_1690_ = lean_ctor_get(v_x_1688_, 0);
v___x_1691_ = lean_alloc_ctor(1, 0, 1);
v___x_1692_ = lean_unbox(v_val_1690_);
lean_ctor_set_uint8(v___x_1691_, 0, v___x_1692_);
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v_k_1687_);
lean_ctor_set(v___x_1693_, 1, v___x_1691_);
v___x_1694_ = lean_box(0);
v___x_1695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1693_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
return v___x_1695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1___boxed(lean_object* v_k_1696_, lean_object* v_x_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(v_k_1696_, v_x_1697_);
lean_dec(v_x_1697_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(lean_object* v_k_1699_, lean_object* v_x_1700_){
_start:
{
if (lean_obj_tag(v_x_1700_) == 0)
{
lean_object* v___x_1701_; 
lean_dec_ref(v_k_1699_);
v___x_1701_ = lean_box(0);
return v___x_1701_;
}
else
{
lean_object* v_val_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_val_1702_ = lean_ctor_get(v_x_1700_, 0);
lean_inc(v_val_1702_);
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v_k_1699_);
lean_ctor_set(v___x_1703_, 1, v_val_1702_);
v___x_1704_ = lean_box(0);
v___x_1705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
return v___x_1705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10___boxed(lean_object* v_k_1706_, lean_object* v_x_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(v_k_1706_, v_x_1707_);
lean_dec(v_x_1707_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__5(lean_object* v_k_1709_, lean_object* v_x_1710_){
_start:
{
lean_object* v___y_1712_; 
if (lean_obj_tag(v_x_1710_) == 0)
{
lean_object* v___x_1716_; 
lean_dec_ref(v_k_1709_);
v___x_1716_ = lean_box(0);
return v___x_1716_;
}
else
{
lean_object* v_val_1717_; 
v_val_1717_ = lean_ctor_get(v_x_1710_, 0);
lean_inc(v_val_1717_);
lean_dec_ref(v_x_1710_);
if (lean_obj_tag(v_val_1717_) == 0)
{
lean_object* v_i_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1726_; 
v_i_1718_ = lean_ctor_get(v_val_1717_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_val_1717_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1720_ = v_val_1717_;
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_i_1718_);
lean_dec(v_val_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1722_ = l_Lean_JsonNumber_fromInt(v_i_1718_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set_tag(v___x_1720_, 2);
lean_ctor_set(v___x_1720_, 0, v___x_1722_);
v___x_1724_ = v___x_1720_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
v___y_1712_ = v___x_1724_;
goto v___jp_1711_;
}
}
}
else
{
lean_object* v_s_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
v_s_1727_ = lean_ctor_get(v_val_1717_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_val_1717_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v_val_1717_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_s_1727_);
lean_dec(v_val_1717_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set_tag(v___x_1729_, 3);
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_s_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
v___y_1712_ = v___x_1732_;
goto v___jp_1711_;
}
}
}
}
v___jp_1711_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v_k_1709_);
lean_ctor_set(v___x_1713_, 1, v___y_1712_);
v___x_1714_ = lean_box(0);
v___x_1715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1713_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
return v___x_1715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__6(lean_object* v_k_1735_, lean_object* v_x_1736_){
_start:
{
if (lean_obj_tag(v_x_1736_) == 0)
{
lean_object* v___x_1737_; 
lean_dec_ref(v_k_1735_);
v___x_1737_ = lean_box(0);
return v___x_1737_;
}
else
{
lean_object* v_val_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1748_; 
v_val_1738_ = lean_ctor_get(v_x_1736_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_x_1736_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1740_ = v_x_1736_;
v_isShared_1741_ = v_isSharedCheck_1748_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_val_1738_);
lean_dec(v_x_1736_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1748_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set_tag(v___x_1740_, 3);
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_val_1738_);
v___x_1743_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1744_, 0, v_k_1735_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = lean_box(0);
v___x_1746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1744_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
return v___x_1746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(size_t v_sz_1749_, size_t v_i_1750_, lean_object* v_bs_1751_){
_start:
{
uint8_t v___x_1752_; 
v___x_1752_ = lean_usize_dec_lt(v_i_1750_, v_sz_1749_);
if (v___x_1752_ == 0)
{
return v_bs_1751_;
}
else
{
lean_object* v_v_1753_; lean_object* v___x_1754_; lean_object* v_bs_x27_1755_; lean_object* v___y_1757_; uint8_t v___x_1762_; 
v_v_1753_ = lean_array_uget(v_bs_1751_, v_i_1750_);
v___x_1754_ = lean_unsigned_to_nat(0u);
v_bs_x27_1755_ = lean_array_uset(v_bs_1751_, v_i_1750_, v___x_1754_);
v___x_1762_ = lean_unbox(v_v_1753_);
lean_dec(v_v_1753_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; 
v___x_1763_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
v___y_1757_ = v___x_1763_;
goto v___jp_1756_;
}
else
{
lean_object* v___x_1764_; 
v___x_1764_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
v___y_1757_ = v___x_1764_;
goto v___jp_1756_;
}
v___jp_1756_:
{
size_t v___x_1758_; size_t v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = ((size_t)1ULL);
v___x_1759_ = lean_usize_add(v_i_1750_, v___x_1758_);
lean_inc(v___y_1757_);
v___x_1760_ = lean_array_uset(v_bs_x27_1755_, v_i_1750_, v___y_1757_);
v_i_1750_ = v___x_1759_;
v_bs_1751_ = v___x_1760_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14___boxed(lean_object* v_sz_1765_, lean_object* v_i_1766_, lean_object* v_bs_1767_){
_start:
{
size_t v_sz_boxed_1768_; size_t v_i_boxed_1769_; lean_object* v_res_1770_; 
v_sz_boxed_1768_ = lean_unbox_usize(v_sz_1765_);
lean_dec(v_sz_1765_);
v_i_boxed_1769_ = lean_unbox_usize(v_i_1766_);
lean_dec(v_i_1766_);
v_res_1770_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(v_sz_boxed_1768_, v_i_boxed_1769_, v_bs_1767_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10(lean_object* v_a_1771_){
_start:
{
size_t v_sz_1772_; size_t v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_sz_1772_ = lean_array_size(v_a_1771_);
v___x_1773_ = ((size_t)0ULL);
v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10_spec__14(v_sz_1772_, v___x_1773_, v_a_1771_);
v___x_1775_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8(lean_object* v_k_1776_, lean_object* v_x_1777_){
_start:
{
if (lean_obj_tag(v_x_1777_) == 0)
{
lean_object* v___x_1778_; 
lean_dec_ref(v_k_1776_);
v___x_1778_ = lean_box(0);
return v___x_1778_;
}
else
{
lean_object* v_val_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_val_1779_ = lean_ctor_get(v_x_1777_, 0);
lean_inc(v_val_1779_);
lean_dec_ref(v_x_1777_);
v___x_1780_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8_spec__10(v_val_1779_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v_k_1776_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = lean_box(0);
v___x_1783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
return v___x_1783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(lean_object* v_k_1784_, lean_object* v_x_1785_){
_start:
{
lean_object* v___y_1787_; 
if (lean_obj_tag(v_x_1785_) == 0)
{
lean_object* v___x_1791_; 
lean_dec_ref(v_k_1784_);
v___x_1791_ = lean_box(0);
return v___x_1791_;
}
else
{
lean_object* v_val_1792_; uint8_t v___x_1793_; 
v_val_1792_ = lean_ctor_get(v_x_1785_, 0);
v___x_1793_ = lean_unbox(v_val_1792_);
switch(v___x_1793_)
{
case 0:
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
v___y_1787_ = v___x_1794_;
goto v___jp_1786_;
}
case 1:
{
lean_object* v___x_1795_; 
v___x_1795_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
v___y_1787_ = v___x_1795_;
goto v___jp_1786_;
}
case 2:
{
lean_object* v___x_1796_; 
v___x_1796_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__5);
v___y_1787_ = v___x_1796_;
goto v___jp_1786_;
}
default: 
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__7);
v___y_1787_ = v___x_1797_;
goto v___jp_1786_;
}
}
}
v___jp_1786_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_inc(v___y_1787_);
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v_k_1784_);
lean_ctor_set(v___x_1788_, 1, v___y_1787_);
v___x_1789_ = lean_box(0);
v___x_1790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1788_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
return v___x_1790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4___boxed(lean_object* v_k_1798_, lean_object* v_x_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(v_k_1798_, v_x_1799_);
lean_dec(v_x_1799_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(size_t v_sz_1801_, size_t v_i_1802_, lean_object* v_bs_1803_){
_start:
{
uint8_t v___x_1804_; 
v___x_1804_ = lean_usize_dec_lt(v_i_1802_, v_sz_1801_);
if (v___x_1804_ == 0)
{
return v_bs_1803_;
}
else
{
lean_object* v_v_1805_; lean_object* v___x_1806_; lean_object* v_bs_x27_1807_; lean_object* v___x_1808_; size_t v___x_1809_; size_t v___x_1810_; lean_object* v___x_1811_; 
v_v_1805_ = lean_array_uget(v_bs_1803_, v_i_1802_);
v___x_1806_ = lean_unsigned_to_nat(0u);
v_bs_x27_1807_ = lean_array_uset(v_bs_1803_, v_i_1802_, v___x_1806_);
v___x_1808_ = l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson(v_v_1805_);
v___x_1809_ = ((size_t)1ULL);
v___x_1810_ = lean_usize_add(v_i_1802_, v___x_1809_);
v___x_1811_ = lean_array_uset(v_bs_x27_1807_, v_i_1802_, v___x_1808_);
v_i_1802_ = v___x_1810_;
v_bs_1803_ = v___x_1811_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17___boxed(lean_object* v_sz_1813_, lean_object* v_i_1814_, lean_object* v_bs_1815_){
_start:
{
size_t v_sz_boxed_1816_; size_t v_i_boxed_1817_; lean_object* v_res_1818_; 
v_sz_boxed_1816_ = lean_unbox_usize(v_sz_1813_);
lean_dec(v_sz_1813_);
v_i_boxed_1817_ = lean_unbox_usize(v_i_1814_);
lean_dec(v_i_1814_);
v_res_1818_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(v_sz_boxed_1816_, v_i_boxed_1817_, v_bs_1815_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12(lean_object* v_a_1819_){
_start:
{
size_t v_sz_1820_; size_t v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_sz_1820_ = lean_array_size(v_a_1819_);
v___x_1821_ = ((size_t)0ULL);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12_spec__17(v_sz_1820_, v___x_1821_, v_a_1819_);
v___x_1823_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9(lean_object* v_k_1824_, lean_object* v_x_1825_){
_start:
{
if (lean_obj_tag(v_x_1825_) == 0)
{
lean_object* v___x_1826_; 
lean_dec_ref(v_k_1824_);
v___x_1826_ = lean_box(0);
return v___x_1826_;
}
else
{
lean_object* v_val_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v_val_1827_ = lean_ctor_get(v_x_1825_, 0);
lean_inc(v_val_1827_);
lean_dec_ref(v_x_1825_);
v___x_1828_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9_spec__12(v_val_1827_);
v___x_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1829_, 0, v_k_1824_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = lean_box(0);
v___x_1831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1829_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
return v___x_1831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(size_t v_sz_1832_, size_t v_i_1833_, lean_object* v_bs_1834_){
_start:
{
uint8_t v___x_1835_; 
v___x_1835_ = lean_usize_dec_lt(v_i_1833_, v_sz_1832_);
if (v___x_1835_ == 0)
{
return v_bs_1834_;
}
else
{
lean_object* v_v_1836_; lean_object* v___x_1837_; lean_object* v_bs_x27_1838_; lean_object* v___y_1840_; uint8_t v___x_1845_; 
v_v_1836_ = lean_array_uget(v_bs_1834_, v_i_1833_);
v___x_1837_ = lean_unsigned_to_nat(0u);
v_bs_x27_1838_ = lean_array_uset(v_bs_1834_, v_i_1833_, v___x_1837_);
v___x_1845_ = lean_unbox(v_v_1836_);
lean_dec(v_v_1836_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; 
v___x_1846_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__1);
v___y_1840_ = v___x_1846_;
goto v___jp_1839_;
}
else
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_obj_once(&l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3, &l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonDiagnosticSeverity___lam__0___closed__3);
v___y_1840_ = v___x_1847_;
goto v___jp_1839_;
}
v___jp_1839_:
{
size_t v___x_1841_; size_t v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = ((size_t)1ULL);
v___x_1842_ = lean_usize_add(v_i_1833_, v___x_1841_);
lean_inc(v___y_1840_);
v___x_1843_ = lean_array_uset(v_bs_x27_1838_, v_i_1833_, v___y_1840_);
v_i_1833_ = v___x_1842_;
v_bs_1834_ = v___x_1843_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11___boxed(lean_object* v_sz_1848_, lean_object* v_i_1849_, lean_object* v_bs_1850_){
_start:
{
size_t v_sz_boxed_1851_; size_t v_i_boxed_1852_; lean_object* v_res_1853_; 
v_sz_boxed_1851_ = lean_unbox_usize(v_sz_1848_);
lean_dec(v_sz_1848_);
v_i_boxed_1852_ = lean_unbox_usize(v_i_1849_);
lean_dec(v_i_1849_);
v_res_1853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(v_sz_boxed_1851_, v_i_boxed_1852_, v_bs_1850_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8(lean_object* v_a_1854_){
_start:
{
size_t v_sz_1855_; size_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v_sz_1855_ = lean_array_size(v_a_1854_);
v___x_1856_ = ((size_t)0ULL);
v___x_1857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8_spec__11(v_sz_1855_, v___x_1856_, v_a_1854_);
v___x_1858_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7(lean_object* v_k_1859_, lean_object* v_x_1860_){
_start:
{
if (lean_obj_tag(v_x_1860_) == 0)
{
lean_object* v___x_1861_; 
lean_dec_ref(v_k_1859_);
v___x_1861_ = lean_box(0);
return v___x_1861_;
}
else
{
lean_object* v_val_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v_val_1862_ = lean_ctor_get(v_x_1860_, 0);
lean_inc(v_val_1862_);
lean_dec_ref(v_x_1860_);
v___x_1863_ = l_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7_spec__8(v_val_1862_);
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v_k_1859_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_box(0);
v___x_1866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1864_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
return v___x_1866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__3(lean_object* v_k_1867_, lean_object* v_x_1868_){
_start:
{
if (lean_obj_tag(v_x_1868_) == 0)
{
lean_object* v___x_1869_; 
lean_dec_ref(v_k_1867_);
v___x_1869_ = lean_box(0);
return v___x_1869_;
}
else
{
lean_object* v_val_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v_val_1870_ = lean_ctor_get(v_x_1868_, 0);
lean_inc(v_val_1870_);
lean_dec_ref(v_x_1868_);
v___x_1871_ = l_Lean_Lsp_instToJsonRange_toJson(v_val_1870_);
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v_k_1867_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = lean_box(0);
v___x_1874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1872_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
return v___x_1874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2(lean_object* v_x_1875_){
_start:
{
lean_object* v_range_1876_; lean_object* v_fullRange_x3f_1877_; lean_object* v_severity_x3f_1878_; lean_object* v_isSilent_x3f_1879_; lean_object* v_code_x3f_1880_; lean_object* v_source_x3f_1881_; lean_object* v_message_1882_; lean_object* v_tags_x3f_1883_; lean_object* v_leanTags_x3f_1884_; lean_object* v_relatedInformation_x3f_1885_; lean_object* v_data_x3f_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_range_1876_ = lean_ctor_get(v_x_1875_, 0);
lean_inc_ref(v_range_1876_);
v_fullRange_x3f_1877_ = lean_ctor_get(v_x_1875_, 1);
lean_inc(v_fullRange_x3f_1877_);
v_severity_x3f_1878_ = lean_ctor_get(v_x_1875_, 2);
lean_inc(v_severity_x3f_1878_);
v_isSilent_x3f_1879_ = lean_ctor_get(v_x_1875_, 3);
lean_inc(v_isSilent_x3f_1879_);
v_code_x3f_1880_ = lean_ctor_get(v_x_1875_, 4);
lean_inc(v_code_x3f_1880_);
v_source_x3f_1881_ = lean_ctor_get(v_x_1875_, 5);
lean_inc(v_source_x3f_1881_);
v_message_1882_ = lean_ctor_get(v_x_1875_, 6);
lean_inc(v_message_1882_);
v_tags_x3f_1883_ = lean_ctor_get(v_x_1875_, 7);
lean_inc(v_tags_x3f_1883_);
v_leanTags_x3f_1884_ = lean_ctor_get(v_x_1875_, 8);
lean_inc(v_leanTags_x3f_1884_);
v_relatedInformation_x3f_1885_ = lean_ctor_get(v_x_1875_, 9);
lean_inc(v_relatedInformation_x3f_1885_);
v_data_x3f_1886_ = lean_ctor_get(v_x_1875_, 10);
lean_inc(v_data_x3f_1886_);
lean_dec_ref(v_x_1875_);
v___x_1887_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
v___x_1888_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_1876_);
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1887_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v___x_1890_ = lean_box(0);
v___x_1891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1889_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
v___x_1893_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__3(v___x_1892_, v_fullRange_x3f_1877_);
v___x_1894_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
v___x_1895_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__4(v___x_1894_, v_severity_x3f_1878_);
lean_dec(v_severity_x3f_1878_);
v___x_1896_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
v___x_1897_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(v___x_1896_, v_isSilent_x3f_1879_);
lean_dec(v_isSilent_x3f_1879_);
v___x_1898_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
v___x_1899_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__5(v___x_1898_, v_code_x3f_1880_);
v___x_1900_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
v___x_1901_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__6(v___x_1900_, v_source_x3f_1881_);
v___x_1902_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
v___x_1903_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1903_, 0, v_message_1882_);
v___x_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1902_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
lean_ctor_set(v___x_1905_, 1, v___x_1890_);
v___x_1906_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
v___x_1907_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__7(v___x_1906_, v_tags_x3f_1883_);
v___x_1908_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
v___x_1909_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__8(v___x_1908_, v_leanTags_x3f_1884_);
v___x_1910_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
v___x_1911_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__9(v___x_1910_, v_relatedInformation_x3f_1885_);
v___x_1912_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
v___x_1913_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2_spec__10(v___x_1912_, v_data_x3f_1886_);
lean_dec(v_data_x3f_1886_);
v___x_1914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
lean_ctor_set(v___x_1914_, 1, v___x_1890_);
v___x_1915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1911_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1909_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1907_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1905_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1901_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1899_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1897_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1895_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1893_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1891_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2));
v___x_1926_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(v___x_1924_, v___x_1925_);
v___x_1927_ = l_Lean_Json_mkObj(v___x_1926_);
lean_dec(v___x_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(size_t v_sz_1928_, size_t v_i_1929_, lean_object* v_bs_1930_){
_start:
{
uint8_t v___x_1931_; 
v___x_1931_ = lean_usize_dec_lt(v_i_1929_, v_sz_1928_);
if (v___x_1931_ == 0)
{
return v_bs_1930_;
}
else
{
lean_object* v_v_1932_; lean_object* v___x_1933_; lean_object* v_bs_x27_1934_; lean_object* v___x_1935_; size_t v___x_1936_; size_t v___x_1937_; lean_object* v___x_1938_; 
v_v_1932_ = lean_array_uget(v_bs_1930_, v_i_1929_);
v___x_1933_ = lean_unsigned_to_nat(0u);
v_bs_x27_1934_ = lean_array_uset(v_bs_1930_, v_i_1929_, v___x_1933_);
v___x_1935_ = l_Lean_Lsp_instToJsonDiagnosticWith_toJson___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__2(v_v_1932_);
v___x_1936_ = ((size_t)1ULL);
v___x_1937_ = lean_usize_add(v_i_1929_, v___x_1936_);
v___x_1938_ = lean_array_uset(v_bs_x27_1934_, v_i_1929_, v___x_1935_);
v_i_1929_ = v___x_1937_;
v_bs_1930_ = v___x_1938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3___boxed(lean_object* v_sz_1940_, lean_object* v_i_1941_, lean_object* v_bs_1942_){
_start:
{
size_t v_sz_boxed_1943_; size_t v_i_boxed_1944_; lean_object* v_res_1945_; 
v_sz_boxed_1943_ = lean_unbox_usize(v_sz_1940_);
lean_dec(v_sz_1940_);
v_i_boxed_1944_ = lean_unbox_usize(v_i_1941_);
lean_dec(v_i_1941_);
v_res_1945_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(v_sz_boxed_1943_, v_i_boxed_1944_, v_bs_1942_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2(lean_object* v_a_1946_){
_start:
{
size_t v_sz_1947_; size_t v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v_sz_1947_ = lean_array_size(v_a_1946_);
v___x_1948_ = ((size_t)0ULL);
v___x_1949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2_spec__3(v_sz_1947_, v___x_1948_, v_a_1946_);
v___x_1950_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson(lean_object* v_x_1955_){
_start:
{
lean_object* v_uri_1956_; lean_object* v_version_x3f_1957_; lean_object* v_isIncremental_x3f_1958_; lean_object* v_diagnostics_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_uri_1956_ = lean_ctor_get(v_x_1955_, 0);
lean_inc_ref(v_uri_1956_);
v_version_x3f_1957_ = lean_ctor_get(v_x_1955_, 1);
lean_inc(v_version_x3f_1957_);
v_isIncremental_x3f_1958_ = lean_ctor_get(v_x_1955_, 2);
lean_inc(v_isIncremental_x3f_1958_);
v_diagnostics_1959_ = lean_ctor_get(v_x_1955_, 3);
lean_inc_ref(v_diagnostics_1959_);
lean_dec_ref(v_x_1955_);
v___x_1960_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0));
v___x_1961_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1961_, 0, v_uri_1956_);
v___x_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1960_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = lean_box(0);
v___x_1964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1));
v___x_1966_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__0(v___x_1965_, v_version_x3f_1957_);
v___x_1967_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2));
v___x_1968_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__1(v___x_1967_, v_isIncremental_x3f_1958_);
lean_dec(v_isIncremental_x3f_1958_);
v___x_1969_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3));
v___x_1970_ = l_Array_toJson___at___00Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson_spec__2(v_diagnostics_1959_);
v___x_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1969_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
lean_ctor_set(v___x_1972_, 1, v___x_1963_);
v___x_1973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
lean_ctor_set(v___x_1973_, 1, v___x_1963_);
v___x_1974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1968_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1966_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1964_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__2));
v___x_1978_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson_spec__0(v___x_1976_, v___x_1977_);
v___x_1979_ = l_Lean_Json_mkObj(v___x_1978_);
lean_dec(v___x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(lean_object* v_x_1984_){
_start:
{
if (lean_obj_tag(v_x_1984_) == 0)
{
lean_object* v___x_1985_; 
v___x_1985_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___closed__0));
return v___x_1985_;
}
else
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_Json_getBool_x3f(v_x_1984_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1986_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1986_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2003_; 
v_a_1995_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1997_ = v___x_1986_;
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1986_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1999_, 0, v_a_1995_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_1999_);
v___x_2001_ = v___x_1997_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2___boxed(lean_object* v_x_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(v_x_2004_);
lean_dec(v_x_2004_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(lean_object* v_j_2006_, lean_object* v_k_2007_){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = l_Lean_Json_getObjValD(v_j_2006_, v_k_2007_);
v___x_2009_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1_spec__2(v___x_2008_);
lean_dec(v___x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1___boxed(lean_object* v_j_2010_, lean_object* v_k_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_j_2010_, v_k_2011_);
lean_dec_ref(v_k_2011_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0(lean_object* v_x_2015_){
_start:
{
if (lean_obj_tag(v_x_2015_) == 0)
{
lean_object* v___x_2016_; 
v___x_2016_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0___closed__0));
return v___x_2016_;
}
else
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_Json_getInt_x3f(v_x_2015_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2017_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2017_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2034_; 
v_a_2026_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2028_ = v___x_2017_;
v_isShared_2029_ = v_isSharedCheck_2034_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2017_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2034_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2030_, 0, v_a_2026_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2030_);
v___x_2032_ = v___x_2028_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(lean_object* v_j_2035_, lean_object* v_k_2036_){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = l_Lean_Json_getObjValD(v_j_2035_, v_k_2036_);
v___x_2038_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0_spec__0(v___x_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0___boxed(lean_object* v_j_2039_, lean_object* v_k_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(v_j_2039_, v_k_2040_);
lean_dec_ref(v_k_2040_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22(lean_object* v_x_2044_){
_start:
{
if (lean_obj_tag(v_x_2044_) == 0)
{
lean_object* v___x_2045_; 
v___x_2045_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22___closed__0));
return v___x_2045_;
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_x_2044_);
v___x_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
return v___x_2047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(lean_object* v_j_2048_, lean_object* v_k_2049_){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = l_Lean_Json_getObjValD(v_j_2048_, v_k_2049_);
v___x_2051_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14_spec__22(v___x_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14___boxed(lean_object* v_j_2052_, lean_object* v_k_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(v_j_2052_, v_k_2053_);
lean_dec_ref(v_k_2053_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(size_t v_sz_2057_, size_t v_i_2058_, lean_object* v_bs_2059_){
_start:
{
uint8_t v___x_2062_; 
v___x_2062_ = lean_usize_dec_lt(v_i_2058_, v_sz_2057_);
if (v___x_2062_ == 0)
{
lean_object* v___x_2063_; 
v___x_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_bs_2059_);
return v___x_2063_;
}
else
{
lean_object* v_v_2064_; lean_object* v___x_2065_; 
v_v_2064_ = lean_array_uget_borrowed(v_bs_2059_, v_i_2058_);
lean_inc(v_v_2064_);
v___x_2065_ = l_Lean_Json_getNat_x3f(v_v_2064_);
if (lean_obj_tag(v___x_2065_) == 1)
{
lean_object* v_a_2066_; lean_object* v___x_2067_; lean_object* v_bs_x27_2068_; uint8_t v_a_2070_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref(v___x_2065_);
v___x_2067_ = lean_unsigned_to_nat(0u);
v_bs_x27_2068_ = lean_array_uset(v_bs_2059_, v_i_2058_, v___x_2067_);
v___x_2076_ = lean_unsigned_to_nat(1u);
v___x_2077_ = lean_nat_dec_eq(v_a_2066_, v___x_2076_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2078_ = lean_unsigned_to_nat(2u);
v___x_2079_ = lean_nat_dec_eq(v_a_2066_, v___x_2078_);
lean_dec(v_a_2066_);
if (v___x_2079_ == 0)
{
lean_dec_ref(v_bs_x27_2068_);
goto v___jp_2060_;
}
else
{
uint8_t v___x_2080_; 
v___x_2080_ = 1;
v_a_2070_ = v___x_2080_;
goto v___jp_2069_;
}
}
else
{
uint8_t v___x_2081_; 
lean_dec(v_a_2066_);
v___x_2081_ = 0;
v_a_2070_ = v___x_2081_;
goto v___jp_2069_;
}
v___jp_2069_:
{
size_t v___x_2071_; size_t v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2071_ = ((size_t)1ULL);
v___x_2072_ = lean_usize_add(v_i_2058_, v___x_2071_);
v___x_2073_ = lean_box(v_a_2070_);
v___x_2074_ = lean_array_uset(v_bs_x27_2068_, v_i_2058_, v___x_2073_);
v_i_2058_ = v___x_2072_;
v_bs_2059_ = v___x_2074_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_bs_2059_);
goto v___jp_2060_;
}
}
v___jp_2060_:
{
lean_object* v___x_2061_; 
v___x_2061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___closed__0));
return v___x_2061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26___boxed(lean_object* v_sz_2082_, lean_object* v_i_2083_, lean_object* v_bs_2084_){
_start:
{
size_t v_sz_boxed_2085_; size_t v_i_boxed_2086_; lean_object* v_res_2087_; 
v_sz_boxed_2085_ = lean_unbox_usize(v_sz_2082_);
lean_dec(v_sz_2082_);
v_i_boxed_2086_ = lean_unbox_usize(v_i_2083_);
lean_dec(v_i_2083_);
v_res_2087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(v_sz_boxed_2085_, v_i_boxed_2086_, v_bs_2084_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21(lean_object* v_x_2089_){
_start:
{
if (lean_obj_tag(v_x_2089_) == 4)
{
lean_object* v_elems_2090_; size_t v_sz_2091_; size_t v___x_2092_; lean_object* v___x_2093_; 
v_elems_2090_ = lean_ctor_get(v_x_2089_, 0);
lean_inc_ref(v_elems_2090_);
lean_dec_ref(v_x_2089_);
v_sz_2091_ = lean_array_size(v_elems_2090_);
v___x_2092_ = ((size_t)0ULL);
v___x_2093_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21_spec__26(v_sz_2091_, v___x_2092_, v_elems_2090_);
return v___x_2093_;
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2094_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0));
v___x_2095_ = lean_unsigned_to_nat(80u);
v___x_2096_ = l_Lean_Json_pretty(v_x_2089_, v___x_2095_);
v___x_2097_ = lean_string_append(v___x_2094_, v___x_2096_);
lean_dec_ref(v___x_2096_);
v___x_2098_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2099_ = lean_string_append(v___x_2097_, v___x_2098_);
v___x_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
return v___x_2100_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18(lean_object* v_x_2103_){
_start:
{
if (lean_obj_tag(v_x_2103_) == 0)
{
lean_object* v___x_2104_; 
v___x_2104_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18___closed__0));
return v___x_2104_;
}
else
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21(v_x_2103_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2105_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2105_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2122_; 
v_a_2114_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2116_ = v___x_2105_;
v_isShared_2117_ = v_isSharedCheck_2122_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2105_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2122_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v_a_2114_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2118_);
v___x_2120_ = v___x_2116_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(lean_object* v_j_2123_, lean_object* v_k_2124_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = l_Lean_Json_getObjValD(v_j_2123_, v_k_2124_);
v___x_2126_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18(v___x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12___boxed(lean_object* v_j_2127_, lean_object* v_k_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(v_j_2127_, v_k_2128_);
lean_dec_ref(v_k_2128_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12(lean_object* v_x_2132_){
_start:
{
lean_object* v_a_2134_; lean_object* v_j_2138_; 
if (lean_obj_tag(v_x_2132_) == 0)
{
lean_object* v___x_2146_; 
v___x_2146_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12___closed__0));
return v___x_2146_;
}
else
{
switch(lean_obj_tag(v_x_2132_))
{
case 2:
{
lean_object* v_n_2147_; lean_object* v_mantissa_2148_; lean_object* v_exponent_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v_n_2147_ = lean_ctor_get(v_x_2132_, 0);
v_mantissa_2148_ = lean_ctor_get(v_n_2147_, 0);
v_exponent_2149_ = lean_ctor_get(v_n_2147_, 1);
v___x_2150_ = lean_unsigned_to_nat(0u);
v___x_2151_ = lean_nat_dec_eq(v_exponent_2149_, v___x_2150_);
if (v___x_2151_ == 0)
{
v_j_2138_ = v_x_2132_;
goto v___jp_2137_;
}
else
{
lean_object* v___x_2152_; 
lean_inc(v_mantissa_2148_);
lean_dec_ref(v_x_2132_);
v___x_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2152_, 0, v_mantissa_2148_);
v_a_2134_ = v___x_2152_;
goto v___jp_2133_;
}
}
case 3:
{
lean_object* v_s_2153_; lean_object* v___x_2154_; 
v_s_2153_ = lean_ctor_get(v_x_2132_, 0);
lean_inc_ref(v_s_2153_);
lean_dec_ref(v_x_2132_);
v___x_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2154_, 0, v_s_2153_);
v_a_2134_ = v___x_2154_;
goto v___jp_2133_;
}
default: 
{
v_j_2138_ = v_x_2132_;
goto v___jp_2137_;
}
}
}
v___jp_2133_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2135_, 0, v_a_2134_);
v___x_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
return v___x_2136_;
}
v___jp_2137_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2139_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticCode___lam__0___closed__0));
v___x_2140_ = lean_unsigned_to_nat(80u);
v___x_2141_ = l_Lean_Json_pretty(v_j_2138_, v___x_2140_);
v___x_2142_ = lean_string_append(v___x_2139_, v___x_2141_);
lean_dec_ref(v___x_2141_);
v___x_2143_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2144_ = lean_string_append(v___x_2142_, v___x_2143_);
v___x_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
return v___x_2145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(lean_object* v_j_2155_, lean_object* v_k_2156_){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = l_Lean_Json_getObjValD(v_j_2155_, v_k_2156_);
v___x_2158_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9_spec__12(v___x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9___boxed(lean_object* v_j_2159_, lean_object* v_k_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(v_j_2159_, v_k_2160_);
lean_dec_ref(v_k_2160_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(lean_object* v_j_2162_, lean_object* v_k_2163_){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = l_Lean_Json_getObjValD(v_j_2162_, v_k_2163_);
v___x_2165_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6___boxed(lean_object* v_j_2166_, lean_object* v_k_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(v_j_2166_, v_k_2167_);
lean_dec_ref(v_k_2167_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(size_t v_sz_2171_, size_t v_i_2172_, lean_object* v_bs_2173_){
_start:
{
uint8_t v___x_2176_; 
v___x_2176_ = lean_usize_dec_lt(v_i_2172_, v_sz_2171_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; 
v___x_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2177_, 0, v_bs_2173_);
return v___x_2177_;
}
else
{
lean_object* v_v_2178_; lean_object* v___x_2179_; 
v_v_2178_ = lean_array_uget_borrowed(v_bs_2173_, v_i_2172_);
lean_inc(v_v_2178_);
v___x_2179_ = l_Lean_Json_getNat_x3f(v_v_2178_);
if (lean_obj_tag(v___x_2179_) == 1)
{
lean_object* v_a_2180_; lean_object* v___x_2181_; lean_object* v_bs_x27_2182_; uint8_t v_a_2184_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref(v___x_2179_);
v___x_2181_ = lean_unsigned_to_nat(0u);
v_bs_x27_2182_ = lean_array_uset(v_bs_2173_, v_i_2172_, v___x_2181_);
v___x_2190_ = lean_unsigned_to_nat(1u);
v___x_2191_ = lean_nat_dec_eq(v_a_2180_, v___x_2190_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2192_ = lean_unsigned_to_nat(2u);
v___x_2193_ = lean_nat_dec_eq(v_a_2180_, v___x_2192_);
lean_dec(v_a_2180_);
if (v___x_2193_ == 0)
{
lean_dec_ref(v_bs_x27_2182_);
goto v___jp_2174_;
}
else
{
uint8_t v___x_2194_; 
v___x_2194_ = 1;
v_a_2184_ = v___x_2194_;
goto v___jp_2183_;
}
}
else
{
uint8_t v___x_2195_; 
lean_dec(v_a_2180_);
v___x_2195_ = 0;
v_a_2184_ = v___x_2195_;
goto v___jp_2183_;
}
v___jp_2183_:
{
size_t v___x_2185_; size_t v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2185_ = ((size_t)1ULL);
v___x_2186_ = lean_usize_add(v_i_2172_, v___x_2185_);
v___x_2187_ = lean_box(v_a_2184_);
v___x_2188_ = lean_array_uset(v_bs_x27_2182_, v_i_2172_, v___x_2187_);
v_i_2172_ = v___x_2186_;
v_bs_2173_ = v___x_2188_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_2179_);
lean_dec_ref(v_bs_2173_);
goto v___jp_2174_;
}
}
v___jp_2174_:
{
lean_object* v___x_2175_; 
v___x_2175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___closed__0));
return v___x_2175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23___boxed(lean_object* v_sz_2196_, lean_object* v_i_2197_, lean_object* v_bs_2198_){
_start:
{
size_t v_sz_boxed_2199_; size_t v_i_boxed_2200_; lean_object* v_res_2201_; 
v_sz_boxed_2199_ = lean_unbox_usize(v_sz_2196_);
lean_dec(v_sz_2196_);
v_i_boxed_2200_ = lean_unbox_usize(v_i_2197_);
lean_dec(v_i_2197_);
v_res_2201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(v_sz_boxed_2199_, v_i_boxed_2200_, v_bs_2198_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18(lean_object* v_x_2202_){
_start:
{
if (lean_obj_tag(v_x_2202_) == 4)
{
lean_object* v_elems_2203_; size_t v_sz_2204_; size_t v___x_2205_; lean_object* v___x_2206_; 
v_elems_2203_ = lean_ctor_get(v_x_2202_, 0);
lean_inc_ref(v_elems_2203_);
lean_dec_ref(v_x_2202_);
v_sz_2204_ = lean_array_size(v_elems_2203_);
v___x_2205_ = ((size_t)0ULL);
v___x_2206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18_spec__23(v_sz_2204_, v___x_2205_, v_elems_2203_);
return v___x_2206_;
}
else
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2207_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0));
v___x_2208_ = lean_unsigned_to_nat(80u);
v___x_2209_ = l_Lean_Json_pretty(v_x_2202_, v___x_2208_);
v___x_2210_ = lean_string_append(v___x_2207_, v___x_2209_);
lean_dec_ref(v___x_2209_);
v___x_2211_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2212_ = lean_string_append(v___x_2210_, v___x_2211_);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
return v___x_2213_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16(lean_object* v_x_2216_){
_start:
{
if (lean_obj_tag(v_x_2216_) == 0)
{
lean_object* v___x_2217_; 
v___x_2217_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16___closed__0));
return v___x_2217_;
}
else
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16_spec__18(v_x_2216_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2218_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2218_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2235_; 
v_a_2227_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2229_ = v___x_2218_;
v_isShared_2230_ = v_isSharedCheck_2235_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2218_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2235_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2231_, 0, v_a_2227_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2231_);
v___x_2233_ = v___x_2229_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(lean_object* v_j_2236_, lean_object* v_k_2237_){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = l_Lean_Json_getObjValD(v_j_2236_, v_k_2237_);
v___x_2239_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11_spec__16(v___x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11___boxed(lean_object* v_j_2240_, lean_object* v_k_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(v_j_2240_, v_k_2241_);
lean_dec_ref(v_k_2241_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10(lean_object* v_x_2245_){
_start:
{
uint8_t v_a_2255_; 
if (lean_obj_tag(v_x_2245_) == 0)
{
lean_object* v___x_2259_; 
v___x_2259_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10___closed__0));
return v___x_2259_;
}
else
{
lean_object* v___x_2260_; 
lean_inc(v_x_2245_);
v___x_2260_ = l_Lean_Json_getNat_x3f(v_x_2245_);
if (lean_obj_tag(v___x_2260_) == 1)
{
lean_object* v_a_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref(v___x_2260_);
v___x_2262_ = lean_unsigned_to_nat(1u);
v___x_2263_ = lean_nat_dec_eq(v_a_2261_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; uint8_t v___x_2265_; 
v___x_2264_ = lean_unsigned_to_nat(2u);
v___x_2265_ = lean_nat_dec_eq(v_a_2261_, v___x_2264_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2266_ = lean_unsigned_to_nat(3u);
v___x_2267_ = lean_nat_dec_eq(v_a_2261_, v___x_2266_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; uint8_t v___x_2269_; 
v___x_2268_ = lean_unsigned_to_nat(4u);
v___x_2269_ = lean_nat_dec_eq(v_a_2261_, v___x_2268_);
lean_dec(v_a_2261_);
if (v___x_2269_ == 0)
{
goto v___jp_2246_;
}
else
{
uint8_t v___x_2270_; 
lean_dec(v_x_2245_);
v___x_2270_ = 3;
v_a_2255_ = v___x_2270_;
goto v___jp_2254_;
}
}
else
{
uint8_t v___x_2271_; 
lean_dec(v_a_2261_);
lean_dec(v_x_2245_);
v___x_2271_ = 2;
v_a_2255_ = v___x_2271_;
goto v___jp_2254_;
}
}
else
{
uint8_t v___x_2272_; 
lean_dec(v_a_2261_);
lean_dec(v_x_2245_);
v___x_2272_ = 1;
v_a_2255_ = v___x_2272_;
goto v___jp_2254_;
}
}
else
{
uint8_t v___x_2273_; 
lean_dec(v_a_2261_);
lean_dec(v_x_2245_);
v___x_2273_ = 0;
v_a_2255_ = v___x_2273_;
goto v___jp_2254_;
}
}
else
{
lean_dec_ref(v___x_2260_);
goto v___jp_2246_;
}
}
v___jp_2246_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2247_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__0));
v___x_2248_ = lean_unsigned_to_nat(80u);
v___x_2249_ = l_Lean_Json_pretty(v_x_2245_, v___x_2248_);
v___x_2250_ = lean_string_append(v___x_2247_, v___x_2249_);
lean_dec_ref(v___x_2249_);
v___x_2251_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2252_ = lean_string_append(v___x_2250_, v___x_2251_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
return v___x_2253_;
}
v___jp_2254_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = lean_box(v_a_2255_);
v___x_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
v___x_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
return v___x_2258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(lean_object* v_j_2274_, lean_object* v_k_2275_){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = l_Lean_Json_getObjValD(v_j_2274_, v_k_2275_);
v___x_2277_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8_spec__10(v___x_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8___boxed(lean_object* v_j_2278_, lean_object* v_k_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(v_j_2278_, v_k_2279_);
lean_dec_ref(v_k_2279_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8(lean_object* v_x_2283_){
_start:
{
if (lean_obj_tag(v_x_2283_) == 0)
{
lean_object* v___x_2284_; 
v___x_2284_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8___closed__0));
return v___x_2284_;
}
else
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_Lsp_instFromJsonRange_fromJson(v_x_2283_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2285_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2285_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2302_; 
v_a_2294_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2296_ = v___x_2285_;
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2285_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2298_, 0, v_a_2294_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2298_);
v___x_2300_ = v___x_2296_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(lean_object* v_j_2303_, lean_object* v_k_2304_){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = l_Lean_Json_getObjValD(v_j_2303_, v_k_2304_);
v___x_2306_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7_spec__8(v___x_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7___boxed(lean_object* v_j_2307_, lean_object* v_k_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(v_j_2307_, v_k_2308_);
lean_dec_ref(v_k_2308_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(size_t v_sz_2310_, size_t v_i_2311_, lean_object* v_bs_2312_){
_start:
{
uint8_t v___x_2313_; 
v___x_2313_ = lean_usize_dec_lt(v_i_2311_, v_sz_2310_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2314_, 0, v_bs_2312_);
return v___x_2314_;
}
else
{
lean_object* v_v_2315_; lean_object* v___x_2316_; 
v_v_2315_ = lean_array_uget_borrowed(v_bs_2312_, v_i_2311_);
lean_inc(v_v_2315_);
v___x_2316_ = l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson(v_v_2315_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_dec_ref(v_bs_2312_);
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_2316_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2316_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2326_; lean_object* v_bs_x27_2327_; size_t v___x_2328_; size_t v___x_2329_; lean_object* v___x_2330_; 
v_a_2325_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2325_);
lean_dec_ref(v___x_2316_);
v___x_2326_ = lean_unsigned_to_nat(0u);
v_bs_x27_2327_ = lean_array_uset(v_bs_2312_, v_i_2311_, v___x_2326_);
v___x_2328_ = ((size_t)1ULL);
v___x_2329_ = lean_usize_add(v_i_2311_, v___x_2328_);
v___x_2330_ = lean_array_uset(v_bs_x27_2327_, v_i_2311_, v_a_2325_);
v_i_2311_ = v___x_2329_;
v_bs_2312_ = v___x_2330_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29___boxed(lean_object* v_sz_2332_, lean_object* v_i_2333_, lean_object* v_bs_2334_){
_start:
{
size_t v_sz_boxed_2335_; size_t v_i_boxed_2336_; lean_object* v_res_2337_; 
v_sz_boxed_2335_ = lean_unbox_usize(v_sz_2332_);
lean_dec(v_sz_2332_);
v_i_boxed_2336_ = lean_unbox_usize(v_i_2333_);
lean_dec(v_i_2333_);
v_res_2337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(v_sz_boxed_2335_, v_i_boxed_2336_, v_bs_2334_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24(lean_object* v_x_2338_){
_start:
{
if (lean_obj_tag(v_x_2338_) == 4)
{
lean_object* v_elems_2339_; size_t v_sz_2340_; size_t v___x_2341_; lean_object* v___x_2342_; 
v_elems_2339_ = lean_ctor_get(v_x_2338_, 0);
lean_inc_ref(v_elems_2339_);
lean_dec_ref(v_x_2338_);
v_sz_2340_ = lean_array_size(v_elems_2339_);
v___x_2341_ = ((size_t)0ULL);
v___x_2342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24_spec__29(v_sz_2340_, v___x_2341_, v_elems_2339_);
return v___x_2342_;
}
else
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2343_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0));
v___x_2344_ = lean_unsigned_to_nat(80u);
v___x_2345_ = l_Lean_Json_pretty(v_x_2338_, v___x_2344_);
v___x_2346_ = lean_string_append(v___x_2343_, v___x_2345_);
lean_dec_ref(v___x_2345_);
v___x_2347_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2348_ = lean_string_append(v___x_2346_, v___x_2347_);
v___x_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
return v___x_2349_;
}
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20(lean_object* v_x_2352_){
_start:
{
if (lean_obj_tag(v_x_2352_) == 0)
{
lean_object* v___x_2353_; 
v___x_2353_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20___closed__0));
return v___x_2353_;
}
else
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20_spec__24(v_x_2352_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2354_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2354_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2371_; 
v_a_2363_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2365_ = v___x_2354_;
v_isShared_2366_ = v_isSharedCheck_2371_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2354_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2371_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2367_, 0, v_a_2363_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2367_);
v___x_2369_ = v___x_2365_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(lean_object* v_j_2372_, lean_object* v_k_2373_){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = l_Lean_Json_getObjValD(v_j_2372_, v_k_2373_);
v___x_2375_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13_spec__20(v___x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13___boxed(lean_object* v_j_2376_, lean_object* v_k_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(v_j_2376_, v_k_2377_);
lean_dec_ref(v_k_2377_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14(lean_object* v_x_2381_){
_start:
{
if (lean_obj_tag(v_x_2381_) == 0)
{
lean_object* v___x_2382_; 
v___x_2382_ = ((lean_object*)(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14___closed__0));
return v___x_2382_;
}
else
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Lean_Json_getStr_x3f(v_x_2381_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2383_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2383_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2400_; 
v_a_2392_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2394_ = v___x_2383_;
v_isShared_2395_ = v_isSharedCheck_2400_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2383_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2400_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2396_; lean_object* v___x_2398_; 
v___x_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2396_, 0, v_a_2392_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 0, v___x_2396_);
v___x_2398_ = v___x_2394_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2396_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(lean_object* v_j_2401_, lean_object* v_k_2402_){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2403_ = l_Lean_Json_getObjValD(v_j_2401_, v_k_2402_);
v___x_2404_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10_spec__14(v___x_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10___boxed(lean_object* v_j_2405_, lean_object* v_k_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(v_j_2405_, v_k_2406_);
lean_dec_ref(v_k_2406_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5(lean_object* v_json_2408_){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__7));
lean_inc(v_json_2408_);
v___x_2410_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__6(v_json_2408_, v___x_2409_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2420_; 
lean_dec(v_json_2408_);
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2413_ = v___x_2410_;
v_isShared_2414_ = v_isSharedCheck_2420_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2410_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2420_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2418_; 
v___x_2415_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__9);
v___x_2416_ = lean_string_append(v___x_2415_, v_a_2411_);
lean_dec(v_a_2411_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2416_);
v___x_2418_ = v___x_2413_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
else
{
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec(v_json_2408_);
v_a_2421_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2410_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2410_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
lean_ctor_set_tag(v___x_2423_, 0);
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_a_2429_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2429_);
lean_dec_ref(v___x_2410_);
v___x_2430_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__8));
lean_inc(v_json_2408_);
v___x_2431_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__7(v_json_2408_, v___x_2430_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2441_; 
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2441_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2441_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2436_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__14);
v___x_2437_ = lean_string_append(v___x_2436_, v_a_2432_);
lean_dec(v_a_2432_);
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v___x_2437_);
v___x_2439_ = v___x_2434_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
else
{
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2442_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2431_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2431_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
lean_ctor_set_tag(v___x_2444_, 0);
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v_a_2450_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_a_2450_);
lean_dec_ref(v___x_2431_);
v___x_2451_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__9));
lean_inc(v_json_2408_);
v___x_2452_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__8(v_json_2408_, v___x_2451_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2462_; 
lean_dec(v_a_2450_);
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2462_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2462_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2460_; 
v___x_2457_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__20);
v___x_2458_ = lean_string_append(v___x_2457_, v_a_2453_);
lean_dec(v_a_2453_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2458_);
v___x_2460_ = v___x_2455_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2458_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
else
{
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec(v_a_2450_);
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2463_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2452_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2452_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
lean_ctor_set_tag(v___x_2465_, 0);
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v_a_2471_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2471_);
lean_dec_ref(v___x_2452_);
v___x_2472_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__10));
lean_inc(v_json_2408_);
v___x_2473_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_json_2408_, v___x_2472_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2483_; 
lean_dec(v_a_2471_);
lean_dec(v_a_2450_);
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2476_ = v___x_2473_;
v_isShared_2477_ = v_isSharedCheck_2483_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2473_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2483_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2478_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__27);
v___x_2479_ = lean_string_append(v___x_2478_, v_a_2474_);
lean_dec(v_a_2474_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 0, v___x_2479_);
v___x_2481_ = v___x_2476_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
else
{
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec(v_a_2471_);
lean_dec(v_a_2450_);
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2484_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2473_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2473_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
lean_ctor_set_tag(v___x_2486_, 0);
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
else
{
lean_object* v_a_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v_a_2492_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2492_);
lean_dec_ref(v___x_2473_);
v___x_2493_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__11));
lean_inc(v_json_2408_);
v___x_2494_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__9(v_json_2408_, v___x_2493_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2504_; 
lean_dec(v_a_2492_);
lean_dec(v_a_2471_);
lean_dec(v_a_2450_);
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2497_ = v___x_2494_;
v_isShared_2498_ = v_isSharedCheck_2504_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2494_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2504_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2499_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__33);
v___x_2500_ = lean_string_append(v___x_2499_, v_a_2495_);
lean_dec(v_a_2495_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 0, v___x_2500_);
v___x_2502_ = v___x_2497_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
else
{
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v_a_2492_);
lean_dec(v_a_2471_);
lean_dec(v_a_2450_);
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2505_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2494_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2494_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
lean_ctor_set_tag(v___x_2507_, 0);
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v_a_2513_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2513_);
lean_dec_ref(v___x_2494_);
v___x_2514_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__12));
lean_inc(v_json_2408_);
v___x_2515_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__10(v_json_2408_, v___x_2514_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2525_; 
lean_dec(v_a_2513_);
lean_dec(v_a_2492_);
lean_dec(v_a_2471_);
lean_dec(v_a_2450_);
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2525_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2525_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2520_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__40);
v___x_2521_ = lean_string_append(v___x_2520_, v_a_2516_);
lean_dec(v_a_2516_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2521_);
v___x_2523_ = v___x_2518_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
else
{
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v_a_2513_);
lean_dec(v_a_2492_);
lean_dec(v_a_2471_);
lean_dec(v_a_2450_);
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2526_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2515_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2515_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set_tag(v___x_2528_, 0);
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v_a_2534_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2534_);
lean_dec_ref(v___x_2515_);
v___x_2535_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticRelatedInformation_toJson___closed__1));
lean_inc(v_json_2408_);
v___x_2536_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_2408_, v___x_2535_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2546_; 
lean_dec(v_a_2534_);
lean_dec(v_a_2513_);
lean_dec(v_a_2492_);
lean_dec(v_a_2471_);
lean_dec(v_a_2450_);
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2546_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2546_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2544_; 
v___x_2541_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__42);
v___x_2542_ = lean_string_append(v___x_2541_, v_a_2537_);
lean_dec(v_a_2537_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v___x_2542_);
v___x_2544_ = v___x_2539_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
else
{
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_dec(v_a_2534_);
lean_dec(v_a_2513_);
lean_dec(v_a_2492_);
lean_dec(v_a_2471_);
lean_dec(v_a_2450_);
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2547_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2536_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2536_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
lean_ctor_set_tag(v___x_2549_, 0);
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v_a_2555_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2555_);
lean_dec_ref(v___x_2536_);
v___x_2556_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__13));
lean_inc(v_json_2408_);
v___x_2557_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__11(v_json_2408_, v___x_2556_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2567_; 
lean_dec(v_a_2555_);
lean_dec(v_a_2534_);
lean_dec(v_a_2513_);
lean_dec(v_a_2492_);
lean_dec(v_a_2471_);
lean_dec(v_a_2450_);
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2560_ = v___x_2557_;
v_isShared_2561_ = v_isSharedCheck_2567_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2567_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2565_; 
v___x_2562_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__49);
v___x_2563_ = lean_string_append(v___x_2562_, v_a_2558_);
lean_dec(v_a_2558_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v___x_2563_);
v___x_2565_ = v___x_2560_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2563_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
else
{
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec(v_a_2555_);
lean_dec(v_a_2534_);
lean_dec(v_a_2513_);
lean_dec(v_a_2492_);
lean_dec(v_a_2471_);
lean_dec(v_a_2450_);
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2568_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2557_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2557_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
lean_ctor_set_tag(v___x_2570_, 0);
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v_a_2576_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2576_);
lean_dec_ref(v___x_2557_);
v___x_2577_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__14));
lean_inc(v_json_2408_);
v___x_2578_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12(v_json_2408_, v___x_2577_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2588_; 
lean_dec(v_a_2576_);
lean_dec(v_a_2555_);
lean_dec(v_a_2534_);
lean_dec(v_a_2513_);
lean_dec(v_a_2492_);
lean_dec(v_a_2471_);
lean_dec(v_a_2450_);
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2588_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2588_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2583_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__56);
v___x_2584_ = lean_string_append(v___x_2583_, v_a_2579_);
lean_dec(v_a_2579_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2584_);
v___x_2586_ = v___x_2581_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
else
{
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec(v_a_2576_);
lean_dec(v_a_2555_);
lean_dec(v_a_2534_);
lean_dec(v_a_2513_);
lean_dec(v_a_2492_);
lean_dec(v_a_2471_);
lean_dec(v_a_2450_);
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2589_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2578_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2578_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set_tag(v___x_2591_, 0);
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v_a_2597_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2597_);
lean_dec_ref(v___x_2578_);
v___x_2598_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__15));
lean_inc(v_json_2408_);
v___x_2599_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__13(v_json_2408_, v___x_2598_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2609_; 
lean_dec(v_a_2597_);
lean_dec(v_a_2576_);
lean_dec(v_a_2555_);
lean_dec(v_a_2534_);
lean_dec(v_a_2513_);
lean_dec(v_a_2492_);
lean_dec(v_a_2471_);
lean_dec(v_a_2450_);
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2602_ = v___x_2599_;
v_isShared_2603_ = v_isSharedCheck_2609_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2599_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2609_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2607_; 
v___x_2604_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63, &l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63_once, _init_l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___redArg___closed__63);
v___x_2605_ = lean_string_append(v___x_2604_, v_a_2600_);
lean_dec(v_a_2600_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v___x_2605_);
v___x_2607_ = v___x_2602_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
else
{
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_dec(v_a_2597_);
lean_dec(v_a_2576_);
lean_dec(v_a_2555_);
lean_dec(v_a_2534_);
lean_dec(v_a_2513_);
lean_dec(v_a_2492_);
lean_dec(v_a_2471_);
lean_dec(v_a_2450_);
lean_dec(v_a_2429_);
lean_dec(v_json_2408_);
v_a_2610_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2599_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2599_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
lean_ctor_set_tag(v___x_2612_, 0);
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2629_; 
v_a_2618_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2618_);
lean_dec_ref(v___x_2599_);
v___x_2619_ = ((lean_object*)(l_Lean_Lsp_instToJsonDiagnosticWith_toJson___redArg___closed__16));
v___x_2620_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__14(v_json_2408_, v___x_2619_);
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2623_ = v___x_2620_;
v_isShared_2624_ = v_isSharedCheck_2629_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2620_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2629_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2625_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2625_, 0, v_a_2429_);
lean_ctor_set(v___x_2625_, 1, v_a_2450_);
lean_ctor_set(v___x_2625_, 2, v_a_2471_);
lean_ctor_set(v___x_2625_, 3, v_a_2492_);
lean_ctor_set(v___x_2625_, 4, v_a_2513_);
lean_ctor_set(v___x_2625_, 5, v_a_2534_);
lean_ctor_set(v___x_2625_, 6, v_a_2555_);
lean_ctor_set(v___x_2625_, 7, v_a_2576_);
lean_ctor_set(v___x_2625_, 8, v_a_2597_);
lean_ctor_set(v___x_2625_, 9, v_a_2618_);
lean_ctor_set(v___x_2625_, 10, v_a_2621_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v___x_2625_);
v___x_2627_ = v___x_2623_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(size_t v_sz_2630_, size_t v_i_2631_, lean_object* v_bs_2632_){
_start:
{
uint8_t v___x_2633_; 
v___x_2633_ = lean_usize_dec_lt(v_i_2631_, v_sz_2630_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; 
v___x_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2634_, 0, v_bs_2632_);
return v___x_2634_;
}
else
{
lean_object* v_v_2635_; lean_object* v___x_2636_; 
v_v_2635_ = lean_array_uget_borrowed(v_bs_2632_, v_i_2631_);
lean_inc(v_v_2635_);
v___x_2636_ = l_Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5(v_v_2635_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec_ref(v_bs_2632_);
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2636_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
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
lean_object* v_a_2645_; lean_object* v___x_2646_; lean_object* v_bs_x27_2647_; size_t v___x_2648_; size_t v___x_2649_; lean_object* v___x_2650_; 
v_a_2645_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2645_);
lean_dec_ref(v___x_2636_);
v___x_2646_ = lean_unsigned_to_nat(0u);
v_bs_x27_2647_ = lean_array_uset(v_bs_2632_, v_i_2631_, v___x_2646_);
v___x_2648_ = ((size_t)1ULL);
v___x_2649_ = lean_usize_add(v_i_2631_, v___x_2648_);
v___x_2650_ = lean_array_uset(v_bs_x27_2647_, v_i_2631_, v_a_2645_);
v_i_2631_ = v___x_2649_;
v_bs_2632_ = v___x_2650_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6___boxed(lean_object* v_sz_2652_, lean_object* v_i_2653_, lean_object* v_bs_2654_){
_start:
{
size_t v_sz_boxed_2655_; size_t v_i_boxed_2656_; lean_object* v_res_2657_; 
v_sz_boxed_2655_ = lean_unbox_usize(v_sz_2652_);
lean_dec(v_sz_2652_);
v_i_boxed_2656_ = lean_unbox_usize(v_i_2653_);
lean_dec(v_i_2653_);
v_res_2657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(v_sz_boxed_2655_, v_i_boxed_2656_, v_bs_2654_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4(lean_object* v_x_2658_){
_start:
{
if (lean_obj_tag(v_x_2658_) == 4)
{
lean_object* v_elems_2659_; size_t v_sz_2660_; size_t v___x_2661_; lean_object* v___x_2662_; 
v_elems_2659_ = lean_ctor_get(v_x_2658_, 0);
lean_inc_ref(v_elems_2659_);
lean_dec_ref(v_x_2658_);
v_sz_2660_ = lean_array_size(v_elems_2659_);
v___x_2661_ = ((size_t)0ULL);
v___x_2662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__6(v_sz_2660_, v___x_2661_, v_elems_2659_);
return v___x_2662_;
}
else
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2663_ = ((lean_object*)(l_Array_fromJson_x3f___at___00Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticWith_fromJson___at___00Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4_spec__5_spec__12_spec__18_spec__21___closed__0));
v___x_2664_ = lean_unsigned_to_nat(80u);
v___x_2665_ = l_Lean_Json_pretty(v_x_2658_, v___x_2664_);
v___x_2666_ = lean_string_append(v___x_2663_, v___x_2665_);
lean_dec_ref(v___x_2665_);
v___x_2667_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticSeverity___lam__0___closed__1));
v___x_2668_ = lean_string_append(v___x_2666_, v___x_2667_);
v___x_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
return v___x_2669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(lean_object* v_j_2670_, lean_object* v_k_2671_){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2672_ = l_Lean_Json_getObjValD(v_j_2670_, v_k_2671_);
v___x_2673_ = l_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2_spec__4(v___x_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2___boxed(lean_object* v_j_2674_, lean_object* v_k_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(v_j_2674_, v_k_2675_);
lean_dec_ref(v_k_2675_);
return v_res_2676_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2682_ = 1;
v___x_2683_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__1));
v___x_2684_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2683_, v___x_2682_);
return v___x_2684_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2685_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__5));
v___x_2686_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__2);
v___x_2687_ = lean_string_append(v___x_2686_, v___x_2685_);
return v___x_2687_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5(void){
_start:
{
uint8_t v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2690_ = 1;
v___x_2691_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__4));
v___x_2692_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2691_, v___x_2690_);
return v___x_2692_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2693_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__5);
v___x_2694_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
v___x_2695_ = lean_string_append(v___x_2694_, v___x_2693_);
return v___x_2695_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_2697_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__6);
v___x_2698_ = lean_string_append(v___x_2697_, v___x_2696_);
return v___x_2698_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10(void){
_start:
{
uint8_t v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2702_ = 1;
v___x_2703_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__9));
v___x_2704_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2703_, v___x_2702_);
return v___x_2704_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2705_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__10);
v___x_2706_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
v___x_2707_ = lean_string_append(v___x_2706_, v___x_2705_);
return v___x_2707_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2708_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_2709_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__11);
v___x_2710_ = lean_string_append(v___x_2709_, v___x_2708_);
return v___x_2710_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15(void){
_start:
{
uint8_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2714_ = 1;
v___x_2715_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__14));
v___x_2716_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2715_, v___x_2714_);
return v___x_2716_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2717_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__15);
v___x_2718_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
v___x_2719_ = lean_string_append(v___x_2718_, v___x_2717_);
return v___x_2719_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2720_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_2721_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__16);
v___x_2722_ = lean_string_append(v___x_2721_, v___x_2720_);
return v___x_2722_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19(void){
_start:
{
uint8_t v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2725_ = 1;
v___x_2726_ = ((lean_object*)(l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__18));
v___x_2727_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2726_, v___x_2725_);
return v___x_2727_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20(void){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2728_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__19);
v___x_2729_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__3);
v___x_2730_ = lean_string_append(v___x_2729_, v___x_2728_);
return v___x_2730_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21(void){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2731_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson___closed__10));
v___x_2732_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__20);
v___x_2733_ = lean_string_append(v___x_2732_, v___x_2731_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson(lean_object* v_json_2734_){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__0));
lean_inc(v_json_2734_);
v___x_2736_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDiagnosticRelatedInformation_fromJson_spec__1(v_json_2734_, v___x_2735_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2746_; 
lean_dec(v_json_2734_);
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2739_ = v___x_2736_;
v_isShared_2740_ = v_isSharedCheck_2746_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2736_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2746_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2744_; 
v___x_2741_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__7);
v___x_2742_ = lean_string_append(v___x_2741_, v_a_2737_);
lean_dec(v_a_2737_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 0, v___x_2742_);
v___x_2744_ = v___x_2739_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2742_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
else
{
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec(v_json_2734_);
v_a_2747_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2736_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2736_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
lean_ctor_set_tag(v___x_2749_, 0);
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v_a_2755_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2755_);
lean_dec_ref(v___x_2736_);
v___x_2756_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__1));
lean_inc(v_json_2734_);
v___x_2757_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__0(v_json_2734_, v___x_2756_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2767_; 
lean_dec(v_a_2755_);
lean_dec(v_json_2734_);
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2760_ = v___x_2757_;
v_isShared_2761_ = v_isSharedCheck_2767_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2767_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2765_; 
v___x_2762_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__12);
v___x_2763_ = lean_string_append(v___x_2762_, v_a_2758_);
lean_dec(v_a_2758_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2763_);
v___x_2765_ = v___x_2760_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2763_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
else
{
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec(v_a_2755_);
lean_dec(v_json_2734_);
v_a_2768_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2757_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2757_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set_tag(v___x_2770_, 0);
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_a_2776_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_a_2776_);
lean_dec_ref(v___x_2757_);
v___x_2777_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__2));
lean_inc(v_json_2734_);
v___x_2778_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__1(v_json_2734_, v___x_2777_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2788_; 
lean_dec(v_a_2776_);
lean_dec(v_a_2755_);
lean_dec(v_json_2734_);
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2788_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2788_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2786_; 
v___x_2783_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__17);
v___x_2784_ = lean_string_append(v___x_2783_, v_a_2779_);
lean_dec(v_a_2779_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2784_);
v___x_2786_ = v___x_2781_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
else
{
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec(v_a_2776_);
lean_dec(v_a_2755_);
lean_dec(v_json_2734_);
v_a_2789_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2778_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2778_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set_tag(v___x_2791_, 0);
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
else
{
lean_object* v_a_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_a_2797_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2797_);
lean_dec_ref(v___x_2778_);
v___x_2798_ = ((lean_object*)(l_Lean_Lsp_instToJsonPublishDiagnosticsParams_toJson___closed__3));
v___x_2799_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson_spec__2(v_json_2734_, v___x_2798_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2809_; 
lean_dec(v_a_2797_);
lean_dec(v_a_2776_);
lean_dec(v_a_2755_);
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2802_ = v___x_2799_;
v_isShared_2803_ = v_isSharedCheck_2809_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2799_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2809_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2807_; 
v___x_2804_ = lean_obj_once(&l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21, &l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonPublishDiagnosticsParams_fromJson___closed__21);
v___x_2805_ = lean_string_append(v___x_2804_, v_a_2800_);
lean_dec(v_a_2800_);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v___x_2805_);
v___x_2807_ = v___x_2802_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2805_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
else
{
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec(v_a_2797_);
lean_dec(v_a_2776_);
lean_dec(v_a_2755_);
v_a_2810_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2799_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2799_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
lean_ctor_set_tag(v___x_2812_, 0);
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2826_; 
v_a_2818_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2820_ = v___x_2799_;
v_isShared_2821_ = v_isSharedCheck_2826_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2799_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2826_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2822_; lean_object* v___x_2824_; 
v___x_2822_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2822_, 0, v_a_2755_);
lean_ctor_set(v___x_2822_, 1, v_a_2776_);
lean_ctor_set(v___x_2822_, 2, v_a_2797_);
lean_ctor_set(v___x_2822_, 3, v_a_2818_);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v___x_2822_);
v___x_2824_ = v___x_2820_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
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
