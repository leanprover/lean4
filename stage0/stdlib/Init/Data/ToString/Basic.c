// Lean compiler output
// Module: Init.Data.ToString.Basic
// Imports: public import Init.Data.Repr import Init.Data.Char.Basic
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
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_string_isprefixof(lean_object*, lean_object*);
uint8_t lean_string_any(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Substring_Raw_Internal_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instToStringString___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringString___closed__0 = (const lean_object*)&l_instToStringString___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringString = (const lean_object*)&l_instToStringString___closed__0_value;
static const lean_closure_object l_instToStringRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Substring_Raw_Internal_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringRaw___closed__0 = (const lean_object*)&l_instToStringRaw___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringRaw = (const lean_object*)&l_instToStringRaw___closed__0_value;
static const lean_string_object l_instToStringChar___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_instToStringChar___lam__0___closed__0 = (const lean_object*)&l_instToStringChar___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringChar___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_instToStringChar___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringChar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringChar___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringChar___closed__0 = (const lean_object*)&l_instToStringChar___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringChar = (const lean_object*)&l_instToStringChar___closed__0_value;
static const lean_string_object l_instToStringBool___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_instToStringBool___lam__0___closed__0 = (const lean_object*)&l_instToStringBool___lam__0___closed__0_value;
static const lean_string_object l_instToStringBool___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_instToStringBool___lam__0___closed__1 = (const lean_object*)&l_instToStringBool___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instToStringBool___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instToStringBool___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringBool___closed__0 = (const lean_object*)&l_instToStringBool___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringBool = (const lean_object*)&l_instToStringBool___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringDecidable___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instToStringDecidable___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringDecidable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringDecidable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringDecidable___closed__0 = (const lean_object*)&l_instToStringDecidable___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringDecidable(lean_object*);
static const lean_string_object l_instToStringPUnit___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "()"};
static const lean_object* l_instToStringPUnit___lam__0___closed__0 = (const lean_object*)&l_instToStringPUnit___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringPUnit___lam__0(lean_object*);
static const lean_closure_object l_instToStringPUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringPUnit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringPUnit___closed__0 = (const lean_object*)&l_instToStringPUnit___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringPUnit = (const lean_object*)&l_instToStringPUnit___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringULift___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringULift___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringULift(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_instToStringUnit = (const lean_object*)&l_instToStringPUnit___closed__0_value;
static const lean_closure_object l_instToStringNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_reprFast, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringNat___closed__0 = (const lean_object*)&l_instToStringNat___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringNat = (const lean_object*)&l_instToStringNat___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringRaw__1 = (const lean_object*)&l_instToStringNat___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringFin(lean_object*);
LEAN_EXPORT lean_object* l_instToStringFin___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringUInt8___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringUInt8___closed__0 = (const lean_object*)&l_instToStringUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringUInt8 = (const lean_object*)&l_instToStringUInt8___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0(uint16_t);
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringUInt16___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringUInt16___closed__0 = (const lean_object*)&l_instToStringUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringUInt16 = (const lean_object*)&l_instToStringUInt16___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringUInt32___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringUInt32___closed__0 = (const lean_object*)&l_instToStringUInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringUInt32 = (const lean_object*)&l_instToStringUInt32___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringUInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringUInt64___closed__0 = (const lean_object*)&l_instToStringUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringUInt64 = (const lean_object*)&l_instToStringUInt64___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0(size_t);
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringUSize___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringUSize___closed__0 = (const lean_object*)&l_instToStringUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringUSize = (const lean_object*)&l_instToStringUSize___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringFormat___lam__0(lean_object*);
static const lean_closure_object l_instToStringFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringFormat___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringFormat___closed__0 = (const lean_object*)&l_instToStringFormat___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringFormat = (const lean_object*)&l_instToStringFormat___closed__0_value;
LEAN_EXPORT uint8_t l_addParenHeuristic___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_addParenHeuristic___lam__0___boxed(lean_object*);
static const lean_closure_object l_addParenHeuristic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_addParenHeuristic___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_addParenHeuristic___closed__0 = (const lean_object*)&l_addParenHeuristic___closed__0_value;
static const lean_string_object l_addParenHeuristic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_addParenHeuristic___closed__1 = (const lean_object*)&l_addParenHeuristic___closed__1_value;
static const lean_string_object l_addParenHeuristic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_addParenHeuristic___closed__2 = (const lean_object*)&l_addParenHeuristic___closed__2_value;
static const lean_string_object l_addParenHeuristic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_addParenHeuristic___closed__3 = (const lean_object*)&l_addParenHeuristic___closed__3_value;
static const lean_string_object l_addParenHeuristic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_addParenHeuristic___closed__4 = (const lean_object*)&l_addParenHeuristic___closed__4_value;
static const lean_string_object l_addParenHeuristic___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_addParenHeuristic___closed__5 = (const lean_object*)&l_addParenHeuristic___closed__5_value;
LEAN_EXPORT lean_object* l_addParenHeuristic(lean_object*);
static const lean_string_object l_instToStringOption___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_instToStringOption___redArg___lam__0___closed__0 = (const lean_object*)&l_instToStringOption___redArg___lam__0___closed__0_value;
static const lean_string_object l_instToStringOption___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "(some "};
static const lean_object* l_instToStringOption___redArg___lam__0___closed__1 = (const lean_object*)&l_instToStringOption___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instToStringOption___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringOption(lean_object*, lean_object*);
static const lean_string_object l_instToStringSum___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "(inl "};
static const lean_object* l_instToStringSum___redArg___lam__0___closed__0 = (const lean_object*)&l_instToStringSum___redArg___lam__0___closed__0_value;
static const lean_string_object l_instToStringSum___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "(inr "};
static const lean_object* l_instToStringSum___redArg___lam__0___closed__1 = (const lean_object*)&l_instToStringSum___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instToStringSum___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSum___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSum(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_instToStringProd___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_instToStringProd___redArg___lam__0___closed__0 = (const lean_object*)&l_instToStringProd___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_instToStringProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringProd(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_instToStringSigma___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_instToStringSigma___redArg___lam__0___closed__0 = (const lean_object*)&l_instToStringSigma___redArg___lam__0___closed__0_value;
static const lean_string_object l_instToStringSigma___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_instToStringSigma___redArg___lam__0___closed__1 = (const lean_object*)&l_instToStringSigma___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instToStringSigma___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSigma___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSigma(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringSubtype(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_instToStringExcept___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l_instToStringExcept___redArg___lam__0___closed__0 = (const lean_object*)&l_instToStringExcept___redArg___lam__0___closed__0_value;
static const lean_string_object l_instToStringExcept___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ok: "};
static const lean_object* l_instToStringExcept___redArg___lam__0___closed__1 = (const lean_object*)&l_instToStringExcept___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instToStringExcept___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringExcept___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringExcept(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_instReprExcept___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Except.error "};
static const lean_object* l_instReprExcept___redArg___lam__0___closed__0 = (const lean_object*)&l_instReprExcept___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_instReprExcept___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprExcept___redArg___lam__0___closed__0_value)}};
static const lean_object* l_instReprExcept___redArg___lam__0___closed__1 = (const lean_object*)&l_instReprExcept___redArg___lam__0___closed__1_value;
static const lean_string_object l_instReprExcept___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Except.ok "};
static const lean_object* l_instReprExcept___redArg___lam__0___closed__2 = (const lean_object*)&l_instReprExcept___redArg___lam__0___closed__2_value;
static const lean_ctor_object l_instReprExcept___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprExcept___redArg___lam__0___closed__2_value)}};
static const lean_object* l_instReprExcept___redArg___lam__0___closed__3 = (const lean_object*)&l_instReprExcept___redArg___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprExcept___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprExcept(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___redArg(lean_object* v_inst_1_){
_start:
{
lean_inc_ref(v_inst_1_);
return v_inst_1_;
}
}
LEAN_EXPORT lean_object* l_instToStringId___redArg___boxed(lean_object* v_inst_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_instToStringId___redArg(v_inst_2_);
lean_dec_ref(v_inst_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_instToStringId(lean_object* v_00_u03b1_4_, lean_object* v_inst_5_){
_start:
{
lean_inc_ref(v_inst_5_);
return v_inst_5_;
}
}
LEAN_EXPORT lean_object* l_instToStringId___boxed(lean_object* v_00_u03b1_6_, lean_object* v_inst_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_instToStringId(v_00_u03b1_6_, v_inst_7_);
lean_dec_ref(v_inst_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___redArg(lean_object* v_inst_9_){
_start:
{
lean_inc_ref(v_inst_9_);
return v_inst_9_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___redArg___boxed(lean_object* v_inst_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_instToStringId__1___redArg(v_inst_10_);
lean_dec_ref(v_inst_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1(lean_object* v_00_u03b1_12_, lean_object* v_inst_13_){
_start:
{
lean_inc_ref(v_inst_13_);
return v_inst_13_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___boxed(lean_object* v_00_u03b1_14_, lean_object* v_inst_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_instToStringId__1(v_00_u03b1_14_, v_inst_15_);
lean_dec_ref(v_inst_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_instToStringString___lam__0(lean_object* v_s_17_){
_start:
{
lean_inc_ref(v_s_17_);
return v_s_17_;
}
}
LEAN_EXPORT lean_object* l_instToStringString___lam__0___boxed(lean_object* v_s_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_instToStringString___lam__0(v_s_18_);
lean_dec_ref(v_s_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_instToStringChar___lam__0(uint32_t v_c_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = ((lean_object*)(l_instToStringChar___lam__0___closed__0));
v___x_27_ = lean_string_push(v___x_26_, v_c_25_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_instToStringChar___lam__0___boxed(lean_object* v_c_28_){
_start:
{
uint32_t v_c_boxed_29_; lean_object* v_res_30_; 
v_c_boxed_29_ = lean_unbox_uint32(v_c_28_);
lean_dec(v_c_28_);
v_res_30_ = l_instToStringChar___lam__0(v_c_boxed_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_instToStringBool___lam__0(uint8_t v_b_35_){
_start:
{
if (v_b_35_ == 0)
{
lean_object* v___x_36_; 
v___x_36_ = ((lean_object*)(l_instToStringBool___lam__0___closed__0));
return v___x_36_;
}
else
{
lean_object* v___x_37_; 
v___x_37_ = ((lean_object*)(l_instToStringBool___lam__0___closed__1));
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringBool___lam__0___boxed(lean_object* v_b_38_){
_start:
{
uint8_t v_b_boxed_39_; lean_object* v_res_40_; 
v_b_boxed_39_ = lean_unbox(v_b_38_);
v_res_40_ = l_instToStringBool___lam__0(v_b_boxed_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable___lam__0(uint8_t v_h_43_){
_start:
{
if (v_h_43_ == 0)
{
lean_object* v___x_44_; 
v___x_44_ = ((lean_object*)(l_instToStringBool___lam__0___closed__0));
return v___x_44_;
}
else
{
lean_object* v___x_45_; 
v___x_45_ = ((lean_object*)(l_instToStringBool___lam__0___closed__1));
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable___lam__0___boxed(lean_object* v_h_46_){
_start:
{
uint8_t v_h_boxed_47_; lean_object* v_res_48_; 
v_h_boxed_47_ = lean_unbox(v_h_46_);
v_res_48_ = l_instToStringDecidable___lam__0(v_h_boxed_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable(lean_object* v_p_50_){
_start:
{
lean_object* v___f_51_; 
v___f_51_ = ((lean_object*)(l_instToStringDecidable___closed__0));
return v___f_51_;
}
}
LEAN_EXPORT lean_object* l_instToStringPUnit___lam__0(lean_object* v_x_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = ((lean_object*)(l_instToStringPUnit___lam__0___closed__0));
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_instToStringULift___redArg___lam__0(lean_object* v_inst_57_, lean_object* v_v_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_apply_1(v_inst_57_, v_v_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_instToStringULift___redArg(lean_object* v_inst_60_){
_start:
{
lean_object* v___f_61_; 
v___f_61_ = lean_alloc_closure((void*)(l_instToStringULift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_61_, 0, v_inst_60_);
return v___f_61_;
}
}
LEAN_EXPORT lean_object* l_instToStringULift(lean_object* v_00_u03b1_62_, lean_object* v_inst_63_){
_start:
{
lean_object* v___f_64_; 
v___f_64_ = lean_alloc_closure((void*)(l_instToStringULift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_64_, 0, v_inst_63_);
return v___f_64_;
}
}
LEAN_EXPORT lean_object* l_instToStringFin(lean_object* v_n_69_){
_start:
{
lean_object* v___f_70_; 
v___f_70_ = ((lean_object*)(l_instToStringNat___closed__0));
return v___f_70_;
}
}
LEAN_EXPORT lean_object* l_instToStringFin___boxed(lean_object* v_n_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_instToStringFin(v_n_71_);
lean_dec(v_n_71_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0(uint8_t v_n_73_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_uint8_to_nat(v_n_73_);
v___x_75_ = l_Nat_reprFast(v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0___boxed(lean_object* v_n_76_){
_start:
{
uint8_t v_n_boxed_77_; lean_object* v_res_78_; 
v_n_boxed_77_ = lean_unbox(v_n_76_);
v_res_78_ = l_instToStringUInt8___lam__0(v_n_boxed_77_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0(uint16_t v_n_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_uint16_to_nat(v_n_81_);
v___x_83_ = l_Nat_reprFast(v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0___boxed(lean_object* v_n_84_){
_start:
{
uint16_t v_n_boxed_85_; lean_object* v_res_86_; 
v_n_boxed_85_ = lean_unbox(v_n_84_);
v_res_86_ = l_instToStringUInt16___lam__0(v_n_boxed_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0(uint32_t v_n_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_uint32_to_nat(v_n_89_);
v___x_91_ = l_Nat_reprFast(v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0___boxed(lean_object* v_n_92_){
_start:
{
uint32_t v_n_boxed_93_; lean_object* v_res_94_; 
v_n_boxed_93_ = lean_unbox_uint32(v_n_92_);
lean_dec(v_n_92_);
v_res_94_ = l_instToStringUInt32___lam__0(v_n_boxed_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0(uint64_t v_n_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_uint64_to_nat(v_n_97_);
v___x_99_ = l_Nat_reprFast(v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0___boxed(lean_object* v_n_100_){
_start:
{
uint64_t v_n_boxed_101_; lean_object* v_res_102_; 
v_n_boxed_101_ = lean_unbox_uint64(v_n_100_);
lean_dec_ref(v_n_100_);
v_res_102_ = l_instToStringUInt64___lam__0(v_n_boxed_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0(size_t v_n_105_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_usize_to_nat(v_n_105_);
v___x_107_ = l_Nat_reprFast(v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0___boxed(lean_object* v_n_108_){
_start:
{
size_t v_n_boxed_109_; lean_object* v_res_110_; 
v_n_boxed_109_ = lean_unbox_usize(v_n_108_);
lean_dec(v_n_108_);
v_res_110_ = l_instToStringUSize___lam__0(v_n_boxed_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_instToStringFormat___lam__0(lean_object* v_f_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = l_Std_Format_defWidth;
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = l_Std_Format_pretty(v_f_113_, v___x_114_, v___x_115_, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT uint8_t l_addParenHeuristic___lam__0(uint32_t v___y_119_){
_start:
{
uint8_t v___y_121_; uint32_t v___x_126_; uint8_t v___x_127_; 
v___x_126_ = 32;
v___x_127_ = lean_uint32_dec_eq(v___y_119_, v___x_126_);
if (v___x_127_ == 0)
{
uint32_t v___x_128_; uint8_t v___x_129_; 
v___x_128_ = 9;
v___x_129_ = lean_uint32_dec_eq(v___y_119_, v___x_128_);
v___y_121_ = v___x_129_;
goto v___jp_120_;
}
else
{
v___y_121_ = v___x_127_;
goto v___jp_120_;
}
v___jp_120_:
{
if (v___y_121_ == 0)
{
uint32_t v___x_122_; uint8_t v___x_123_; 
v___x_122_ = 13;
v___x_123_ = lean_uint32_dec_eq(v___y_119_, v___x_122_);
if (v___x_123_ == 0)
{
uint32_t v___x_124_; uint8_t v___x_125_; 
v___x_124_ = 10;
v___x_125_ = lean_uint32_dec_eq(v___y_119_, v___x_124_);
return v___x_125_;
}
else
{
return v___x_123_;
}
}
else
{
return v___y_121_;
}
}
}
}
LEAN_EXPORT lean_object* l_addParenHeuristic___lam__0___boxed(lean_object* v___y_130_){
_start:
{
uint32_t v___y_211__boxed_131_; uint8_t v_res_132_; lean_object* v_r_133_; 
v___y_211__boxed_131_ = lean_unbox_uint32(v___y_130_);
lean_dec(v___y_130_);
v_res_132_ = l_addParenHeuristic___lam__0(v___y_211__boxed_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT lean_object* l_addParenHeuristic(lean_object* v_s_140_){
_start:
{
lean_object* v___f_141_; lean_object* v___x_142_; uint8_t v___y_144_; uint8_t v___x_153_; 
v___f_141_ = ((lean_object*)(l_addParenHeuristic___closed__0));
v___x_142_ = ((lean_object*)(l_addParenHeuristic___closed__1));
lean_inc_ref(v_s_140_);
v___x_153_ = lean_string_isprefixof(v___x_142_, v_s_140_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = ((lean_object*)(l_addParenHeuristic___closed__5));
lean_inc_ref(v_s_140_);
v___x_155_ = lean_string_isprefixof(v___x_154_, v_s_140_);
v___y_144_ = v___x_155_;
goto v___jp_143_;
}
else
{
v___y_144_ = v___x_153_;
goto v___jp_143_;
}
v___jp_143_:
{
if (v___y_144_ == 0)
{
lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_145_ = ((lean_object*)(l_addParenHeuristic___closed__2));
lean_inc_ref(v_s_140_);
v___x_146_ = lean_string_isprefixof(v___x_145_, v_s_140_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_147_ = ((lean_object*)(l_addParenHeuristic___closed__3));
lean_inc_ref(v_s_140_);
v___x_148_ = lean_string_isprefixof(v___x_147_, v_s_140_);
if (v___x_148_ == 0)
{
uint8_t v___x_149_; 
lean_inc_ref(v_s_140_);
v___x_149_ = lean_string_any(v_s_140_, v___f_141_);
if (v___x_149_ == 0)
{
return v_s_140_;
}
else
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lean_string_append(v___x_142_, v_s_140_);
lean_dec_ref(v_s_140_);
v___x_151_ = ((lean_object*)(l_addParenHeuristic___closed__4));
v___x_152_ = lean_string_append(v___x_150_, v___x_151_);
return v___x_152_;
}
}
else
{
return v_s_140_;
}
}
else
{
return v_s_140_;
}
}
else
{
return v_s_140_;
}
}
}
}
LEAN_EXPORT lean_object* l_instToStringOption___redArg___lam__0(lean_object* v_inst_158_, lean_object* v_x_159_){
_start:
{
if (lean_obj_tag(v_x_159_) == 0)
{
lean_object* v___x_160_; 
lean_dec_ref(v_inst_158_);
v___x_160_ = ((lean_object*)(l_instToStringOption___redArg___lam__0___closed__0));
return v___x_160_;
}
else
{
lean_object* v_val_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_val_161_ = lean_ctor_get(v_x_159_, 0);
lean_inc(v_val_161_);
lean_dec_ref(v_x_159_);
v___x_162_ = ((lean_object*)(l_instToStringOption___redArg___lam__0___closed__1));
v___x_163_ = lean_apply_1(v_inst_158_, v_val_161_);
v___x_164_ = l_addParenHeuristic(v___x_163_);
v___x_165_ = lean_string_append(v___x_162_, v___x_164_);
lean_dec_ref(v___x_164_);
v___x_166_ = ((lean_object*)(l_addParenHeuristic___closed__4));
v___x_167_ = lean_string_append(v___x_165_, v___x_166_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringOption___redArg(lean_object* v_inst_168_){
_start:
{
lean_object* v___f_169_; 
v___f_169_ = lean_alloc_closure((void*)(l_instToStringOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_169_, 0, v_inst_168_);
return v___f_169_;
}
}
LEAN_EXPORT lean_object* l_instToStringOption(lean_object* v_00_u03b1_170_, lean_object* v_inst_171_){
_start:
{
lean_object* v___f_172_; 
v___f_172_ = lean_alloc_closure((void*)(l_instToStringOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_172_, 0, v_inst_171_);
return v___f_172_;
}
}
LEAN_EXPORT lean_object* l_instToStringSum___redArg___lam__0(lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_x_177_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
lean_object* v_val_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec_ref(v_inst_176_);
v_val_178_ = lean_ctor_get(v_x_177_, 0);
lean_inc(v_val_178_);
lean_dec_ref(v_x_177_);
v___x_179_ = ((lean_object*)(l_instToStringSum___redArg___lam__0___closed__0));
v___x_180_ = lean_apply_1(v_inst_175_, v_val_178_);
v___x_181_ = l_addParenHeuristic(v___x_180_);
v___x_182_ = lean_string_append(v___x_179_, v___x_181_);
lean_dec_ref(v___x_181_);
v___x_183_ = ((lean_object*)(l_addParenHeuristic___closed__4));
v___x_184_ = lean_string_append(v___x_182_, v___x_183_);
return v___x_184_;
}
else
{
lean_object* v_val_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec_ref(v_inst_175_);
v_val_185_ = lean_ctor_get(v_x_177_, 0);
lean_inc(v_val_185_);
lean_dec_ref(v_x_177_);
v___x_186_ = ((lean_object*)(l_instToStringSum___redArg___lam__0___closed__1));
v___x_187_ = lean_apply_1(v_inst_176_, v_val_185_);
v___x_188_ = l_addParenHeuristic(v___x_187_);
v___x_189_ = lean_string_append(v___x_186_, v___x_188_);
lean_dec_ref(v___x_188_);
v___x_190_ = ((lean_object*)(l_addParenHeuristic___closed__4));
v___x_191_ = lean_string_append(v___x_189_, v___x_190_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringSum___redArg(lean_object* v_inst_192_, lean_object* v_inst_193_){
_start:
{
lean_object* v___f_194_; 
v___f_194_ = lean_alloc_closure((void*)(l_instToStringSum___redArg___lam__0), 3, 2);
lean_closure_set(v___f_194_, 0, v_inst_192_);
lean_closure_set(v___f_194_, 1, v_inst_193_);
return v___f_194_;
}
}
LEAN_EXPORT lean_object* l_instToStringSum(lean_object* v_00_u03b1_195_, lean_object* v_00_u03b2_196_, lean_object* v_inst_197_, lean_object* v_inst_198_){
_start:
{
lean_object* v___f_199_; 
v___f_199_ = lean_alloc_closure((void*)(l_instToStringSum___redArg___lam__0), 3, 2);
lean_closure_set(v___f_199_, 0, v_inst_197_);
lean_closure_set(v___f_199_, 1, v_inst_198_);
return v___f_199_;
}
}
LEAN_EXPORT lean_object* l_instToStringProd___redArg___lam__0(lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_x_203_){
_start:
{
lean_object* v_fst_204_; lean_object* v_snd_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_fst_204_ = lean_ctor_get(v_x_203_, 0);
lean_inc(v_fst_204_);
v_snd_205_ = lean_ctor_get(v_x_203_, 1);
lean_inc(v_snd_205_);
lean_dec_ref(v_x_203_);
v___x_206_ = ((lean_object*)(l_addParenHeuristic___closed__1));
v___x_207_ = lean_apply_1(v_inst_201_, v_fst_204_);
v___x_208_ = lean_string_append(v___x_206_, v___x_207_);
lean_dec_ref(v___x_207_);
v___x_209_ = ((lean_object*)(l_instToStringProd___redArg___lam__0___closed__0));
v___x_210_ = lean_string_append(v___x_208_, v___x_209_);
v___x_211_ = lean_apply_1(v_inst_202_, v_snd_205_);
v___x_212_ = lean_string_append(v___x_210_, v___x_211_);
lean_dec_ref(v___x_211_);
v___x_213_ = ((lean_object*)(l_addParenHeuristic___closed__4));
v___x_214_ = lean_string_append(v___x_212_, v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_instToStringProd___redArg(lean_object* v_inst_215_, lean_object* v_inst_216_){
_start:
{
lean_object* v___f_217_; 
v___f_217_ = lean_alloc_closure((void*)(l_instToStringProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_217_, 0, v_inst_215_);
lean_closure_set(v___f_217_, 1, v_inst_216_);
return v___f_217_;
}
}
LEAN_EXPORT lean_object* l_instToStringProd(lean_object* v_00_u03b1_218_, lean_object* v_00_u03b2_219_, lean_object* v_inst_220_, lean_object* v_inst_221_){
_start:
{
lean_object* v___f_222_; 
v___f_222_ = lean_alloc_closure((void*)(l_instToStringProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_222_, 0, v_inst_220_);
lean_closure_set(v___f_222_, 1, v_inst_221_);
return v___f_222_;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma___redArg___lam__0(lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_x_227_){
_start:
{
lean_object* v_fst_228_; lean_object* v_snd_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_fst_228_ = lean_ctor_get(v_x_227_, 0);
lean_inc(v_fst_228_);
v_snd_229_ = lean_ctor_get(v_x_227_, 1);
lean_inc(v_snd_229_);
lean_dec_ref(v_x_227_);
v___x_230_ = ((lean_object*)(l_instToStringSigma___redArg___lam__0___closed__0));
lean_inc(v_fst_228_);
v___x_231_ = lean_apply_1(v_inst_225_, v_fst_228_);
v___x_232_ = lean_string_append(v___x_230_, v___x_231_);
lean_dec_ref(v___x_231_);
v___x_233_ = ((lean_object*)(l_instToStringProd___redArg___lam__0___closed__0));
v___x_234_ = lean_string_append(v___x_232_, v___x_233_);
v___x_235_ = lean_apply_2(v_inst_226_, v_fst_228_, v_snd_229_);
v___x_236_ = lean_string_append(v___x_234_, v___x_235_);
lean_dec_ref(v___x_235_);
v___x_237_ = ((lean_object*)(l_instToStringSigma___redArg___lam__0___closed__1));
v___x_238_ = lean_string_append(v___x_236_, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma___redArg(lean_object* v_inst_239_, lean_object* v_inst_240_){
_start:
{
lean_object* v___f_241_; 
v___f_241_ = lean_alloc_closure((void*)(l_instToStringSigma___redArg___lam__0), 3, 2);
lean_closure_set(v___f_241_, 0, v_inst_239_);
lean_closure_set(v___f_241_, 1, v_inst_240_);
return v___f_241_;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma(lean_object* v_00_u03b1_242_, lean_object* v_00_u03b2_243_, lean_object* v_inst_244_, lean_object* v_inst_245_){
_start:
{
lean_object* v___f_246_; 
v___f_246_ = lean_alloc_closure((void*)(l_instToStringSigma___redArg___lam__0), 3, 2);
lean_closure_set(v___f_246_, 0, v_inst_244_);
lean_closure_set(v___f_246_, 1, v_inst_245_);
return v___f_246_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg___lam__0(lean_object* v_inst_247_, lean_object* v_s_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = lean_apply_1(v_inst_247_, v_s_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg(lean_object* v_inst_250_){
_start:
{
lean_object* v___f_251_; 
v___f_251_ = lean_alloc_closure((void*)(l_instToStringSubtype___redArg___lam__0), 2, 1);
lean_closure_set(v___f_251_, 0, v_inst_250_);
return v___f_251_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype(lean_object* v_00_u03b1_252_, lean_object* v_p_253_, lean_object* v_inst_254_){
_start:
{
lean_object* v___f_255_; 
v___f_255_ = lean_alloc_closure((void*)(l_instToStringSubtype___redArg___lam__0), 2, 1);
lean_closure_set(v___f_255_, 0, v_inst_254_);
return v___f_255_;
}
}
LEAN_EXPORT lean_object* l_instToStringExcept___redArg___lam__0(lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_x_260_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec_ref(v_inst_259_);
v_a_261_ = lean_ctor_get(v_x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref(v_x_260_);
v___x_262_ = ((lean_object*)(l_instToStringExcept___redArg___lam__0___closed__0));
v___x_263_ = lean_apply_1(v_inst_258_, v_a_261_);
v___x_264_ = lean_string_append(v___x_262_, v___x_263_);
lean_dec_ref(v___x_263_);
return v___x_264_;
}
else
{
lean_object* v_a_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec_ref(v_inst_258_);
v_a_265_ = lean_ctor_get(v_x_260_, 0);
lean_inc(v_a_265_);
lean_dec_ref(v_x_260_);
v___x_266_ = ((lean_object*)(l_instToStringExcept___redArg___lam__0___closed__1));
v___x_267_ = lean_apply_1(v_inst_259_, v_a_265_);
v___x_268_ = lean_string_append(v___x_266_, v___x_267_);
lean_dec_ref(v___x_267_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringExcept___redArg(lean_object* v_inst_269_, lean_object* v_inst_270_){
_start:
{
lean_object* v___f_271_; 
v___f_271_ = lean_alloc_closure((void*)(l_instToStringExcept___redArg___lam__0), 3, 2);
lean_closure_set(v___f_271_, 0, v_inst_269_);
lean_closure_set(v___f_271_, 1, v_inst_270_);
return v___f_271_;
}
}
LEAN_EXPORT lean_object* l_instToStringExcept(lean_object* v_00_u03b5_272_, lean_object* v_00_u03b1_273_, lean_object* v_inst_274_, lean_object* v_inst_275_){
_start:
{
lean_object* v___f_276_; 
v___f_276_ = lean_alloc_closure((void*)(l_instToStringExcept___redArg___lam__0), 3, 2);
lean_closure_set(v___f_276_, 0, v_inst_274_);
lean_closure_set(v___f_276_, 1, v_inst_275_);
return v___f_276_;
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0(lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
if (lean_obj_tag(v_x_285_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec_ref(v_inst_284_);
v_a_287_ = lean_ctor_get(v_x_285_, 0);
lean_inc(v_a_287_);
lean_dec_ref(v_x_285_);
v___x_288_ = ((lean_object*)(l_instReprExcept___redArg___lam__0___closed__1));
v___x_289_ = lean_unsigned_to_nat(1024u);
v___x_290_ = lean_apply_2(v_inst_283_, v_a_287_, v___x_289_);
v___x_291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_288_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = l_Repr_addAppParen(v___x_291_, v_x_286_);
return v___x_292_;
}
else
{
lean_object* v_a_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec_ref(v_inst_283_);
v_a_293_ = lean_ctor_get(v_x_285_, 0);
lean_inc(v_a_293_);
lean_dec_ref(v_x_285_);
v___x_294_ = ((lean_object*)(l_instReprExcept___redArg___lam__0___closed__3));
v___x_295_ = lean_unsigned_to_nat(1024u);
v___x_296_ = lean_apply_2(v_inst_284_, v_a_293_, v___x_295_);
v___x_297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_294_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = l_Repr_addAppParen(v___x_297_, v_x_286_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0___boxed(lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_instReprExcept___redArg___lam__0(v_inst_299_, v_inst_300_, v_x_301_, v_x_302_);
lean_dec(v_x_302_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg(lean_object* v_inst_304_, lean_object* v_inst_305_){
_start:
{
lean_object* v___f_306_; 
v___f_306_ = lean_alloc_closure((void*)(l_instReprExcept___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_306_, 0, v_inst_304_);
lean_closure_set(v___f_306_, 1, v_inst_305_);
return v___f_306_;
}
}
LEAN_EXPORT lean_object* l_instReprExcept(lean_object* v_00_u03b5_307_, lean_object* v_00_u03b1_308_, lean_object* v_inst_309_, lean_object* v_inst_310_){
_start:
{
lean_object* v___f_311_; 
v___f_311_ = lean_alloc_closure((void*)(l_instReprExcept___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_311_, 0, v_inst_309_);
lean_closure_set(v___f_311_, 1, v_inst_310_);
return v___f_311_;
}
}
lean_object* runtime_initialize_Init_Data_Repr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_ToString_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Repr(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_ToString_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
