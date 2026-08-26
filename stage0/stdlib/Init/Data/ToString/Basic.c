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
LEAN_EXPORT lean_object* l_instToStringId___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringId__1___aux__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_instToStringId___aux__1___redArg(lean_object* v_inst_1_){
_start:
{
lean_inc_ref(v_inst_1_);
return v_inst_1_;
}
}
LEAN_EXPORT lean_object* l_instToStringId___aux__1___redArg___boxed(lean_object* v_inst_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_instToStringId___aux__1___redArg(v_inst_2_);
lean_dec_ref(v_inst_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_instToStringId___aux__1(lean_object* v_00_u03b1_4_, lean_object* v_inst_5_){
_start:
{
lean_inc_ref(v_inst_5_);
return v_inst_5_;
}
}
LEAN_EXPORT lean_object* l_instToStringId___aux__1___boxed(lean_object* v_00_u03b1_6_, lean_object* v_inst_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_instToStringId___aux__1(v_00_u03b1_6_, v_inst_7_);
lean_dec_ref(v_inst_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_instToStringId___redArg(lean_object* v_inst_9_){
_start:
{
lean_inc_ref(v_inst_9_);
return v_inst_9_;
}
}
LEAN_EXPORT lean_object* l_instToStringId___redArg___boxed(lean_object* v_inst_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_instToStringId___redArg(v_inst_10_);
lean_dec_ref(v_inst_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_instToStringId(lean_object* v_00_u03b1_12_, lean_object* v_inst_13_){
_start:
{
lean_inc_ref(v_inst_13_);
return v_inst_13_;
}
}
LEAN_EXPORT lean_object* l_instToStringId___boxed(lean_object* v_00_u03b1_14_, lean_object* v_inst_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_instToStringId(v_00_u03b1_14_, v_inst_15_);
lean_dec_ref(v_inst_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___aux__1___redArg(lean_object* v_inst_17_){
_start:
{
lean_inc_ref(v_inst_17_);
return v_inst_17_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___aux__1___redArg___boxed(lean_object* v_inst_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_instToStringId__1___aux__1___redArg(v_inst_18_);
lean_dec_ref(v_inst_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___aux__1(lean_object* v_00_u03b1_20_, lean_object* v_inst_21_){
_start:
{
lean_inc_ref(v_inst_21_);
return v_inst_21_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___aux__1___boxed(lean_object* v_00_u03b1_22_, lean_object* v_inst_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_instToStringId__1___aux__1(v_00_u03b1_22_, v_inst_23_);
lean_dec_ref(v_inst_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___redArg(lean_object* v_inst_25_){
_start:
{
lean_inc_ref(v_inst_25_);
return v_inst_25_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___redArg___boxed(lean_object* v_inst_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_instToStringId__1___redArg(v_inst_26_);
lean_dec_ref(v_inst_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1(lean_object* v_00_u03b1_28_, lean_object* v_inst_29_){
_start:
{
lean_inc_ref(v_inst_29_);
return v_inst_29_;
}
}
LEAN_EXPORT lean_object* l_instToStringId__1___boxed(lean_object* v_00_u03b1_30_, lean_object* v_inst_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_instToStringId__1(v_00_u03b1_30_, v_inst_31_);
lean_dec_ref(v_inst_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_instToStringString___lam__0(lean_object* v_s_33_){
_start:
{
lean_inc_ref(v_s_33_);
return v_s_33_;
}
}
LEAN_EXPORT lean_object* l_instToStringString___lam__0___boxed(lean_object* v_s_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_instToStringString___lam__0(v_s_34_);
lean_dec_ref(v_s_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_instToStringChar___lam__0(uint32_t v_c_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = ((lean_object*)(l_instToStringChar___lam__0___closed__0));
v___x_43_ = lean_string_push(v___x_42_, v_c_41_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_instToStringChar___lam__0___boxed(lean_object* v_c_44_){
_start:
{
uint32_t v_c_boxed_45_; lean_object* v_res_46_; 
v_c_boxed_45_ = lean_unbox_uint32(v_c_44_);
lean_dec(v_c_44_);
v_res_46_ = l_instToStringChar___lam__0(v_c_boxed_45_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_instToStringBool___lam__0(uint8_t v_b_51_){
_start:
{
if (v_b_51_ == 0)
{
lean_object* v___x_52_; 
v___x_52_ = ((lean_object*)(l_instToStringBool___lam__0___closed__0));
return v___x_52_;
}
else
{
lean_object* v___x_53_; 
v___x_53_ = ((lean_object*)(l_instToStringBool___lam__0___closed__1));
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringBool___lam__0___boxed(lean_object* v_b_54_){
_start:
{
uint8_t v_b_boxed_55_; lean_object* v_res_56_; 
v_b_boxed_55_ = lean_unbox(v_b_54_);
v_res_56_ = l_instToStringBool___lam__0(v_b_boxed_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable___lam__0(uint8_t v_h_59_){
_start:
{
if (v_h_59_ == 0)
{
lean_object* v___x_60_; 
v___x_60_ = ((lean_object*)(l_instToStringBool___lam__0___closed__0));
return v___x_60_;
}
else
{
lean_object* v___x_61_; 
v___x_61_ = ((lean_object*)(l_instToStringBool___lam__0___closed__1));
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable___lam__0___boxed(lean_object* v_h_62_){
_start:
{
uint8_t v_h_boxed_63_; lean_object* v_res_64_; 
v_h_boxed_63_ = lean_unbox(v_h_62_);
v_res_64_ = l_instToStringDecidable___lam__0(v_h_boxed_63_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_instToStringDecidable(lean_object* v_p_66_){
_start:
{
lean_object* v___f_67_; 
v___f_67_ = ((lean_object*)(l_instToStringDecidable___closed__0));
return v___f_67_;
}
}
LEAN_EXPORT lean_object* l_instToStringPUnit___lam__0(lean_object* v_x_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = ((lean_object*)(l_instToStringPUnit___lam__0___closed__0));
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_instToStringULift___redArg___lam__0(lean_object* v_inst_73_, lean_object* v_v_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_apply_1(v_inst_73_, v_v_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_instToStringULift___redArg(lean_object* v_inst_76_){
_start:
{
lean_object* v___f_77_; 
v___f_77_ = lean_alloc_closure((void*)(l_instToStringULift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_77_, 0, v_inst_76_);
return v___f_77_;
}
}
LEAN_EXPORT lean_object* l_instToStringULift(lean_object* v_00_u03b1_78_, lean_object* v_inst_79_){
_start:
{
lean_object* v___f_80_; 
v___f_80_ = lean_alloc_closure((void*)(l_instToStringULift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_80_, 0, v_inst_79_);
return v___f_80_;
}
}
LEAN_EXPORT lean_object* l_instToStringFin(lean_object* v_n_85_){
_start:
{
lean_object* v___f_86_; 
v___f_86_ = ((lean_object*)(l_instToStringNat___closed__0));
return v___f_86_;
}
}
LEAN_EXPORT lean_object* l_instToStringFin___boxed(lean_object* v_n_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_instToStringFin(v_n_87_);
lean_dec(v_n_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0(uint8_t v_n_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_uint8_to_nat(v_n_89_);
v___x_91_ = l_Nat_reprFast(v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt8___lam__0___boxed(lean_object* v_n_92_){
_start:
{
uint8_t v_n_boxed_93_; lean_object* v_res_94_; 
v_n_boxed_93_ = lean_unbox(v_n_92_);
v_res_94_ = l_instToStringUInt8___lam__0(v_n_boxed_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0(uint16_t v_n_97_){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_uint16_to_nat(v_n_97_);
v___x_99_ = l_Nat_reprFast(v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt16___lam__0___boxed(lean_object* v_n_100_){
_start:
{
uint16_t v_n_boxed_101_; lean_object* v_res_102_; 
v_n_boxed_101_ = lean_unbox(v_n_100_);
v_res_102_ = l_instToStringUInt16___lam__0(v_n_boxed_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0(uint32_t v_n_105_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_uint32_to_nat(v_n_105_);
v___x_107_ = l_Nat_reprFast(v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt32___lam__0___boxed(lean_object* v_n_108_){
_start:
{
uint32_t v_n_boxed_109_; lean_object* v_res_110_; 
v_n_boxed_109_ = lean_unbox_uint32(v_n_108_);
lean_dec(v_n_108_);
v_res_110_ = l_instToStringUInt32___lam__0(v_n_boxed_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0(uint64_t v_n_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_uint64_to_nat(v_n_113_);
v___x_115_ = l_Nat_reprFast(v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_instToStringUInt64___lam__0___boxed(lean_object* v_n_116_){
_start:
{
uint64_t v_n_boxed_117_; lean_object* v_res_118_; 
v_n_boxed_117_ = lean_unbox_uint64(v_n_116_);
lean_dec_ref(v_n_116_);
v_res_118_ = l_instToStringUInt64___lam__0(v_n_boxed_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0(size_t v_n_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_usize_to_nat(v_n_121_);
v___x_123_ = l_Nat_reprFast(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_instToStringUSize___lam__0___boxed(lean_object* v_n_124_){
_start:
{
size_t v_n_boxed_125_; lean_object* v_res_126_; 
v_n_boxed_125_ = lean_unbox_usize(v_n_124_);
lean_dec(v_n_124_);
v_res_126_ = l_instToStringUSize___lam__0(v_n_boxed_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_instToStringFormat___lam__0(lean_object* v_f_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = l_Std_Format_defWidth;
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = l_Std_Format_pretty(v_f_129_, v___x_130_, v___x_131_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT uint8_t l_addParenHeuristic___lam__0(uint32_t v___y_135_){
_start:
{
uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_136_ = 32;
v___x_137_ = lean_uint32_dec_eq(v___y_135_, v___x_136_);
if (v___x_137_ == 0)
{
uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = 9;
v___x_139_ = lean_uint32_dec_eq(v___y_135_, v___x_138_);
if (v___x_139_ == 0)
{
uint32_t v___x_140_; uint8_t v___x_141_; 
v___x_140_ = 13;
v___x_141_ = lean_uint32_dec_eq(v___y_135_, v___x_140_);
if (v___x_141_ == 0)
{
uint32_t v___x_142_; uint8_t v___x_143_; 
v___x_142_ = 10;
v___x_143_ = lean_uint32_dec_eq(v___y_135_, v___x_142_);
return v___x_143_;
}
else
{
return v___x_141_;
}
}
else
{
return v___x_139_;
}
}
else
{
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_addParenHeuristic___lam__0___boxed(lean_object* v___y_144_){
_start:
{
uint32_t v___y_187__boxed_145_; uint8_t v_res_146_; lean_object* v_r_147_; 
v___y_187__boxed_145_ = lean_unbox_uint32(v___y_144_);
lean_dec(v___y_144_);
v_res_146_ = l_addParenHeuristic___lam__0(v___y_187__boxed_145_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT lean_object* l_addParenHeuristic(lean_object* v_s_154_){
_start:
{
lean_object* v___f_155_; lean_object* v___x_156_; uint8_t v___y_158_; uint8_t v___x_167_; 
v___f_155_ = ((lean_object*)(l_addParenHeuristic___closed__0));
v___x_156_ = ((lean_object*)(l_addParenHeuristic___closed__1));
lean_inc_ref(v_s_154_);
v___x_167_ = lean_string_isprefixof(v___x_156_, v_s_154_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = ((lean_object*)(l_addParenHeuristic___closed__5));
lean_inc_ref(v_s_154_);
v___x_169_ = lean_string_isprefixof(v___x_168_, v_s_154_);
v___y_158_ = v___x_169_;
goto v___jp_157_;
}
else
{
v___y_158_ = v___x_167_;
goto v___jp_157_;
}
v___jp_157_:
{
if (v___y_158_ == 0)
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = ((lean_object*)(l_addParenHeuristic___closed__2));
lean_inc_ref(v_s_154_);
v___x_160_ = lean_string_isprefixof(v___x_159_, v_s_154_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = ((lean_object*)(l_addParenHeuristic___closed__3));
lean_inc_ref(v_s_154_);
v___x_162_ = lean_string_isprefixof(v___x_161_, v_s_154_);
if (v___x_162_ == 0)
{
uint8_t v___x_163_; 
lean_inc_ref(v_s_154_);
v___x_163_ = lean_string_any(v_s_154_, v___f_155_);
if (v___x_163_ == 0)
{
return v_s_154_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_string_append(v___x_156_, v_s_154_);
lean_dec_ref(v_s_154_);
v___x_165_ = ((lean_object*)(l_addParenHeuristic___closed__4));
v___x_166_ = lean_string_append(v___x_164_, v___x_165_);
return v___x_166_;
}
}
else
{
return v_s_154_;
}
}
else
{
return v_s_154_;
}
}
else
{
return v_s_154_;
}
}
}
}
LEAN_EXPORT lean_object* l_instToStringOption___redArg___lam__0(lean_object* v_inst_172_, lean_object* v_x_173_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v___x_174_; 
lean_dec_ref(v_inst_172_);
v___x_174_ = ((lean_object*)(l_instToStringOption___redArg___lam__0___closed__0));
return v___x_174_;
}
else
{
lean_object* v_val_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_val_175_ = lean_ctor_get(v_x_173_, 0);
lean_inc(v_val_175_);
lean_dec_ref_known(v_x_173_, 1);
v___x_176_ = ((lean_object*)(l_instToStringOption___redArg___lam__0___closed__1));
v___x_177_ = lean_apply_1(v_inst_172_, v_val_175_);
v___x_178_ = l_addParenHeuristic(v___x_177_);
v___x_179_ = lean_string_append(v___x_176_, v___x_178_);
lean_dec_ref(v___x_178_);
v___x_180_ = ((lean_object*)(l_addParenHeuristic___closed__4));
v___x_181_ = lean_string_append(v___x_179_, v___x_180_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringOption___redArg(lean_object* v_inst_182_){
_start:
{
lean_object* v___f_183_; 
v___f_183_ = lean_alloc_closure((void*)(l_instToStringOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_183_, 0, v_inst_182_);
return v___f_183_;
}
}
LEAN_EXPORT lean_object* l_instToStringOption(lean_object* v_00_u03b1_184_, lean_object* v_inst_185_){
_start:
{
lean_object* v___f_186_; 
v___f_186_ = lean_alloc_closure((void*)(l_instToStringOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_186_, 0, v_inst_185_);
return v___f_186_;
}
}
LEAN_EXPORT lean_object* l_instToStringSum___redArg___lam__0(lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_x_191_){
_start:
{
if (lean_obj_tag(v_x_191_) == 0)
{
lean_object* v_val_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec_ref(v_inst_190_);
v_val_192_ = lean_ctor_get(v_x_191_, 0);
lean_inc(v_val_192_);
lean_dec_ref_known(v_x_191_, 1);
v___x_193_ = ((lean_object*)(l_instToStringSum___redArg___lam__0___closed__0));
v___x_194_ = lean_apply_1(v_inst_189_, v_val_192_);
v___x_195_ = l_addParenHeuristic(v___x_194_);
v___x_196_ = lean_string_append(v___x_193_, v___x_195_);
lean_dec_ref(v___x_195_);
v___x_197_ = ((lean_object*)(l_addParenHeuristic___closed__4));
v___x_198_ = lean_string_append(v___x_196_, v___x_197_);
return v___x_198_;
}
else
{
lean_object* v_val_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec_ref(v_inst_189_);
v_val_199_ = lean_ctor_get(v_x_191_, 0);
lean_inc(v_val_199_);
lean_dec_ref_known(v_x_191_, 1);
v___x_200_ = ((lean_object*)(l_instToStringSum___redArg___lam__0___closed__1));
v___x_201_ = lean_apply_1(v_inst_190_, v_val_199_);
v___x_202_ = l_addParenHeuristic(v___x_201_);
v___x_203_ = lean_string_append(v___x_200_, v___x_202_);
lean_dec_ref(v___x_202_);
v___x_204_ = ((lean_object*)(l_addParenHeuristic___closed__4));
v___x_205_ = lean_string_append(v___x_203_, v___x_204_);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringSum___redArg(lean_object* v_inst_206_, lean_object* v_inst_207_){
_start:
{
lean_object* v___f_208_; 
v___f_208_ = lean_alloc_closure((void*)(l_instToStringSum___redArg___lam__0), 3, 2);
lean_closure_set(v___f_208_, 0, v_inst_206_);
lean_closure_set(v___f_208_, 1, v_inst_207_);
return v___f_208_;
}
}
LEAN_EXPORT lean_object* l_instToStringSum(lean_object* v_00_u03b1_209_, lean_object* v_00_u03b2_210_, lean_object* v_inst_211_, lean_object* v_inst_212_){
_start:
{
lean_object* v___f_213_; 
v___f_213_ = lean_alloc_closure((void*)(l_instToStringSum___redArg___lam__0), 3, 2);
lean_closure_set(v___f_213_, 0, v_inst_211_);
lean_closure_set(v___f_213_, 1, v_inst_212_);
return v___f_213_;
}
}
LEAN_EXPORT lean_object* l_instToStringProd___redArg___lam__0(lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_x_217_){
_start:
{
lean_object* v_fst_218_; lean_object* v_snd_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_fst_218_ = lean_ctor_get(v_x_217_, 0);
lean_inc(v_fst_218_);
v_snd_219_ = lean_ctor_get(v_x_217_, 1);
lean_inc(v_snd_219_);
lean_dec_ref(v_x_217_);
v___x_220_ = ((lean_object*)(l_addParenHeuristic___closed__1));
v___x_221_ = lean_apply_1(v_inst_215_, v_fst_218_);
v___x_222_ = lean_string_append(v___x_220_, v___x_221_);
lean_dec_ref(v___x_221_);
v___x_223_ = ((lean_object*)(l_instToStringProd___redArg___lam__0___closed__0));
v___x_224_ = lean_string_append(v___x_222_, v___x_223_);
v___x_225_ = lean_apply_1(v_inst_216_, v_snd_219_);
v___x_226_ = lean_string_append(v___x_224_, v___x_225_);
lean_dec_ref(v___x_225_);
v___x_227_ = ((lean_object*)(l_addParenHeuristic___closed__4));
v___x_228_ = lean_string_append(v___x_226_, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_instToStringProd___redArg(lean_object* v_inst_229_, lean_object* v_inst_230_){
_start:
{
lean_object* v___f_231_; 
v___f_231_ = lean_alloc_closure((void*)(l_instToStringProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_231_, 0, v_inst_229_);
lean_closure_set(v___f_231_, 1, v_inst_230_);
return v___f_231_;
}
}
LEAN_EXPORT lean_object* l_instToStringProd(lean_object* v_00_u03b1_232_, lean_object* v_00_u03b2_233_, lean_object* v_inst_234_, lean_object* v_inst_235_){
_start:
{
lean_object* v___f_236_; 
v___f_236_ = lean_alloc_closure((void*)(l_instToStringProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_236_, 0, v_inst_234_);
lean_closure_set(v___f_236_, 1, v_inst_235_);
return v___f_236_;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma___redArg___lam__0(lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_x_241_){
_start:
{
lean_object* v_fst_242_; lean_object* v_snd_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_fst_242_ = lean_ctor_get(v_x_241_, 0);
lean_inc_n(v_fst_242_, 2);
v_snd_243_ = lean_ctor_get(v_x_241_, 1);
lean_inc(v_snd_243_);
lean_dec_ref(v_x_241_);
v___x_244_ = ((lean_object*)(l_instToStringSigma___redArg___lam__0___closed__0));
v___x_245_ = lean_apply_1(v_inst_239_, v_fst_242_);
v___x_246_ = lean_string_append(v___x_244_, v___x_245_);
lean_dec_ref(v___x_245_);
v___x_247_ = ((lean_object*)(l_instToStringProd___redArg___lam__0___closed__0));
v___x_248_ = lean_string_append(v___x_246_, v___x_247_);
v___x_249_ = lean_apply_2(v_inst_240_, v_fst_242_, v_snd_243_);
v___x_250_ = lean_string_append(v___x_248_, v___x_249_);
lean_dec_ref(v___x_249_);
v___x_251_ = ((lean_object*)(l_instToStringSigma___redArg___lam__0___closed__1));
v___x_252_ = lean_string_append(v___x_250_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma___redArg(lean_object* v_inst_253_, lean_object* v_inst_254_){
_start:
{
lean_object* v___f_255_; 
v___f_255_ = lean_alloc_closure((void*)(l_instToStringSigma___redArg___lam__0), 3, 2);
lean_closure_set(v___f_255_, 0, v_inst_253_);
lean_closure_set(v___f_255_, 1, v_inst_254_);
return v___f_255_;
}
}
LEAN_EXPORT lean_object* l_instToStringSigma(lean_object* v_00_u03b1_256_, lean_object* v_00_u03b2_257_, lean_object* v_inst_258_, lean_object* v_inst_259_){
_start:
{
lean_object* v___f_260_; 
v___f_260_ = lean_alloc_closure((void*)(l_instToStringSigma___redArg___lam__0), 3, 2);
lean_closure_set(v___f_260_, 0, v_inst_258_);
lean_closure_set(v___f_260_, 1, v_inst_259_);
return v___f_260_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg___lam__0(lean_object* v_inst_261_, lean_object* v_s_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lean_apply_1(v_inst_261_, v_s_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype___redArg(lean_object* v_inst_264_){
_start:
{
lean_object* v___f_265_; 
v___f_265_ = lean_alloc_closure((void*)(l_instToStringSubtype___redArg___lam__0), 2, 1);
lean_closure_set(v___f_265_, 0, v_inst_264_);
return v___f_265_;
}
}
LEAN_EXPORT lean_object* l_instToStringSubtype(lean_object* v_00_u03b1_266_, lean_object* v_p_267_, lean_object* v_inst_268_){
_start:
{
lean_object* v___f_269_; 
v___f_269_ = lean_alloc_closure((void*)(l_instToStringSubtype___redArg___lam__0), 2, 1);
lean_closure_set(v___f_269_, 0, v_inst_268_);
return v___f_269_;
}
}
LEAN_EXPORT lean_object* l_instToStringExcept___redArg___lam__0(lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_x_274_){
_start:
{
if (lean_obj_tag(v_x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec_ref(v_inst_273_);
v_a_275_ = lean_ctor_get(v_x_274_, 0);
lean_inc(v_a_275_);
lean_dec_ref_known(v_x_274_, 1);
v___x_276_ = ((lean_object*)(l_instToStringExcept___redArg___lam__0___closed__0));
v___x_277_ = lean_apply_1(v_inst_272_, v_a_275_);
v___x_278_ = lean_string_append(v___x_276_, v___x_277_);
lean_dec_ref(v___x_277_);
return v___x_278_;
}
else
{
lean_object* v_a_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec_ref(v_inst_272_);
v_a_279_ = lean_ctor_get(v_x_274_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v_x_274_, 1);
v___x_280_ = ((lean_object*)(l_instToStringExcept___redArg___lam__0___closed__1));
v___x_281_ = lean_apply_1(v_inst_273_, v_a_279_);
v___x_282_ = lean_string_append(v___x_280_, v___x_281_);
lean_dec_ref(v___x_281_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringExcept___redArg(lean_object* v_inst_283_, lean_object* v_inst_284_){
_start:
{
lean_object* v___f_285_; 
v___f_285_ = lean_alloc_closure((void*)(l_instToStringExcept___redArg___lam__0), 3, 2);
lean_closure_set(v___f_285_, 0, v_inst_283_);
lean_closure_set(v___f_285_, 1, v_inst_284_);
return v___f_285_;
}
}
LEAN_EXPORT lean_object* l_instToStringExcept(lean_object* v_00_u03b5_286_, lean_object* v_00_u03b1_287_, lean_object* v_inst_288_, lean_object* v_inst_289_){
_start:
{
lean_object* v___f_290_; 
v___f_290_ = lean_alloc_closure((void*)(l_instToStringExcept___redArg___lam__0), 3, 2);
lean_closure_set(v___f_290_, 0, v_inst_288_);
lean_closure_set(v___f_290_, 1, v_inst_289_);
return v___f_290_;
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0(lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
if (lean_obj_tag(v_x_299_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec_ref(v_inst_298_);
v_a_301_ = lean_ctor_get(v_x_299_, 0);
lean_inc(v_a_301_);
lean_dec_ref_known(v_x_299_, 1);
v___x_302_ = ((lean_object*)(l_instReprExcept___redArg___lam__0___closed__1));
v___x_303_ = lean_unsigned_to_nat(1024u);
v___x_304_ = lean_apply_2(v_inst_297_, v_a_301_, v___x_303_);
v___x_305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_302_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = l_Repr_addAppParen(v___x_305_, v_x_300_);
return v___x_306_;
}
else
{
lean_object* v_a_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec_ref(v_inst_297_);
v_a_307_ = lean_ctor_get(v_x_299_, 0);
lean_inc(v_a_307_);
lean_dec_ref_known(v_x_299_, 1);
v___x_308_ = ((lean_object*)(l_instReprExcept___redArg___lam__0___closed__3));
v___x_309_ = lean_unsigned_to_nat(1024u);
v___x_310_ = lean_apply_2(v_inst_298_, v_a_307_, v___x_309_);
v___x_311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_308_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = l_Repr_addAppParen(v___x_311_, v_x_300_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg___lam__0___boxed(lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_instReprExcept___redArg___lam__0(v_inst_313_, v_inst_314_, v_x_315_, v_x_316_);
lean_dec(v_x_316_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_instReprExcept___redArg(lean_object* v_inst_318_, lean_object* v_inst_319_){
_start:
{
lean_object* v___f_320_; 
v___f_320_ = lean_alloc_closure((void*)(l_instReprExcept___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_320_, 0, v_inst_318_);
lean_closure_set(v___f_320_, 1, v_inst_319_);
return v___f_320_;
}
}
LEAN_EXPORT lean_object* l_instReprExcept(lean_object* v_00_u03b5_321_, lean_object* v_00_u03b1_322_, lean_object* v_inst_323_, lean_object* v_inst_324_){
_start:
{
lean_object* v___f_325_; 
v___f_325_ = lean_alloc_closure((void*)(l_instReprExcept___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_325_, 0, v_inst_323_);
lean_closure_set(v___f_325_, 1, v_inst_324_);
return v___f_325_;
}
}
lean_object* runtime_initialize_Init_Data_Repr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
