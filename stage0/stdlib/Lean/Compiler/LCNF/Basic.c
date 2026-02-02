// Lean compiler output
// Module: Lean.Compiler.LCNF.Basic
// Imports: public import Lean.Meta.Instances public import Lean.Compiler.ExternAttr public import Lean.Compiler.Specialize public import Lean.Compiler.LCNF.Types
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_pure_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_pure_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_pure_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_pure_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_impure_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_impure_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_impure_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_impure_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instInhabitedPurity_default;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instInhabitedPurity;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Purity_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_ofNat___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableEqPurity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableEqPurity___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashablePurity_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashablePurity_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instHashablePurity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instHashablePurity_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instHashablePurity___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instHashablePurity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instHashablePurity = (const lean_object*)&l_Lean_Compiler_LCNF_instHashablePurity___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pure"};
static const lean_object* l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "impure"};
static const lean_object* l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToStringPurity___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToStringPurity___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instToStringPurity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instToStringPurity___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instToStringPurity___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instToStringPurity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instToStringPurity = (const lean_object*)&l_Lean_Compiler_LCNF_instToStringPurity___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Compiler.LCNF.Purity.withAssertPurity"};
static const lean_object* l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ", this is a bug"};
static const lean_object* l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Purity should be "};
static const lean_object* l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " but is "};
static const lean_object* l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__4_value;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_withAssertPurity(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_withAssertPurity___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_tacticPurity__tac___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Compiler_LCNF_tacticPurity__tac___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_tacticPurity__tac___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_tacticPurity__tac___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_tacticPurity__tac___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l_Lean_Compiler_LCNF_tacticPurity__tac___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_tacticPurity__tac___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "tacticPurity_tac"};
static const lean_object* l_Lean_Compiler_LCNF_tacticPurity__tac___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_tacticPurity__tac___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_tacticPurity__tac___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__4_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__1_value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_tacticPurity__tac___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__4_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__2_value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_tacticPurity__tac___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__4_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__3_value),LEAN_SCALAR_PTR_LITERAL(30, 138, 226, 4, 153, 188, 214, 169)}};
static const lean_object* l_Lean_Compiler_LCNF_tacticPurity__tac___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_tacticPurity__tac___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "purity_tac"};
static const lean_object* l_Lean_Compiler_LCNF_tacticPurity__tac___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__5_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_tacticPurity__tac___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_tacticPurity__tac___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_tacticPurity__tac___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__6_value)}};
static const lean_object* l_Lean_Compiler_LCNF_tacticPurity__tac___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_tacticPurity__tac = (const lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__7_value;
static const lean_string_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__4_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__7_value;
static const lean_string_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__8_value;
static const lean_string_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__9_value;
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__10_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__10_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__10_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__10_value;
static const lean_string_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__11_value;
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__12_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__12_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__12_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__12_value;
static const lean_string_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withReducible"};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__13_value;
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__14_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__14_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__14_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(197, 44, 223, 192, 8, 197, 146, 83)}};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__14_value;
static const lean_string_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "with_reducible"};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__15_value;
static const lean_string_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__16_value;
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__17_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__17_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__17_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__17 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__17_value;
static const lean_string_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__18 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__18_value;
static const lean_string_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "assumption"};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__19 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__19_value;
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_tacticPurity__tac___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__20_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__20_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__20_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(240, 50, 167, 190, 65, 82, 149, 231)}};
static const lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__20 = (const lean_object*)&l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__20_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__1_value;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__2;
extern lean_object* l_Lean_instInhabitedFVarId_default;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedParam(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedParam___boxed(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqParam_beq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqParam_beq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqParam_beq(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqParam_beq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqParam(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqParam___boxed(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toExpr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toExpr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_nat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_nat_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_str_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_str_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_uint8_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_uint8_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_uint16_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_uint16_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_uint32_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_uint32_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_uint64_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_uint64_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_usize_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_usize_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedLitValue_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedLitValue_default___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedLitValue_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instInhabitedLitValue_default = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedLitValue_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instInhabitedLitValue = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedLitValue_default___closed__0_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqLitValue_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqLitValue_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instBEqLitValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instBEqLitValue_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instBEqLitValue___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instBEqLitValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instBEqLitValue = (const lean_object*)&l_Lean_Compiler_LCNF_instBEqLitValue___closed__0_value;
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint8_to_uint64(uint8_t);
uint64_t lean_uint16_to_uint64(uint16_t);
uint64_t lean_uint32_to_uint64(uint32_t);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableLitValue_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableLitValue_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instHashableLitValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instHashableLitValue_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instHashableLitValue___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instHashableLitValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instHashableLitValue = (const lean_object*)&l_Lean_Compiler_LCNF_instHashableLitValue___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_LitValue_toExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_LitValue_toExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_LitValue_toExpr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LitValue_toExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__2_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(113, 212, 171, 80, 86, 90, 103, 206)}};
static const lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__2_value;
static lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr___closed__3;
static const lean_string_object l_Lean_Compiler_LCNF_LitValue_toExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LitValue_toExpr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LitValue_toExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__5_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(23, 109, 23, 47, 202, 202, 227, 131)}};
static const lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__5_value;
static lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr___closed__6;
static const lean_string_object l_Lean_Compiler_LCNF_LitValue_toExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__7_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LitValue_toExpr___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__7_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LitValue_toExpr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__8_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(139, 73, 218, 73, 188, 181, 30, 93)}};
static const lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__8_value;
static lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr___closed__9;
static const lean_string_object l_Lean_Compiler_LCNF_LitValue_toExpr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__10_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LitValue_toExpr___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__10_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LitValue_toExpr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__11_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 45, 252, 130, 147, 16, 202, 24)}};
static const lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__11_value;
static lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr___closed__12;
static const lean_string_object l_Lean_Compiler_LCNF_LitValue_toExpr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__13_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_LitValue_toExpr___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_LitValue_toExpr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__14_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(208, 54, 241, 83, 163, 219, 17, 78)}};
static const lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_LitValue_toExpr___closed__14_value;
static lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr___closed__15;
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Arg___auto__1___closed__0;
lean_object* l_Lean_mkAtom(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Arg___auto__1___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Arg___auto__1___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Arg___auto__1___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Arg___auto__1___closed__4;
static lean_object* l_Lean_Compiler_LCNF_Arg___auto__1___closed__5;
static lean_object* l_Lean_Compiler_LCNF_Arg___auto__1___closed__6;
static lean_object* l_Lean_Compiler_LCNF_Arg___auto__1___closed__7;
static lean_object* l_Lean_Compiler_LCNF_Arg___auto__1___closed__8;
static lean_object* l_Lean_Compiler_LCNF_Arg___auto__1___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg___auto__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_ctorIdx(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_ctorElim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_erased_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_erased_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_erased_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_fvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_fvar_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_fvar_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_type_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_type_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_type_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedArg_default(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedArg_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedArg(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqArg_beq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqArg_beq(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqArg_beq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqArg(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqArg___boxed(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableArg_hash___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableArg_hash(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableArg_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableArg(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toArg___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toArg___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toArg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_toExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_toExpr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_toExpr___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.Arg.updateTypeImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1_value;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__2;
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.Arg.updateFVarImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg___closed__0_value;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue___auto__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue___auto__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_ctorIdx(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_ctorElim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_lit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_lit_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_lit_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_erased_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_erased_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_erased_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_proj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_proj_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_proj_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_const_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_const_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_const_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_fvar_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_fvar_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_fvar_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedLetValue_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedLitValue_default___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedLetValue_default___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedLetValue_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLetValue_default(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLetValue_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLetValue(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLetValue___boxed(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqLetValue_beq(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqLetValue_beq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqLetValue(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqLetValue___boxed(lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__1___redArg(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableLetValue_hash(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableLetValue_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__1(uint8_t, lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableLetValue(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableLetValue___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Arg_toLetValue___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_toLetValue___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_toLetValue(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_toLetValue___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.LetValue.updateProjImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp___closed__0_value;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateConstImp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.LetValue.updateConstImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateConstImp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateConstImp___closed__0_value;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateConstImp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateConstImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateConstImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.LetValue.updateFVarImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___closed__0_value;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.LetValue.updateArgsImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___closed__0_value;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LetValue_toExpr_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LetValue_toExpr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LetValue_toExpr_spec__0(uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LetValue_toExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLetDecl_default(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLetDecl_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLetDecl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLetDecl___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqLetDecl_beq(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqLetDecl_beq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqLetDecl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqLetDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt___auto__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt___auto__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_ctorIdx(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_ctorElim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_alt_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_alt_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_alt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_default_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_default_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_default_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_ctorIdx(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_ctorElim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_let_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_let_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_let_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_fun_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_fun_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_fun_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_jp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_jp_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_jp_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_jmp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_jmp_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_jmp_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cases_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cases_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cases_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_return_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_return_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_return_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_unreach_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_unreach_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_unreach_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instInhabitedCases_default__1___closed__0;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedCases_default__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCases_default__1(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCases_default__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCases(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCases___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1___closed__0;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCode(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_fvarId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_fvarId___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_fvarId(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_fvarId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_binderName___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_binderName___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_binderName(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_binderName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_params___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_params___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_params(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_params___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_type___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_type___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_type(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_type___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_value___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_value___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_value(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_value___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateBinderName___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateBinderName(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateBinderName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toParam___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toParam___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toParam(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toParam___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_typeName___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_typeName___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_typeName(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_typeName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_resultType___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_resultType___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_resultType(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_resultType___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_discr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_discr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_discr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_discr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_alts___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_alts___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_alts(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_alts___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_updateAlts___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_updateAlts(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_updateAlts___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDecl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_getArity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_getArity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_getArity(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_getArity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Cases_getCtorNames_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Cases_getCtorNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_getCtorNames___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_getCtorNames___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_getCtorNames(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_getCtorNames___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl___auto__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_ctorIdx(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_ctorElim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_let_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_let_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_let_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_fun_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_fun_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_fun_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_jp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_jp_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_jp_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_attachCodeDecls_go(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_attachCodeDecls_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_CodeDecl_fvarId_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_CodeDecl_fvarId_match__1_splitter(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_CodeDecl_fvarId_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_attachCodeDecls___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqFunDecl(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqFunDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqImp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqCode(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqCode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqFunDecl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqFunDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_getCode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_getCode___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_getCode(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_getCode___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Alt_getParams___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_getParams___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_getParams___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_getParams(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_getParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateAltImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___closed__0_value;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateAltsImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp___closed__0_value;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateCasesImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp___closed__0_value;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateLetImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp___closed__0_value;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateContImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__0_value;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp___closed__0_value;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateReturnImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp___closed__0_value;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateJmpImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp___closed__0_value;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateUnreachImp"};
static const lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp___closed__0_value;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateParamCoreImp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateParamCoreImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateParamCoreImp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetDeclCoreImp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetDeclCoreImp(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetDeclCoreImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunDeclCoreImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunDeclCoreImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunDeclCoreImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Cases_extractAlt_x21_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Cases_extractAlt_x21_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Cases_extractAlt_x21___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Cases_extractAlt_x21___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Cases_extractAlt_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Cases_extractAlt_x21___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Cases_extractAlt_x21___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Cases_extractAlt_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Compiler.LCNF.Cases.extractAlt!"};
static const lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Cases_extractAlt_x21___closed__1_value;
static lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21___closed__2;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx_x21___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_isDecl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isDecl___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_isDecl(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isDecl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_isFun___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isFun___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_isFun(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isFun___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isReturnOf___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isReturnOf___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_size_go(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_size_go_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_size_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_size_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_size(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_size___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_inc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_inc___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_sizeLe(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_sizeLe___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_instantiateParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsNoCache(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instExpr(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instLetValue___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instLetValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___at___00List_mapMono_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instLetValue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instLetDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instAlt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instFunDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_ctorIdx(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_ctorElim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_code_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_code_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_code_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_extern_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_extern_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_extern_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclValue_default(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclValue_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclValue(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclValue___boxed(lean_object*);
uint8_t l_Lean_instBEqExternAttrData_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqDeclValue_beq(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqDeclValue_beq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqDeclValue(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqDeclValue___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_size(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_size___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCode___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCode(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl_default(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl___boxed(lean_object*);
uint8_t l_Lean_Compiler_instBEqInlineAttributeKind_beq(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_instBEqDecl_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_instBEqDecl_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Compiler_LCNF_instBEqDecl_beq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Compiler_LCNF_instBEqDecl_beq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqDecl_beq(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqDecl_beq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqDecl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_size(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_size___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_getArity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_getArity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_getArity(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_getArity___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_inlineAttr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_inlineAttr___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_inlineAttr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_inlineAttr___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_noinlineAttr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_noinlineAttr___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_noinlineAttr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_noinlineAttr___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_inlineable___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_inlineable___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_inlineable(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_inlineable___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Decl_castPurity_x21_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Decl_castPurity_x21_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Decl_castPurity_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Compiler.LCNF.Decl.castPurity!"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_castPurity_x21___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_castPurity_x21___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_castPurity_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Purity "};
static const lean_object* l_Lean_Compiler_LCNF_Decl_castPurity_x21___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_castPurity_x21___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_castPurity_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " does not match "};
static const lean_object* l_Lean_Compiler_LCNF_Decl_castPurity_x21___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_castPurity_x21___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_castPurity_x21(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_castPurity_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go___redArg(lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go(uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasLocalInst___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
uint8_t l_Lean_BinderInfo_isImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasLocalInst___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasLocalInst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasLocalInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isInstanceReducibleCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Decl_isTemplateLike_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Decl_isTemplateLike_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Decl_isTemplateLike_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Decl_isTemplateLike_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_hasSpecializeAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___lam__0___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFVarIdHashSet;
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.collectType"};
static const lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___closed__0_value;
static lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectLetValue(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectLetValue___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_collectUsed_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_collectUsed(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_collectUsed(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_collectUsed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_collectUsed_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_collectUsed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectUsedAtExpr(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit_spec__1(uint8_t, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go_spec__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go_spec__1(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_markRecDecls_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_markRecDecls_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markRecDecls(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markRecDecls___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_markRecDecls_spec__0(lean_object*, uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_markRecDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_expr_instantiate_range(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateRangeArgs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateRangeArgs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateRangeArgs(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateRangeArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateRevRangeArgs(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateRevRangeArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_ctorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_Purity_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Purity_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_Purity_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Purity_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_Compiler_LCNF_Purity_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_pure_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_pure_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Purity_pure_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_pure_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_pure_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Compiler_LCNF_Purity_pure_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_impure_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_impure_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Purity_impure_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_impure_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_impure_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Compiler_LCNF_Purity_impure_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_instInhabitedPurity_default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_instInhabitedPurity() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Purity_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_Purity_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableEqPurity(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Compiler_LCNF_Purity_ctorIdx(x_1);
x_4 = l_Lean_Compiler_LCNF_Purity_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableEqPurity___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Compiler_LCNF_instDecidableEqPurity(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashablePurity_hash(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint64_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint64_t x_3; 
x_3 = 1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashablePurity_hash___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instHashablePurity_hash(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToStringPurity___lam__0(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__1));
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToStringPurity___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instToStringPurity___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Compiler_LCNF_instDecidableEqPurity(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_6 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_7 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__1));
x_8 = lean_unsigned_to_nat(59u);
x_9 = lean_unsigned_to_nat(4u);
x_18 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__3));
if (x_3 == 0)
{
lean_object* x_26; 
x_26 = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__0));
x_19 = x_26;
goto block_25;
}
else
{
lean_object* x_27; 
x_27 = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__1));
x_19 = x_27;
goto block_25;
}
block_17:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__2));
x_14 = lean_string_append(x_12, x_13);
x_15 = l_mkPanicMessageWithDecl(x_6, x_7, x_8, x_9, x_14);
lean_dec_ref(x_14);
x_16 = l_panic___redArg(x_1, x_15);
return x_16;
}
block_25:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_string_append(x_18, x_19);
lean_dec_ref(x_19);
x_21 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__4));
x_22 = lean_string_append(x_20, x_21);
if (x_2 == 0)
{
lean_object* x_23; 
x_23 = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__0));
x_10 = x_22;
x_11 = x_23;
goto block_17;
}
else
{
lean_object* x_24; 
x_24 = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__1));
x_10 = x_22;
x_11 = x_24;
goto block_17;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_1);
x_28 = lean_apply_1(x_4, lean_box(0));
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_withAssertPurity(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lean_Compiler_LCNF_instDecidableEqPurity(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
x_7 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_8 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__1));
x_9 = lean_unsigned_to_nat(59u);
x_10 = lean_unsigned_to_nat(4u);
x_19 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__3));
if (x_4 == 0)
{
lean_object* x_27; 
x_27 = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__0));
x_20 = x_27;
goto block_26;
}
else
{
lean_object* x_28; 
x_28 = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__1));
x_20 = x_28;
goto block_26;
}
block_18:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
x_14 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__2));
x_15 = lean_string_append(x_13, x_14);
x_16 = l_mkPanicMessageWithDecl(x_7, x_8, x_9, x_10, x_15);
lean_dec_ref(x_15);
x_17 = l_panic___redArg(x_2, x_16);
return x_17;
}
block_26:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__4));
x_23 = lean_string_append(x_21, x_22);
if (x_3 == 0)
{
lean_object* x_24; 
x_24 = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__0));
x_11 = x_23;
x_12 = x_24;
goto block_18;
}
else
{
lean_object* x_25; 
x_25 = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__1));
x_11 = x_23;
x_12 = x_25;
goto block_18;
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_2);
x_29 = lean_apply_1(x_5, lean_box(0));
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Purity_withAssertPurity___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_3);
x_7 = lean_unbox(x_4);
x_8 = l_Lean_Compiler_LCNF_Purity_withAssertPurity(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_tacticPurity__tac___closed__4));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_8 = lean_ctor_get(x_2, 5);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
x_11 = ((lean_object*)(l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__2));
x_12 = ((lean_object*)(l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__3));
lean_inc(x_10);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = ((lean_object*)(l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__5));
x_15 = ((lean_object*)(l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__7));
x_16 = ((lean_object*)(l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__8));
lean_inc(x_10);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
x_18 = ((lean_object*)(l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__10));
x_19 = ((lean_object*)(l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__12));
x_20 = ((lean_object*)(l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__14));
x_21 = ((lean_object*)(l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__15));
lean_inc(x_10);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
x_23 = ((lean_object*)(l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__17));
x_24 = ((lean_object*)(l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__18));
lean_inc(x_10);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_10);
x_26 = l_Lean_Syntax_node1(x_10, x_23, x_25);
lean_inc(x_10);
x_27 = l_Lean_Syntax_node1(x_10, x_14, x_26);
lean_inc(x_10);
x_28 = l_Lean_Syntax_node1(x_10, x_19, x_27);
lean_inc(x_10);
x_29 = l_Lean_Syntax_node1(x_10, x_18, x_28);
lean_inc(x_10);
x_30 = l_Lean_Syntax_node2(x_10, x_20, x_22, x_29);
lean_inc(x_10);
x_31 = l_Lean_Syntax_node1(x_10, x_14, x_30);
lean_inc(x_10);
x_32 = l_Lean_Syntax_node1(x_10, x_19, x_31);
lean_inc(x_10);
x_33 = l_Lean_Syntax_node1(x_10, x_18, x_32);
lean_inc_ref(x_17);
lean_inc(x_10);
x_34 = l_Lean_Syntax_node2(x_10, x_15, x_17, x_33);
x_35 = ((lean_object*)(l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__19));
x_36 = ((lean_object*)(l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__20));
lean_inc(x_10);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_10);
lean_ctor_set(x_37, 1, x_35);
lean_inc(x_10);
x_38 = l_Lean_Syntax_node1(x_10, x_36, x_37);
lean_inc(x_10);
x_39 = l_Lean_Syntax_node1(x_10, x_14, x_38);
lean_inc(x_10);
x_40 = l_Lean_Syntax_node1(x_10, x_19, x_39);
lean_inc(x_10);
x_41 = l_Lean_Syntax_node1(x_10, x_18, x_40);
lean_inc(x_10);
x_42 = l_Lean_Syntax_node2(x_10, x_15, x_17, x_41);
lean_inc(x_10);
x_43 = l_Lean_Syntax_node2(x_10, x_14, x_34, x_42);
x_44 = l_Lean_Syntax_node2(x_10, x_12, x_13, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_3);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__2;
x_3 = lean_box(0);
x_4 = l_Lean_instInhabitedFVarId_default;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__3;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedParam_default(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedParam(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedParam_default(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedParam(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqParam_beq___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_11 = l_Lean_instBEqFVarId_beq(x_3, x_7);
if (x_11 == 0)
{
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_name_eq(x_4, x_8);
if (x_12 == 0)
{
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_expr_eqv(x_5, x_9);
if (x_13 == 0)
{
return x_13;
}
else
{
if (x_6 == 0)
{
if (x_10 == 0)
{
return x_13;
}
else
{
return x_6;
}
}
else
{
return x_10;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqParam_beq___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_instBEqParam_beq___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqParam_beq(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Compiler_LCNF_instBEqParam_beq___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqParam_beq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_instBEqParam_beq(x_4, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqParam(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instBEqParam_beq___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instBEqParam(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toExpr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_Expr_fvar___override(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toExpr(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Param_toExpr___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toExpr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Param_toExpr(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_LitValue_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 2:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get_uint8(x_1, 0);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
case 3:
{
uint16_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get_uint16(x_1, 0);
lean_dec_ref(x_1);
x_11 = lean_box(x_10);
x_12 = lean_apply_1(x_2, x_11);
return x_12;
}
case 4:
{
uint32_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get_uint32(x_1, 0);
lean_dec_ref(x_1);
x_14 = lean_box_uint32(x_13);
x_15 = lean_apply_1(x_2, x_14);
return x_15;
}
default: 
{
uint64_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get_uint64(x_1, 0);
lean_dec_ref(x_1);
x_17 = lean_box_uint64(x_16);
x_18 = lean_apply_1(x_2, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_LitValue_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_LitValue_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_nat_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_LitValue_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_nat_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_LitValue_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_str_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_LitValue_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_str_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_LitValue_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_uint8_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_LitValue_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_uint8_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_LitValue_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_uint16_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_LitValue_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_uint16_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_LitValue_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_uint32_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_LitValue_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_uint32_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_LitValue_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_uint64_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_LitValue_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_uint64_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_LitValue_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_usize_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_LitValue_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_usize_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_LitValue_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqLitValue_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_string_dec_eq(x_7, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_ctor_get_uint8(x_1, 0);
x_12 = lean_ctor_get_uint8(x_2, 0);
x_13 = lean_uint8_dec_eq(x_11, x_12);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
uint16_t x_15; uint16_t x_16; uint8_t x_17; 
x_15 = lean_ctor_get_uint16(x_1, 0);
x_16 = lean_ctor_get_uint16(x_2, 0);
x_17 = lean_uint16_dec_eq(x_15, x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
uint32_t x_19; uint32_t x_20; uint8_t x_21; 
x_19 = lean_ctor_get_uint32(x_1, 0);
x_20 = lean_ctor_get_uint32(x_2, 0);
x_21 = lean_uint32_dec_eq(x_19, x_20);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = 0;
return x_22;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
uint64_t x_23; uint64_t x_24; uint8_t x_25; 
x_23 = lean_ctor_get_uint64(x_1, 0);
x_24 = lean_ctor_get_uint64(x_2, 0);
x_25 = lean_uint64_dec_eq(x_23, x_24);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
default: 
{
if (lean_obj_tag(x_2) == 6)
{
uint64_t x_27; uint64_t x_28; uint8_t x_29; 
x_27 = lean_ctor_get_uint64(x_1, 0);
x_28 = lean_ctor_get_uint64(x_2, 0);
x_29 = lean_uint64_dec_eq(x_27, x_28);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = 0;
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqLitValue_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_instBEqLitValue_beq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableLitValue_hash(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 0;
x_4 = lean_uint64_of_nat(x_2);
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 1;
x_8 = lean_string_hash(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
return x_9;
}
case 2:
{
uint8_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; 
x_10 = lean_ctor_get_uint8(x_1, 0);
x_11 = 2;
x_12 = lean_uint8_to_uint64(x_10);
x_13 = lean_uint64_mix_hash(x_11, x_12);
return x_13;
}
case 3:
{
uint16_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; 
x_14 = lean_ctor_get_uint16(x_1, 0);
x_15 = 3;
x_16 = lean_uint16_to_uint64(x_14);
x_17 = lean_uint64_mix_hash(x_15, x_16);
return x_17;
}
case 4:
{
uint32_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; 
x_18 = lean_ctor_get_uint32(x_1, 0);
x_19 = 4;
x_20 = lean_uint32_to_uint64(x_18);
x_21 = lean_uint64_mix_hash(x_19, x_20);
return x_21;
}
case 5:
{
uint64_t x_22; uint64_t x_23; uint64_t x_24; 
x_22 = lean_ctor_get_uint64(x_1, 0);
x_23 = 5;
x_24 = lean_uint64_mix_hash(x_23, x_22);
return x_24;
}
default: 
{
uint64_t x_25; uint64_t x_26; uint64_t x_27; 
x_25 = lean_ctor_get_uint64(x_1, 0);
x_26 = 6;
x_27 = lean_uint64_mix_hash(x_26, x_25);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableLitValue_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instHashableLitValue_hash(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LitValue_toExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_LitValue_toExpr___closed__2));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LitValue_toExpr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_LitValue_toExpr___closed__5));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LitValue_toExpr___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_LitValue_toExpr___closed__8));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LitValue_toExpr___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_LitValue_toExpr___closed__11));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LitValue_toExpr___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_LitValue_toExpr___closed__14));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LitValue_toExpr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_Lean_Expr_lit___override(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_Expr_lit___override(x_5);
return x_6;
}
}
case 1:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Expr_lit___override(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_Expr_lit___override(x_10);
return x_11;
}
}
case 2:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get_uint8(x_1, 0);
lean_dec_ref(x_1);
x_13 = l_Lean_Compiler_LCNF_LitValue_toExpr___closed__3;
x_14 = lean_uint8_to_nat(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Expr_lit___override(x_15);
x_17 = l_Lean_Expr_app___override(x_13, x_16);
return x_17;
}
case 3:
{
uint16_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get_uint16(x_1, 0);
lean_dec_ref(x_1);
x_19 = l_Lean_Compiler_LCNF_LitValue_toExpr___closed__6;
x_20 = lean_uint16_to_nat(x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Expr_lit___override(x_21);
x_23 = l_Lean_Expr_app___override(x_19, x_22);
return x_23;
}
case 4:
{
uint32_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get_uint32(x_1, 0);
lean_dec_ref(x_1);
x_25 = l_Lean_Compiler_LCNF_LitValue_toExpr___closed__9;
x_26 = lean_uint32_to_nat(x_24);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_Expr_lit___override(x_27);
x_29 = l_Lean_Expr_app___override(x_25, x_28);
return x_29;
}
case 5:
{
uint64_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get_uint64(x_1, 0);
lean_dec_ref(x_1);
x_31 = l_Lean_Compiler_LCNF_LitValue_toExpr___closed__12;
x_32 = lean_uint64_to_nat(x_30);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_Expr_lit___override(x_33);
x_35 = l_Lean_Expr_app___override(x_31, x_34);
return x_35;
}
default: 
{
uint64_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get_uint64(x_1, 0);
lean_dec_ref(x_1);
x_37 = l_Lean_Compiler_LCNF_LitValue_toExpr___closed__15;
x_38 = lean_uint64_to_nat(x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_Expr_lit___override(x_39);
x_41 = l_Lean_Expr_app___override(x_37, x_40);
return x_41;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_tacticPurity__tac___closed__5));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__1;
x_2 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__0;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__2;
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_tacticPurity__tac___closed__4));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__3;
x_2 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__0;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__4;
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__5));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__5;
x_2 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__0;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__6;
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__12));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__7;
x_2 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__0;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__8;
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF___aux__Lean__Compiler__LCNF__Basic______macroRules__Lean__Compiler__LCNF__tacticPurity__tac__1___closed__10));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg___auto__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__9;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_ctorIdx___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Arg_ctorIdx___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_ctorIdx(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Arg_ctorIdx___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Arg_ctorIdx(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
default: 
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_2(x_2, x_5, lean_box(0));
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_ctorElim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Arg_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Compiler_LCNF_Arg_ctorElim(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_erased_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Arg_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_erased_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Arg_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_erased_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_Arg_erased_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_fvar_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Arg_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_fvar_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Arg_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_fvar_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_Arg_fvar_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_type_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Arg_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_type_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Arg_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_type_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_Arg_type_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedArg_default(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedArg_default___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedArg_default(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedArg(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedArg(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_2, 0);
x_7 = l_Lean_instBEqFVarId_beq(x_5, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
default: 
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_expr_eqv(x_9, x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqArg_beq___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqArg_beq(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqArg_beq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_instBEqArg_beq(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqArg(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instBEqArg_beq___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instBEqArg(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = 1;
x_5 = l_Lean_instHashableFVarId_hash(x_3);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
default: 
{
lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 2;
x_9 = l_Lean_Expr_hash(x_7);
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = 0;
x_12 = lean_uint64_mix_hash(x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableArg_hash___redArg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableArg_hash(uint8_t x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; 
x_3 = l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableArg_hash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_instHashableArg_hash(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableArg(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableArg_hash___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instHashableArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toArg___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toArg___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Param_toArg___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toArg(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Param_toArg___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Param_toArg(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_toExpr___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_erasedExpr;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_Expr_fvar___override(x_3);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_toExpr(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Arg_toExpr___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_toExpr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Arg_toExpr(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp_spec__0(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(112u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__0));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_4; size_t x_5; size_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ptr_addr(x_4);
x_6 = lean_ptr_addr(x_3);
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
}
else
{
lean_dec_ref(x_3);
return x_2;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_11 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__2;
x_12 = l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp_spec__0___redArg(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(119u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg___closed__0));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_instBEqFVarId_beq(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_dec(x_6);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg___closed__1;
x_9 = l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp_spec__0___redArg(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LetValue___auto__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LetValue___auto__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__9;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_ctorIdx___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_LetValue_ctorIdx___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_ctorIdx(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_LetValue_ctorIdx___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_LetValue_ctorIdx(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
case 1:
{
return x_2;
}
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_4(x_2, x_5, x_6, x_7, lean_box(0));
return x_8;
}
case 3:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_12 = lean_apply_4(x_2, x_9, x_10, x_11, lean_box(0));
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
x_15 = lean_apply_2(x_2, x_13, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_ctorElim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_LetValue_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Compiler_LCNF_LetValue_ctorElim(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_lit_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_LetValue_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_lit_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_LetValue_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_lit_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_LetValue_lit_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_erased_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_LetValue_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_erased_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_LetValue_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_erased_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_LetValue_erased_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_proj_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_LetValue_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_proj_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_LetValue_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_proj_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_LetValue_proj_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_const_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_LetValue_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_const_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_LetValue_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_const_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_LetValue_const_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_fvar_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_LetValue_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_fvar_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_LetValue_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_fvar_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_LetValue_fvar_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLetValue_default(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedLetValue_default___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLetValue_default___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedLetValue_default(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLetValue(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedLetValue_default(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLetValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedLetValue(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_level_eq(x_6, x_8);
if (x_10 == 0)
{
return x_10;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget_borrowed(x_1, x_7);
x_9 = lean_array_fget_borrowed(x_2, x_7);
x_10 = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_7);
return x_10;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__1___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqLetValue_beq(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_Compiler_LCNF_instBEqLitValue_beq(x_4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
case 1:
{
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
case 2:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_name_eq(x_10, x_13);
if (x_16 == 0)
{
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_eq(x_11, x_14);
if (x_17 == 0)
{
return x_17;
}
else
{
uint8_t x_18; 
x_18 = l_Lean_instBEqFVarId_beq(x_12, x_15);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
}
case 3:
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
x_25 = lean_ctor_get(x_3, 2);
x_26 = lean_name_eq(x_20, x_23);
if (x_26 == 0)
{
return x_26;
}
else
{
uint8_t x_27; 
x_27 = l_List_beq___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__0(x_21, x_24);
if (x_27 == 0)
{
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_array_get_size(x_22);
x_29 = lean_array_get_size(x_25);
x_30 = lean_nat_dec_eq(x_28, x_29);
if (x_30 == 0)
{
return x_30;
}
else
{
uint8_t x_31; 
x_31 = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__1___redArg(x_22, x_25, x_28);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = 0;
return x_32;
}
}
default: 
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_ctor_get(x_3, 1);
x_37 = l_Lean_instBEqFVarId_beq(x_33, x_35);
if (x_37 == 0)
{
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_array_get_size(x_34);
x_39 = lean_array_get_size(x_36);
x_40 = lean_nat_dec_eq(x_38, x_39);
if (x_40 == 0)
{
return x_40;
}
else
{
uint8_t x_41; 
x_41 = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__1___redArg(x_34, x_36, x_38);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = 0;
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqLetValue_beq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__1___redArg(x_2, x_3, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
x_8 = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqLetValue(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instBEqLetValue_beq___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqLetValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instBEqLetValue(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__0(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_Level_hash(x_3);
x_6 = lean_uint64_mix_hash(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Compiler_LCNF_instHashableArg_hash___redArg(x_6);
lean_dec(x_6);
x_8 = lean_uint64_mix_hash(x_4, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__1___redArg(x_1, x_5, x_6, x_7);
lean_dec_ref(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT uint64_t l_Lean_Compiler_LCNF_instHashableLetValue_hash(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = 0;
x_5 = l_Lean_Compiler_LCNF_instHashableLitValue_hash(x_3);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
case 1:
{
uint64_t x_7; 
x_7 = 1;
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = 2;
x_12 = l_Lean_Name_hash___override(x_8);
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_14 = lean_uint64_of_nat(x_9);
x_15 = lean_uint64_mix_hash(x_13, x_14);
x_16 = l_Lean_instHashableFVarId_hash(x_10);
x_17 = lean_uint64_mix_hash(x_15, x_16);
x_18 = 0;
x_19 = lean_uint64_mix_hash(x_17, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = 3;
x_24 = l_Lean_Name_hash___override(x_20);
x_25 = lean_uint64_mix_hash(x_23, x_24);
x_26 = 7;
x_27 = l_List_foldl___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__0(x_26, x_21);
x_28 = lean_uint64_mix_hash(x_25, x_27);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_array_get_size(x_22);
x_36 = lean_nat_dec_lt(x_34, x_35);
if (x_36 == 0)
{
x_29 = x_26;
goto block_33;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_35, x_35);
if (x_37 == 0)
{
if (x_36 == 0)
{
x_29 = x_26;
goto block_33;
}
else
{
size_t x_38; size_t x_39; uint64_t x_40; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_35);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__1___redArg(x_22, x_38, x_39, x_26);
x_29 = x_40;
goto block_33;
}
}
else
{
size_t x_41; size_t x_42; uint64_t x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_35);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__1___redArg(x_22, x_41, x_42, x_26);
x_29 = x_43;
goto block_33;
}
}
block_33:
{
uint64_t x_30; uint64_t x_31; uint64_t x_32; 
x_30 = lean_uint64_mix_hash(x_28, x_29);
x_31 = 0;
x_32 = lean_uint64_mix_hash(x_30, x_31);
return x_32;
}
}
default: 
{
lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
x_46 = 4;
x_47 = l_Lean_instHashableFVarId_hash(x_44);
x_48 = lean_uint64_mix_hash(x_46, x_47);
x_49 = 7;
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_array_get_size(x_45);
x_52 = lean_nat_dec_lt(x_50, x_51);
if (x_52 == 0)
{
uint64_t x_53; 
x_53 = lean_uint64_mix_hash(x_48, x_49);
return x_53;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_51, x_51);
if (x_54 == 0)
{
if (x_52 == 0)
{
uint64_t x_55; 
x_55 = lean_uint64_mix_hash(x_48, x_49);
return x_55;
}
else
{
size_t x_56; size_t x_57; uint64_t x_58; uint64_t x_59; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_51);
x_58 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__1___redArg(x_45, x_56, x_57, x_49);
x_59 = lean_uint64_mix_hash(x_48, x_58);
return x_59;
}
}
else
{
size_t x_60; size_t x_61; uint64_t x_62; uint64_t x_63; 
x_60 = 0;
x_61 = lean_usize_of_nat(x_51);
x_62 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__1___redArg(x_45, x_60, x_61, x_49);
x_63 = lean_uint64_mix_hash(x_48, x_62);
return x_63;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableLetValue_hash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_instHashableLetValue_hash(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, uint64_t x_5) {
_start:
{
uint64_t x_6; 
x_6 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__1___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; uint64_t x_9; uint64_t x_10; lean_object* x_11; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_instHashableLetValue_hash_spec__1(x_6, x_2, x_7, x_8, x_9);
lean_dec_ref(x_2);
x_11 = lean_box_uint64(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableLetValue(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instHashableLetValue_hash___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instHashableLetValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instHashableLetValue(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Arg_toLetValue___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg___closed__0;
lean_inc(x_2);
x_4 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_box(1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_toLetValue___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_toLetValue(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_toLetValue___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Arg_toLetValue(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_instInhabitedLetValue_default(x_1);
x_4 = lean_panic_fn(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp_spec__0(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(139u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp___closed__0));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_instBEqFVarId_beq(x_6, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_inc(x_5);
lean_inc(x_4);
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 0);
lean_dec(x_11);
lean_ctor_set(x_2, 2, x_3);
return x_2;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 2, x_3);
return x_12;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp___closed__1;
x_14 = l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp_spec__0(x_1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateConstImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(146u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateConstImp___closed__0));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateConstImp(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_24; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_24 = lean_name_eq(x_6, x_3);
if (x_24 == 0)
{
x_9 = x_24;
goto block_23;
}
else
{
size_t x_25; size_t x_26; uint8_t x_27; 
x_25 = lean_ptr_addr(x_7);
x_26 = lean_ptr_addr(x_4);
x_27 = lean_usize_dec_eq(x_25, x_26);
x_9 = x_27;
goto block_23;
}
block_23:
{
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
lean_ctor_set(x_2, 2, x_5);
lean_ctor_set(x_2, 1, x_4);
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_5);
return x_14;
}
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = lean_ptr_addr(x_8);
x_16 = lean_ptr_addr(x_5);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_2, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_2, 0);
lean_dec(x_21);
lean_ctor_set(x_2, 2, x_5);
lean_ctor_set(x_2, 1, x_4);
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_22; 
lean_dec(x_2);
x_22 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_4);
lean_ctor_set(x_22, 2, x_5);
return x_22;
}
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateConstImp___closed__1;
x_29 = l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp_spec__0(x_1, x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateConstImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateConstImp(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(153u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___closed__0));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_instBEqFVarId_beq(x_8, x_3);
if (x_10 == 0)
{
x_5 = x_10;
goto block_7;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = lean_ptr_addr(x_9);
x_12 = lean_ptr_addr(x_4);
x_13 = lean_usize_dec_eq(x_11, x_12);
x_5 = x_13;
goto block_7;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_4);
lean_dec(x_3);
x_14 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___closed__1;
x_15 = l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp_spec__0(x_1, x_14);
return x_15;
}
block_7:
{
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(x_5, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(161u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___closed__0));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ptr_addr(x_6);
x_8 = lean_ptr_addr(x_3);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_inc(x_5);
lean_inc(x_4);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
lean_ctor_set(x_2, 2, x_3);
return x_2;
}
else
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_3);
return x_14;
}
}
else
{
lean_dec_ref(x_3);
return x_2;
}
}
case 4:
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ptr_addr(x_16);
x_18 = lean_ptr_addr(x_3);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_inc(x_15);
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_2, 0);
lean_dec(x_22);
lean_ctor_set(x_2, 1, x_3);
return x_2;
}
else
{
lean_object* x_23; 
lean_dec(x_2);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
}
else
{
lean_dec_ref(x_3);
return x_2;
}
}
default: 
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_24 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___closed__1;
x_25 = l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp_spec__0(x_1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LetValue_toExpr_spec__0___redArg(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Compiler_LCNF_Arg_toExpr___redArg(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LetValue_toExpr_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LetValue_toExpr_spec__0___redArg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_2);
x_4 = l_Lean_Compiler_LCNF_LitValue_toExpr(x_3);
return x_4;
}
case 1:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_erasedExpr;
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = l_Lean_Expr_fvar___override(x_8);
x_10 = l_Lean_Expr_proj___override(x_6, x_7, x_9);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_2);
x_14 = l_Lean_Expr_const___override(x_11, x_12);
x_15 = lean_array_size(x_13);
x_16 = 0;
x_17 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LetValue_toExpr_spec__0___redArg(x_15, x_16, x_13);
x_18 = l_Lean_mkAppN(x_14, x_17);
lean_dec_ref(x_17);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_20);
lean_dec_ref(x_2);
x_21 = l_Lean_Expr_fvar___override(x_19);
x_22 = lean_array_size(x_20);
x_23 = 0;
x_24 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LetValue_toExpr_spec__0___redArg(x_22, x_23, x_20);
x_25 = l_Lean_mkAppN(x_21, x_24);
lean_dec_ref(x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LetValue_toExpr_spec__0(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LetValue_toExpr_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LetValue_toExpr_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LetValue_toExpr_spec__0(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLetDecl_default(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_instInhabitedFVarId_default;
x_3 = lean_box(0);
x_4 = l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__2;
x_5 = l_Lean_Compiler_LCNF_instInhabitedLetValue_default(x_1);
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLetDecl_default___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedLetDecl_default(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLetDecl(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedLetDecl_default(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedLetDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedLetDecl(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqLetDecl_beq(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_ctor_get(x_3, 3);
x_12 = l_Lean_instBEqFVarId_beq(x_4, x_8);
if (x_12 == 0)
{
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_name_eq(x_5, x_9);
if (x_13 == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_expr_eqv(x_6, x_10);
if (x_14 == 0)
{
return x_14;
}
else
{
uint8_t x_15; 
x_15 = l_Lean_Compiler_LCNF_instBEqLetValue_beq(x_1, x_7, x_11);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqLetDecl_beq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_4, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqLetDecl(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instBEqLetDecl_beq___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqLetDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instBEqLetDecl(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Alt___auto__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Alt___auto__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__9;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_ctorIdx___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Alt_ctorIdx___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_ctorIdx(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Alt_ctorIdx___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Alt_ctorIdx(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_4(x_2, x_3, x_4, x_5, lean_box(0));
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_ctorElim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Alt_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Compiler_LCNF_Alt_ctorElim(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_alt_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Alt_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_alt_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Alt_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_alt_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_Alt_alt_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_default_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Alt_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_default_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Alt_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_default_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_Alt_default_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_ctorIdx___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Code_ctorIdx___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_ctorIdx(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Code_ctorIdx___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Code_ctorIdx(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_3(x_2, x_3, x_4, lean_box(0));
return x_5;
}
case 3:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
case 4:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
case 5:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_apply_1(x_2, x_11);
return x_12;
}
case 6:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_13);
lean_dec_ref(x_1);
x_14 = lean_apply_1(x_2, x_13);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_17 = lean_apply_2(x_2, x_15, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_ctorElim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Code_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Compiler_LCNF_Code_ctorElim(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_let_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Code_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_let_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Code_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_let_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_Code_let_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_fun_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Code_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_fun_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Code_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_fun_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_Code_fun_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_jp_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Code_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_jp_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Code_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_jp_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_Code_jp_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_jmp_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Code_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_jmp_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Code_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_jmp_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_Code_jmp_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cases_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Code_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cases_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Code_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cases_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_Code_cases_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_return_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Code_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_return_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Code_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_return_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_Code_return_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_unreach_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Code_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_unreach_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Code_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_unreach_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_Code_unreach_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCases_default__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCases_default__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_instInhabitedCases_default__1___closed__0;
x_2 = l_Lean_instInhabitedFVarId_default;
x_3 = l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__2;
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCases_default__1(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedCases_default__1___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCases_default__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedCases_default__1(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCases(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedCases_default__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCases___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedCases(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCode_default__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedCode_default__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___closed__0;
x_2 = l_Lean_instInhabitedFVarId_default;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCode(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCode___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedCode(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_fvarId___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_fvarId___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_FunDecl_fvarId___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_fvarId(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_fvarId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_FunDecl_fvarId(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_binderName___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_binderName___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_FunDecl_binderName___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_binderName(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_binderName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_FunDecl_binderName(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_params___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_params___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_FunDecl_params___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_params(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_params___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_FunDecl_params(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_type___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_type___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_FunDecl_type___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_type(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_type___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_FunDecl_type(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_value___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_value___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_FunDecl_value___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_value(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_value___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_FunDecl_value(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateBinderName___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateBinderName(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
lean_dec(x_5);
lean_ctor_set(x_2, 1, x_3);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get(x_2, 4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_8);
lean_ctor_set(x_10, 4, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_updateBinderName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_FunDecl_updateBinderName(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toParam___redArg(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toParam___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Compiler_LCNF_FunDecl_toParam___redArg(x_1, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toParam(uint8_t x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_7 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*3, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_3);
x_6 = l_Lean_Compiler_LCNF_FunDecl_toParam(x_4, x_2, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_typeName___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_typeName___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Cases_typeName___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_typeName(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_typeName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Cases_typeName(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_resultType___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_resultType___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Cases_resultType___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_resultType(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_resultType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Cases_resultType(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_discr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_discr___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Cases_discr___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_discr(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_discr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Cases_discr(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_alts___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_alts___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Cases_alts___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_alts(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_alts___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Cases_alts(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_updateAlts___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_dec(x_4);
lean_ctor_set(x_1, 3, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_updateAlts(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 3);
lean_dec(x_5);
lean_ctor_set(x_2, 3, x_3);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_updateAlts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_Cases_updateAlts(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedAlt(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_instInhabitedFVarId_default;
x_3 = lean_box(0);
x_4 = l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1___closed__0;
x_5 = l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__2;
x_6 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
x_7 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_5);
lean_ctor_set(x_7, 4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDecl(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedFunDecl(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_getArity___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_getArity___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_FunDecl_getArity___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_getArity(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_FunDecl_getArity___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_getArity___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_FunDecl_getArity(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Cases_getCtorNames_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_NameSet_insert(x_4, x_12);
x_5 = x_13;
goto block_9;
}
else
{
lean_dec_ref(x_11);
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Cases_getCtorNames_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Cases_getCtorNames_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_getCtorNames___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = l_Lean_NameSet_empty;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
if (x_6 == 0)
{
return x_3;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Cases_getCtorNames_spec__0(x_2, x_8, x_9, x_3);
return x_10;
}
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Cases_getCtorNames_spec__0(x_2, x_11, x_12, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_getCtorNames___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Cases_getCtorNames___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_getCtorNames(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Cases_getCtorNames___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_getCtorNames___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Cases_getCtorNames(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CodeDecl___auto__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Arg___auto__1___closed__9;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_ctorIdx___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_CodeDecl_ctorIdx___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_ctorIdx(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_CodeDecl_ctorIdx___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_CodeDecl_ctorIdx(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_2(x_2, x_3, lean_box(0));
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_ctorElim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_CodeDecl_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Compiler_LCNF_CodeDecl_ctorElim(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_let_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_CodeDecl_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_let_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_CodeDecl_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_let_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_CodeDecl_let_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_fun_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_CodeDecl_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_fun_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_CodeDecl_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_fun_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_CodeDecl_fun_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_jp_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_CodeDecl_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_jp_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_CodeDecl_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_jp_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_CodeDecl_jp_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedLetDecl_default(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedCodeDecl(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_attachCodeDecls_go(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(x_1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_array_get_borrowed(x_7, x_2, x_9);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
x_3 = x_9;
x_4 = x_12;
goto _start;
}
case 1:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_14);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
x_3 = x_9;
x_4 = x_15;
goto _start;
}
default: 
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_17);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
x_3 = x_9;
x_4 = x_18;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_attachCodeDecls_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_attachCodeDecls_go(x_5, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_CodeDecl_fvarId_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_3, x_7, lean_box(0));
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_CodeDecl_fvarId_match__1_splitter(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_CodeDecl_fvarId_match__1_splitter___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_CodeDecl_fvarId_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_CodeDecl_fvarId_match__1_splitter(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_attachCodeDecls_go(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_attachCodeDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_attachCodeDecls(x_4, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget_borrowed(x_1, x_7);
x_9 = lean_array_fget_borrowed(x_2, x_7);
x_10 = l_Lean_Compiler_LCNF_instBEqParam_beq___redArg(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_7);
return x_10;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt_spec__3___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqFunDecl(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; 
x_4 = lean_ptr_addr(x_2);
x_5 = lean_ptr_addr(x_3);
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_21; uint8_t x_27; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get(x_3, 4);
x_27 = l_Lean_instBEqFVarId_beq(x_7, x_12);
if (x_27 == 0)
{
x_21 = x_27;
goto block_26;
}
else
{
uint8_t x_28; 
x_28 = lean_name_eq(x_8, x_13);
x_21 = x_28;
goto block_26;
}
block_20:
{
if (x_17 == 0)
{
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_expr_eqv(x_10, x_15);
if (x_18 == 0)
{
return x_18;
}
else
{
uint8_t x_19; 
x_19 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqImp(x_1, x_11, x_16);
return x_19;
}
}
}
block_26:
{
if (x_21 == 0)
{
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_array_get_size(x_9);
x_23 = lean_array_get_size(x_14);
x_24 = lean_nat_dec_eq(x_22, x_23);
if (x_24 == 0)
{
x_17 = x_6;
goto block_20;
}
else
{
uint8_t x_25; 
x_25 = l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt_spec__3___redArg(x_9, x_14, x_22);
x_17 = x_25;
goto block_20;
}
}
}
}
else
{
return x_6;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_19; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_ctor_get(x_3, 3);
x_19 = lean_expr_eqv(x_5, x_9);
if (x_19 == 0)
{
x_12 = x_19;
goto block_18;
}
else
{
uint8_t x_20; 
x_20 = l_Lean_instBEqFVarId_beq(x_6, x_10);
x_12 = x_20;
goto block_18;
}
block_18:
{
if (x_12 == 0)
{
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_name_eq(x_4, x_8);
if (x_13 == 0)
{
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_array_get_size(x_7);
x_15 = lean_array_get_size(x_11);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases_spec__1___redArg(x_1, x_7, x_11, x_14);
return x_17;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqImp(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; 
x_4 = lean_ptr_addr(x_2);
x_5 = lean_ptr_addr(x_3);
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
switch (lean_obj_tag(x_2)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(x_1, x_7, x_9);
if (x_11 == 0)
{
return x_11;
}
else
{
x_2 = x_8;
x_3 = x_10;
goto _start;
}
}
else
{
return x_6;
}
}
case 1:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqFunDecl(x_1, x_13, x_15);
if (x_17 == 0)
{
return x_17;
}
else
{
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
else
{
return x_6;
}
}
case 2:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqFunDecl(x_1, x_19, x_21);
if (x_23 == 0)
{
return x_23;
}
else
{
x_2 = x_20;
x_3 = x_22;
goto _start;
}
}
else
{
return x_6;
}
}
case 3:
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
x_29 = l_Lean_instBEqFVarId_beq(x_25, x_27);
if (x_29 == 0)
{
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_array_get_size(x_26);
x_31 = lean_array_get_size(x_28);
x_32 = lean_nat_dec_eq(x_30, x_31);
if (x_32 == 0)
{
return x_6;
}
else
{
uint8_t x_33; 
x_33 = l_Array_isEqvAux___at___00Lean_Compiler_LCNF_instBEqLetValue_beq_spec__1___redArg(x_26, x_28, x_30);
return x_33;
}
}
}
else
{
return x_6;
}
}
case 4:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_3, 0);
x_36 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases(x_1, x_34, x_35);
return x_36;
}
else
{
return x_6;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_2, 0);
x_38 = lean_ctor_get(x_3, 0);
x_39 = l_Lean_instBEqFVarId_beq(x_37, x_38);
return x_39;
}
else
{
return x_6;
}
}
default: 
{
if (lean_obj_tag(x_3) == 6)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_2, 0);
x_41 = lean_ctor_get(x_3, 0);
x_42 = lean_expr_eqv(x_40, x_41);
return x_42;
}
else
{
return x_6;
}
}
}
}
else
{
return x_6;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 2);
x_13 = lean_name_eq(x_4, x_7);
if (x_13 == 0)
{
x_10 = x_13;
goto block_12;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_array_get_size(x_5);
x_15 = lean_array_get_size(x_8);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt_spec__3___redArg(x_5, x_8, x_14);
x_10 = x_17;
goto block_12;
}
}
block_12:
{
if (x_10 == 0)
{
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqImp(x_1, x_6, x_9);
return x_11;
}
}
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
else
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_3, 0);
x_21 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqImp(x_1, x_19, x_20);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = 0;
return x_22;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases_spec__1___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 1)
{
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
x_9 = lean_array_fget_borrowed(x_2, x_8);
x_10 = lean_array_fget_borrowed(x_3, x_8);
x_11 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt(x_1, x_9, x_10);
if (x_11 == 0)
{
lean_dec(x_8);
return x_11;
}
else
{
x_4 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
x_6 = l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases_spec__1___redArg(x_5, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases(x_4, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt(x_4, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqFunDecl(x_4, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqImp(x_4, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases_spec__1___redArg(x_1, x_2, x_3, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
x_8 = l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqCases_spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt_spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt_spec__3___redArg(x_2, x_3, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
x_8 = l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt_spec__3(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqCode(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqImp___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqCode___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instBEqCode(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqFunDecl(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqFunDecl___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqFunDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instBEqFunDecl(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_getCode___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_getCode___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Alt_getCode___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_getCode(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_3);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_getCode___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Alt_getCode(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Alt_getParams___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_getParams___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Alt_getParams___redArg___closed__0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_getParams___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Alt_getParams___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_getParams(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Alt_getParams___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_getParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Alt_getParams(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Alt_forCodeM___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_forCodeM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Compiler_LCNF_Alt_forCodeM(x_1, x_6, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ptr_addr(x_5);
x_7 = lean_ptr_addr(x_2);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_inc_ref(x_4);
lean_inc(x_3);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_13, 2, x_2);
return x_13;
}
}
else
{
lean_dec_ref(x_2);
return x_1;
}
}
else
{
lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ptr_addr(x_14);
x_16 = lean_ptr_addr(x_2);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_1, 0);
lean_dec(x_19);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
return x_20;
}
}
else
{
lean_dec_ref(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(x_1);
x_4 = lean_panic_fn(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp_spec__0(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(358u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___closed__0));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; size_t x_15; size_t x_16; uint8_t x_17; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_15 = lean_ptr_addr(x_7);
x_16 = lean_ptr_addr(x_4);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
x_8 = x_17;
goto block_14;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = lean_ptr_addr(x_6);
x_19 = lean_ptr_addr(x_3);
x_20 = lean_usize_dec_eq(x_18, x_19);
x_8 = x_20;
goto block_14;
}
block_14:
{
if (x_8 == 0)
{
uint8_t x_9; 
lean_inc(x_5);
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_dec(x_12);
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
return x_2;
}
else
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 2, x_4);
return x_13;
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_2;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_21 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___closed__1;
x_22 = l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp_spec__0(x_1, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(365u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp___closed__0));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 2);
x_9 = lean_ctor_get(x_4, 3);
x_10 = lean_ptr_addr(x_9);
lean_dec_ref(x_9);
x_11 = lean_ptr_addr(x_3);
x_12 = lean_usize_dec_eq(x_10, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
lean_ctor_set(x_4, 3, x_3);
return x_2;
}
else
{
lean_object* x_15; 
lean_dec(x_2);
lean_ctor_set(x_4, 3, x_3);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
else
{
lean_free_object(x_4);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
return x_2;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 2);
x_19 = lean_ctor_get(x_4, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_20 = lean_ptr_addr(x_19);
lean_dec_ref(x_19);
x_21 = lean_ptr_addr(x_3);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_23 = x_2;
} else {
 lean_dec_ref(x_2);
 x_23 = lean_box(0);
}
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_3);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(4, 1, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_3);
return x_2;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_26 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
x_27 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp___closed__1;
x_28 = l_panic___redArg(x_26, x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(376u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp___closed__0));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_15; size_t x_18; size_t x_19; uint8_t x_20; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_10);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 x_11 = x_6;
} else {
 lean_dec_ref(x_6);
 x_11 = lean_box(0);
}
x_18 = lean_ptr_addr(x_10);
lean_dec_ref(x_10);
x_19 = lean_ptr_addr(x_5);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_dec_ref(x_8);
x_15 = x_20;
goto block_17;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = lean_ptr_addr(x_8);
lean_dec_ref(x_8);
x_22 = lean_ptr_addr(x_3);
x_23 = lean_usize_dec_eq(x_21, x_22);
x_15 = x_23;
goto block_17;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
if (lean_is_scalar(x_11)) {
 x_12 = lean_alloc_ctor(0, 4, 0);
} else {
 x_12 = x_11;
}
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_3);
lean_ctor_set(x_12, 2, x_4);
lean_ctor_set(x_12, 3, x_5);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
block_17:
{
if (x_15 == 0)
{
lean_dec(x_9);
lean_dec_ref(x_2);
goto block_14;
}
else
{
uint8_t x_16; 
x_16 = l_Lean_instBEqFVarId_beq(x_9, x_4);
lean_dec(x_9);
if (x_16 == 0)
{
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_2;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_24 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
x_25 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp___closed__1;
x_26 = l_panic___redArg(x_24, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(383u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp___closed__0));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ptr_addr(x_9);
x_11 = lean_ptr_addr(x_4);
x_12 = lean_usize_dec_eq(x_10, x_11);
if (x_12 == 0)
{
x_5 = x_12;
goto block_7;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ptr_addr(x_8);
x_14 = lean_ptr_addr(x_3);
x_15 = lean_usize_dec_eq(x_13, x_14);
x_5 = x_15;
goto block_7;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_16 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
x_17 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp___closed__1;
x_18 = l_panic___redArg(x_16, x_17);
return x_18;
}
block_7:
{
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_inc_ref(x_2);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp(x_5, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(392u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__0));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ptr_addr(x_5);
x_7 = lean_ptr_addr(x_3);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_inc_ref(x_4);
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 0);
lean_dec(x_11);
lean_ctor_set(x_2, 1, x_3);
return x_2;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
else
{
lean_dec_ref(x_3);
return x_2;
}
}
case 1:
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ptr_addr(x_14);
x_16 = lean_ptr_addr(x_3);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_inc_ref(x_13);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_2, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 0);
lean_dec(x_20);
lean_ctor_set(x_2, 1, x_3);
return x_2;
}
else
{
lean_object* x_21; 
lean_dec(x_2);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
else
{
lean_dec_ref(x_3);
return x_2;
}
}
case 2:
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ptr_addr(x_23);
x_25 = lean_ptr_addr(x_3);
x_26 = lean_usize_dec_eq(x_24, x_25);
if (x_26 == 0)
{
uint8_t x_27; 
lean_inc_ref(x_22);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_2, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_2, 0);
lean_dec(x_29);
lean_ctor_set(x_2, 1, x_3);
return x_2;
}
else
{
lean_object* x_30; 
lean_dec(x_2);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_3);
return x_30;
}
}
else
{
lean_dec_ref(x_3);
return x_2;
}
}
default: 
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_31 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
x_32 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__1;
x_33 = l_panic___redArg(x_31, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(400u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp___closed__0));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_8; 
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ptr_addr(x_12);
x_14 = lean_ptr_addr(x_4);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
x_5 = x_15;
goto block_7;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = lean_ptr_addr(x_11);
x_17 = lean_ptr_addr(x_3);
x_18 = lean_usize_dec_eq(x_16, x_17);
x_5 = x_18;
goto block_7;
}
}
case 2:
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ptr_addr(x_20);
x_22 = lean_ptr_addr(x_4);
x_23 = lean_usize_dec_eq(x_21, x_22);
if (x_23 == 0)
{
x_8 = x_23;
goto block_10;
}
else
{
size_t x_24; size_t x_25; uint8_t x_26; 
x_24 = lean_ptr_addr(x_19);
x_25 = lean_ptr_addr(x_3);
x_26 = lean_usize_dec_eq(x_24, x_25);
x_8 = x_26;
goto block_10;
}
}
default: 
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_27 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
x_28 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp___closed__1;
x_29 = l_panic___redArg(x_27, x_28);
return x_29;
}
}
block_7:
{
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_inc_ref(x_2);
return x_2;
}
}
block_10:
{
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_inc_ref(x_2);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp(x_5, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(407u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp___closed__0));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_instBEqFVarId_beq(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_9 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
x_10 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp___closed__1;
x_11 = l_panic___redArg(x_9, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(414u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp___closed__0));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_instBEqFVarId_beq(x_8, x_3);
if (x_10 == 0)
{
x_5 = x_10;
goto block_7;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = lean_ptr_addr(x_9);
x_12 = lean_ptr_addr(x_4);
x_13 = lean_usize_dec_eq(x_11, x_12);
x_5 = x_13;
goto block_7;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_4);
lean_dec(x_3);
x_14 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
x_15 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp___closed__1;
x_16 = l_panic___redArg(x_14, x_15);
return x_16;
}
block_7:
{
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_2);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp(x_5, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(421u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp___closed__0));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_4; size_t x_5; size_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ptr_addr(x_4);
x_6 = lean_ptr_addr(x_3);
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
}
else
{
lean_dec_ref(x_3);
return x_2;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_11 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
x_12 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp___closed__1;
x_13 = l_panic___redArg(x_11, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateParamCoreImp___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_7 = lean_ptr_addr(x_2);
x_8 = lean_ptr_addr(x_5);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_inc(x_4);
lean_inc(x_3);
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_2);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_6);
return x_14;
}
}
else
{
lean_dec_ref(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateParamCoreImp(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateParamCoreImp___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateParamCoreImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateParamCoreImp(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetDeclCoreImp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; size_t x_16; size_t x_17; uint8_t x_18; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_16 = lean_ptr_addr(x_2);
x_17 = lean_ptr_addr(x_6);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
x_8 = x_18;
goto block_15;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_ptr_addr(x_3);
x_20 = lean_ptr_addr(x_7);
x_21 = lean_usize_dec_eq(x_19, x_20);
x_8 = x_21;
goto block_15;
}
block_15:
{
if (x_8 == 0)
{
uint8_t x_9; 
lean_inc(x_5);
lean_inc(x_4);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 3);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
lean_ctor_set(x_1, 3, x_3);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_2);
lean_ctor_set(x_14, 3, x_3);
return x_14;
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetDeclCoreImp(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetDeclCoreImp___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetDeclCoreImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetDeclCoreImp(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunDeclCoreImp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_29; size_t x_30; uint8_t x_31; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 4);
x_29 = lean_ptr_addr(x_2);
x_30 = lean_ptr_addr(x_8);
x_31 = lean_usize_dec_eq(x_29, x_30);
if (x_31 == 0)
{
x_10 = x_31;
goto block_28;
}
else
{
size_t x_32; size_t x_33; uint8_t x_34; 
x_32 = lean_ptr_addr(x_3);
x_33 = lean_ptr_addr(x_7);
x_34 = lean_usize_dec_eq(x_32, x_33);
x_10 = x_34;
goto block_28;
}
block_28:
{
if (x_10 == 0)
{
uint8_t x_11; 
lean_inc(x_6);
lean_inc(x_5);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 4);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 0);
lean_dec(x_16);
lean_ctor_set(x_1, 4, x_4);
lean_ctor_set(x_1, 3, x_2);
lean_ctor_set(x_1, 2, x_3);
return x_1;
}
else
{
lean_object* x_17; 
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_3);
lean_ctor_set(x_17, 3, x_2);
lean_ctor_set(x_17, 4, x_4);
return x_17;
}
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = lean_ptr_addr(x_4);
x_19 = lean_ptr_addr(x_9);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc(x_6);
lean_inc(x_5);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_1, 4);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 3);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_1, 0);
lean_dec(x_26);
lean_ctor_set(x_1, 4, x_4);
lean_ctor_set(x_1, 3, x_2);
lean_ctor_set(x_1, 2, x_3);
return x_1;
}
else
{
lean_object* x_27; 
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_6);
lean_ctor_set(x_27, 2, x_3);
lean_ctor_set(x_27, 3, x_2);
lean_ctor_set(x_27, 4, x_4);
return x_27;
}
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_1;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunDeclCoreImp(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunDeclCoreImp___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunDeclCoreImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunDeclCoreImp(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Cases_extractAlt_x21_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(x_1);
x_4 = l_Lean_Compiler_LCNF_instInhabitedCases_default__1(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_panic_fn(x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Cases_extractAlt_x21_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_panic___at___00Lean_Compiler_LCNF_Cases_extractAlt_x21_spec__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Cases_extractAlt_x21___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_name_eq(x_1, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Cases_extractAlt_x21___lam__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21___lam__1(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Cases_extractAlt_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1));
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(471u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_Cases_extractAlt_x21___closed__1));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_17; lean_object* x_18; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_7);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_8 = x_2;
} else {
 lean_dec_ref(x_2);
 x_8 = lean_box(0);
}
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Cases_extractAlt_x21___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_3);
x_10 = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(x_1);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_9, x_7, x_17);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_11 = x_19;
goto block_16;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
x_20 = ((lean_object*)(l_Lean_Compiler_LCNF_Cases_extractAlt_x21___closed__0));
x_21 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_20, x_7, x_17);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_11 = x_22;
goto block_16;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_21);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_23 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21___closed__2;
x_24 = l_panic___at___00Lean_Compiler_LCNF_Cases_extractAlt_x21_spec__0(x_1, x_23);
return x_24;
}
}
block_16:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_get(x_10, x_7, x_11);
x_13 = l_Array_eraseIdx_x21___redArg(x_7, x_11);
if (lean_is_scalar(x_8)) {
 x_14 = lean_alloc_ctor(0, 4, 0);
} else {
 x_14 = x_8;
}
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_6);
lean_ctor_set(x_14, 3, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Cases_extractAlt_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_12);
x_6 = x_12;
goto block_11;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_13);
x_6 = x_13;
goto block_11;
}
block_11:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_apply_1(x_3, x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg___lam__0), 3, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_7);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Alt_mapCodeM___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Compiler_LCNF_Alt_mapCodeM(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_isDecl___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 1:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 2:
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
default: 
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isDecl___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_Code_isDecl___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_isDecl(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Compiler_LCNF_Code_isDecl___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isDecl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Code_isDecl(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_isFun___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isFun___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_Code_isFun___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_isFun(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Compiler_LCNF_Code_isFun___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isFun___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Code_isFun(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_instBEqFVarId_beq(x_3, x_2);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isReturnOf___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_isReturnOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_size_go(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_2 = x_4;
x_3 = x_6;
goto _start;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_8, 4);
x_11 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_size_go(x_1, x_10, x_3);
x_2 = x_9;
x_3 = x_11;
goto _start;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_13, 4);
x_16 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_size_go(x_1, x_15, x_3);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
case 3:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
return x_19;
}
case 4:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_20, 3);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
lean_dec(x_3);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_array_get_size(x_21);
x_26 = lean_nat_dec_lt(x_24, x_25);
if (x_26 == 0)
{
return x_23;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_25, x_25);
if (x_27 == 0)
{
if (x_26 == 0)
{
return x_23;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_25);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_size_go_spec__0(x_1, x_21, x_28, x_29, x_23);
return x_30;
}
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_25);
x_33 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_size_go_spec__0(x_1, x_21, x_31, x_32, x_23);
return x_33;
}
}
}
default: 
{
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_size_go_spec__0(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_3, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_16);
lean_dec_ref(x_15);
x_6 = x_16;
goto block_13;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_15);
x_6 = x_17;
goto block_13;
}
}
else
{
return x_5;
}
block_13:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_9 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_size_go(x_1, x_6, x_8);
lean_dec_ref(x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_size_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_size_go_spec__0(x_6, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_size_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_size_go(x_4, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_size(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_size_go(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_size___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Code_size(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_inc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
x_5 = lean_nat_dec_le(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_inc___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_inc(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_inc(x_2, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
x_3 = x_5;
x_4 = x_7;
goto _start;
}
else
{
return x_6;
}
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_inc(x_2, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_9, 4);
x_14 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go(x_1, x_2, x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec_ref(x_14);
x_3 = x_10;
x_4 = x_15;
goto _start;
}
else
{
return x_14;
}
}
else
{
return x_11;
}
}
case 2:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
x_19 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_inc(x_2, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_17, 4);
x_22 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go(x_1, x_2, x_21, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec_ref(x_22);
x_3 = x_18;
x_4 = x_23;
goto _start;
}
else
{
return x_22;
}
}
else
{
return x_19;
}
}
case 3:
{
lean_object* x_25; 
x_25 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_inc(x_2, x_4);
lean_dec(x_4);
return x_25;
}
case 4:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_inc(x_2, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_ctor_get(x_27, 1);
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_26, 3);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_array_get_size(x_31);
x_34 = lean_box(0);
x_35 = lean_nat_dec_lt(x_32, x_33);
if (x_35 == 0)
{
lean_ctor_set(x_27, 0, x_34);
return x_27;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_33, x_33);
if (x_36 == 0)
{
if (x_35 == 0)
{
lean_ctor_set(x_27, 0, x_34);
return x_27;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; 
lean_free_object(x_27);
x_37 = 0;
x_38 = lean_usize_of_nat(x_33);
x_39 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go_spec__0(x_1, x_2, x_31, x_37, x_38, x_34, x_29);
return x_39;
}
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; 
lean_free_object(x_27);
x_40 = 0;
x_41 = lean_usize_of_nat(x_33);
x_42 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go_spec__0(x_1, x_2, x_31, x_40, x_41, x_34, x_29);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_dec(x_27);
x_44 = lean_ctor_get(x_26, 3);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_array_get_size(x_44);
x_47 = lean_box(0);
x_48 = lean_nat_dec_lt(x_45, x_46);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_46, x_46);
if (x_50 == 0)
{
if (x_48 == 0)
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_43);
return x_51;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_46);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go_spec__0(x_1, x_2, x_44, x_52, x_53, x_47, x_43);
return x_54;
}
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; 
x_55 = 0;
x_56 = lean_usize_of_nat(x_46);
x_57 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go_spec__0(x_1, x_2, x_44, x_55, x_56, x_47, x_43);
return x_57;
}
}
}
}
else
{
return x_27;
}
}
default: 
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_4);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_4, x_5);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_17);
lean_dec_ref(x_16);
x_18 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go(x_1, x_2, x_17, x_7);
lean_dec_ref(x_17);
x_8 = x_18;
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_16);
x_20 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go(x_1, x_2, x_19, x_7);
lean_dec_ref(x_19);
x_8 = x_20;
goto block_14;
}
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
block_14:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_4 = x_12;
x_6 = x_9;
x_7 = x_10;
goto _start;
}
else
{
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go_spec__0(x_8, x_2, x_3, x_9, x_10, x_6, x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go(x_5, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_sizeLe(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_sizeLe_go(x_1, x_3, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec_ref(x_5);
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec_ref(x_5);
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_sizeLe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_Code_sizeLe(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg(x_1, x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_4);
x_8 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg(x_1, x_2, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg(x_2, x_3, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_10, 4);
lean_inc_ref(x_12);
lean_dec_ref(x_10);
lean_inc(x_3);
lean_inc_ref(x_2);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg___lam__1), 4, 3);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_11);
x_14 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg(x_2, x_3, x_12);
x_15 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_14, x_13);
return x_15;
}
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
lean_dec(x_5);
x_16 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_18);
lean_dec_ref(x_16);
lean_inc(x_3);
lean_inc_ref(x_2);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg___lam__1), 4, 3);
lean_closure_set(x_19, 0, x_2);
lean_closure_set(x_19, 1, x_3);
lean_closure_set(x_19, 2, x_17);
x_20 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg(x_2, x_3, x_18);
x_21 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_20, x_19);
return x_21;
}
case 4:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_22);
lean_dec_ref(x_1);
x_23 = lean_ctor_get(x_22, 3);
lean_inc_ref(x_23);
lean_dec_ref(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_array_get_size(x_23);
x_26 = lean_box(0);
x_27 = lean_nat_dec_lt(x_24, x_25);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec_ref(x_23);
lean_dec(x_6);
lean_dec_ref(x_2);
x_28 = lean_apply_2(x_5, lean_box(0), x_26);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_25, x_25);
if (x_29 == 0)
{
if (x_27 == 0)
{
lean_object* x_30; 
lean_dec_ref(x_23);
lean_dec(x_6);
lean_dec_ref(x_2);
x_30 = lean_apply_2(x_5, lean_box(0), x_26);
return x_30;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
lean_dec(x_5);
x_31 = 0;
x_32 = lean_usize_of_nat(x_25);
x_33 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_2, x_6, x_23, x_31, x_32, x_26);
return x_33;
}
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
lean_dec(x_5);
x_34 = 0;
x_35 = lean_usize_of_nat(x_25);
x_36 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_2, x_6, x_23, x_34, x_35, x_26);
return x_36;
}
}
}
default: 
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_37 = lean_box(0);
x_38 = lean_apply_2(x_5, lean_box(0), x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_inc(x_2);
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg___lam__0), 4, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_inc(x_2);
lean_inc_ref(x_3);
x_8 = lean_apply_1(x_2, x_3);
lean_inc(x_5);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg___lam__3), 7, 6);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_5);
lean_closure_set(x_9, 4, x_6);
lean_closure_set(x_9, 5, x_7);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___redArg(x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Compiler_LCNF_Code_forM(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Level_instantiateParams(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_instantiateLevelParamsNoCache(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; uint8_t x_13; 
x_7 = lean_array_fget_borrowed(x_4, x_3);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_2);
lean_inc(x_1);
lean_inc_ref(x_8);
x_9 = l_Lean_Expr_instantiateLevelParamsNoCache(x_8, x_1, x_2);
lean_inc(x_7);
x_10 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateParamCoreImp___redArg(x_7, x_9);
x_11 = lean_ptr_addr(x_7);
x_12 = lean_ptr_addr(x_10);
x_13 = lean_usize_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_14);
x_16 = lean_array_fset(x_4, x_3, x_10);
lean_dec(x_3);
x_3 = x_15;
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_3 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instParams_spec__0(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = 0;
lean_inc_ref(x_4);
x_6 = l_Lean_Expr_instantiateLevelParamsNoCache(x_4, x_1, x_2);
x_7 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(x_5, x_3, x_6);
return x_7;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instLetValue___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Level_instantiateParams(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instLetValue_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; uint8_t x_11; 
x_7 = lean_array_fget_borrowed(x_4, x_3);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instArg(x_1, x_2, x_7);
x_9 = lean_ptr_addr(x_7);
x_10 = lean_ptr_addr(x_8);
x_11 = lean_usize_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
x_14 = lean_array_fset(x_4, x_3, x_8);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_3 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instLetValue(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
case 3:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instLetValue___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = 0;
lean_inc(x_5);
x_9 = l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___at___00List_mapMono_spec__0___redArg(x_7, x_5);
x_10 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_6);
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instLetValue_spec__0(x_1, x_2, x_10, x_6);
x_12 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateConstImp(x_8, x_3, x_4, x_9, x_11);
return x_12;
}
case 4:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
x_15 = 0;
x_16 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_14);
x_17 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instLetValue_spec__0(x_1, x_2, x_16, x_14);
x_18 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(x_15, x_3, x_13, x_17);
lean_dec_ref(x_3);
return x_18;
}
default: 
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 2);
x_5 = lean_ctor_get(x_3, 3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc_ref(x_4);
x_6 = l_Lean_Expr_instantiateLevelParamsNoCache(x_4, x_1, x_2);
lean_inc(x_5);
x_7 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instLetValue(x_1, x_2, x_5);
x_8 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetDeclCoreImp___redArg(x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_ctor_get(x_3, 2);
x_6 = 0;
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instParams(x_1, x_2, x_4);
lean_inc_ref(x_5);
x_8 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(x_1, x_2, x_5);
x_9 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(x_6, x_3, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_10);
x_11 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(x_1, x_2, x_10);
x_12 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_3, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; uint8_t x_11; 
x_7 = lean_array_fget_borrowed(x_4, x_3);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instAlt(x_1, x_2, x_7);
x_9 = lean_ptr_addr(x_7);
x_10 = lean_ptr_addr(x_8);
x_11 = lean_usize_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
x_14 = lean_array_fset(x_4, x_3, x_8);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_8);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_3 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; size_t x_14; size_t x_15; uint8_t x_16; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instLetDecl(x_1, x_2, x_4);
lean_inc_ref(x_5);
x_7 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(x_1, x_2, x_5);
x_14 = lean_ptr_addr(x_5);
x_15 = lean_ptr_addr(x_7);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
x_8 = x_16;
goto block_13;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = lean_ptr_addr(x_4);
x_18 = lean_ptr_addr(x_6);
x_19 = lean_usize_dec_eq(x_17, x_18);
x_8 = x_19;
goto block_13;
}
block_13:
{
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
lean_ctor_set(x_3, 1, x_7);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
else
{
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_3;
}
}
}
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; size_t x_30; size_t x_31; uint8_t x_32; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_20);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instFunDecl(x_1, x_2, x_20);
lean_inc_ref(x_21);
x_23 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(x_1, x_2, x_21);
x_30 = lean_ptr_addr(x_21);
x_31 = lean_ptr_addr(x_23);
x_32 = lean_usize_dec_eq(x_30, x_31);
if (x_32 == 0)
{
x_24 = x_32;
goto block_29;
}
else
{
size_t x_33; size_t x_34; uint8_t x_35; 
x_33 = lean_ptr_addr(x_20);
x_34 = lean_ptr_addr(x_22);
x_35 = lean_usize_dec_eq(x_33, x_34);
x_24 = x_35;
goto block_29;
}
block_29:
{
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_3, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_3, 0);
lean_dec(x_27);
lean_ctor_set(x_3, 1, x_23);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
else
{
lean_object* x_28; 
lean_dec(x_3);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
else
{
lean_dec_ref(x_23);
lean_dec_ref(x_22);
return x_3;
}
}
}
case 2:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; size_t x_46; size_t x_47; uint8_t x_48; 
x_36 = lean_ctor_get(x_3, 0);
x_37 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_36);
lean_inc(x_2);
lean_inc(x_1);
x_38 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instFunDecl(x_1, x_2, x_36);
lean_inc_ref(x_37);
x_39 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(x_1, x_2, x_37);
x_46 = lean_ptr_addr(x_37);
x_47 = lean_ptr_addr(x_39);
x_48 = lean_usize_dec_eq(x_46, x_47);
if (x_48 == 0)
{
x_40 = x_48;
goto block_45;
}
else
{
size_t x_49; size_t x_50; uint8_t x_51; 
x_49 = lean_ptr_addr(x_36);
x_50 = lean_ptr_addr(x_38);
x_51 = lean_usize_dec_eq(x_49, x_50);
x_40 = x_51;
goto block_45;
}
block_45:
{
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_3);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_3, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_3, 0);
lean_dec(x_43);
lean_ctor_set(x_3, 1, x_39);
lean_ctor_set(x_3, 0, x_38);
return x_3;
}
else
{
lean_object* x_44; 
lean_dec(x_3);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
}
else
{
lean_dec_ref(x_39);
lean_dec_ref(x_38);
return x_3;
}
}
}
case 3:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_62; 
x_52 = lean_ctor_get(x_3, 0);
x_53 = lean_ctor_get(x_3, 1);
x_54 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_53);
x_55 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instLetValue_spec__0(x_1, x_2, x_54, x_53);
x_62 = l_Lean_instBEqFVarId_beq(x_52, x_52);
if (x_62 == 0)
{
x_56 = x_62;
goto block_61;
}
else
{
size_t x_63; size_t x_64; uint8_t x_65; 
x_63 = lean_ptr_addr(x_53);
x_64 = lean_ptr_addr(x_55);
x_65 = lean_usize_dec_eq(x_63, x_64);
x_56 = x_65;
goto block_61;
}
block_61:
{
if (x_56 == 0)
{
uint8_t x_57; 
lean_inc(x_52);
x_57 = !lean_is_exclusive(x_3);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_3, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_3, 0);
lean_dec(x_59);
lean_ctor_set(x_3, 1, x_55);
return x_3;
}
else
{
lean_object* x_60; 
lean_dec(x_3);
x_60 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
else
{
lean_dec_ref(x_55);
return x_3;
}
}
}
case 4:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_78; size_t x_81; size_t x_82; uint8_t x_83; 
x_66 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_66, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_66, 3);
lean_inc_ref(x_70);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 lean_ctor_release(x_66, 2);
 lean_ctor_release(x_66, 3);
 x_71 = x_66;
} else {
 lean_dec_ref(x_66);
 x_71 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_1);
lean_inc_ref(x_68);
x_72 = l_Lean_Expr_instantiateLevelParamsNoCache(x_68, x_1, x_2);
x_73 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_70);
x_74 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__1(x_1, x_2, x_73, x_70);
x_81 = lean_ptr_addr(x_70);
lean_dec_ref(x_70);
x_82 = lean_ptr_addr(x_74);
x_83 = lean_usize_dec_eq(x_81, x_82);
if (x_83 == 0)
{
lean_dec_ref(x_68);
x_78 = x_83;
goto block_80;
}
else
{
size_t x_84; size_t x_85; uint8_t x_86; 
x_84 = lean_ptr_addr(x_68);
lean_dec_ref(x_68);
x_85 = lean_ptr_addr(x_72);
x_86 = lean_usize_dec_eq(x_84, x_85);
x_78 = x_86;
goto block_80;
}
block_77:
{
lean_object* x_75; lean_object* x_76; 
if (lean_is_scalar(x_71)) {
 x_75 = lean_alloc_ctor(0, 4, 0);
} else {
 x_75 = x_71;
}
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_72);
lean_ctor_set(x_75, 2, x_69);
lean_ctor_set(x_75, 3, x_74);
x_76 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
block_80:
{
if (x_78 == 0)
{
lean_dec_ref(x_3);
goto block_77;
}
else
{
uint8_t x_79; 
x_79 = l_Lean_instBEqFVarId_beq(x_69, x_69);
if (x_79 == 0)
{
lean_dec_ref(x_3);
goto block_77;
}
else
{
lean_dec_ref(x_74);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_67);
return x_3;
}
}
}
}
case 5:
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
default: 
{
lean_object* x_87; lean_object* x_88; size_t x_89; size_t x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_87);
x_88 = l_Lean_Expr_instantiateLevelParamsNoCache(x_87, x_1, x_2);
x_89 = lean_ptr_addr(x_87);
x_90 = lean_ptr_addr(x_88);
x_91 = lean_usize_dec_eq(x_89, x_90);
if (x_91 == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_3);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_3, 0);
lean_dec(x_93);
lean_ctor_set(x_3, 0, x_88);
return x_3;
}
else
{
lean_object* x_94; 
lean_dec(x_3);
x_94 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_94, 0, x_88);
return x_94;
}
}
else
{
lean_dec_ref(x_88);
return x_3;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 2);
x_5 = lean_ctor_get(x_3, 3);
x_6 = lean_ctor_get(x_3, 4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc_ref(x_5);
x_7 = l_Lean_Expr_instantiateLevelParamsNoCache(x_5, x_1, x_2);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instParams(x_1, x_2, x_4);
lean_inc_ref(x_6);
x_9 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(x_1, x_2, x_6);
x_10 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunDeclCoreImp___redArg(x_3, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_ctorIdx___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_DeclValue_ctorIdx___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_ctorIdx(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_DeclValue_ctorIdx___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_DeclValue_ctorIdx(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_ctorElim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_DeclValue_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Compiler_LCNF_DeclValue_ctorElim(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_code_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_DeclValue_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_code_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_DeclValue_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_code_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_DeclValue_code_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_extern_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_DeclValue_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_extern_elim(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_DeclValue_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_extern_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_DeclValue_extern_elim(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclValue_default(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclValue_default___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedDeclValue_default(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclValue(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedDeclValue_default(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedDeclValue(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqDeclValue_beq(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 0);
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqImp(x_1, x_4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
else
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_3, 0);
x_10 = l_Lean_instBEqExternAttrData_beq(x_8, x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqDeclValue_beq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_instBEqDeclValue_beq(x_4, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqDeclValue(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instBEqDeclValue_beq___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqDeclValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instBEqDeclValue(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_size(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_Compiler_LCNF_Code_size(x_1, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_size___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_DeclValue_size(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCode___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec_ref(x_1);
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCode(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_DeclValue_mapCode___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_DeclValue_mapCode(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_DeclValue_mapCodeM___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_apply_1(x_2, x_7);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_apply_2(x_11, lean_box(0), x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_3);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_DeclValue_forCodeM___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Compiler_LCNF_DeclValue_forCodeM(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_apply_2(x_7, lean_box(0), x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedDecl_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl_default(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lean_Compiler_LCNF_instInhabitedDecl_default___closed__0;
x_5 = l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1___closed__0;
x_6 = l_Lean_Compiler_LCNF_instInhabitedDeclValue_default(x_1);
x_7 = 0;
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_4);
lean_ctor_set(x_9, 3, x_5);
lean_ctor_set(x_9, 4, x_6);
lean_ctor_set(x_9, 5, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*6, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*6 + 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl_default___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedDecl_default(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_instInhabitedDecl_default(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instInhabitedDecl(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_instBEqDecl_beq_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_Compiler_instBEqInlineAttributeKind_beq(x_8, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_instBEqDecl_beq_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_instBEqDecl_beq_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Compiler_LCNF_instBEqDecl_beq_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_name_eq(x_6, x_8);
if (x_10 == 0)
{
return x_10;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Compiler_LCNF_instBEqDecl_beq_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___00Lean_Compiler_LCNF_instBEqDecl_beq_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instBEqDecl_beq(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; uint8_t x_24; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_ctor_get(x_2, 4);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get(x_3, 4);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
x_19 = lean_ctor_get(x_3, 5);
x_24 = lean_name_eq(x_4, x_12);
if (x_24 == 0)
{
return x_24;
}
else
{
uint8_t x_25; 
x_25 = l_List_beq___at___00Lean_Compiler_LCNF_instBEqDecl_beq_spec__1(x_5, x_13);
if (x_25 == 0)
{
return x_25;
}
else
{
uint8_t x_26; 
x_26 = lean_expr_eqv(x_6, x_14);
if (x_26 == 0)
{
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_array_get_size(x_7);
x_28 = lean_array_get_size(x_15);
x_29 = lean_nat_dec_eq(x_27, x_28);
if (x_29 == 0)
{
return x_29;
}
else
{
uint8_t x_30; 
x_30 = l_Array_isEqvAux___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqAlt_spec__3___redArg(x_7, x_15, x_27);
if (x_30 == 0)
{
return x_30;
}
else
{
uint8_t x_31; 
x_31 = l_Lean_Compiler_LCNF_instBEqDeclValue_beq(x_1, x_8, x_16);
if (x_31 == 0)
{
return x_31;
}
else
{
if (x_9 == 0)
{
if (x_17 == 0)
{
x_20 = x_31;
goto block_23;
}
else
{
return x_9;
}
}
else
{
x_20 = x_17;
goto block_23;
}
}
}
}
}
}
}
block_23:
{
if (x_20 == 0)
{
return x_20;
}
else
{
if (x_10 == 0)
{
if (x_18 == 0)
{
uint8_t x_21; 
x_21 = l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_instBEqDecl_beq_spec__0(x_11, x_19);
return x_21;
}
else
{
return x_10;
}
}
else
{
if (x_18 == 0)
{
return x_18;
}
else
{
uint8_t x_22; 
x_22 = l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_instBEqDecl_beq_spec__0(x_11, x_19);
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqDecl_beq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_instBEqDecl_beq(x_4, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqDecl(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instBEqDecl_beq___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instBEqDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_instBEqDecl(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_size(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 4);
x_4 = l_Lean_Compiler_LCNF_DeclValue_size(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_size___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Decl_size(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_getArity___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_getArity___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Decl_getArity___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_getArity(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Decl_getArity___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_getArity___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Decl_getArity(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_inlineAttr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 5);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unbox(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_inlineAttr___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_Decl_inlineAttr___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_inlineAttr(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Compiler_LCNF_Decl_inlineAttr___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_inlineAttr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Decl_inlineAttr(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_noinlineAttr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 5);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unbox(x_3);
if (x_4 == 1)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_noinlineAttr___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_Decl_noinlineAttr___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_noinlineAttr(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Compiler_LCNF_Decl_noinlineAttr___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_noinlineAttr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Decl_noinlineAttr(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 5);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unbox(x_3);
if (x_4 == 3)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Decl_inlineIfReduceAttr(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 5);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unbox(x_3);
if (x_4 == 4)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Decl_alwaysInlineAttr(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_inlineable___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 5);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unbox(x_4);
if (x_5 == 1)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_inlineable___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_Decl_inlineable___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Decl_inlineable(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Compiler_LCNF_Decl_inlineable___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_inlineable___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Decl_inlineable(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Decl_castPurity_x21_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_instInhabitedDecl_default(x_1);
x_4 = lean_panic_fn(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Decl_castPurity_x21_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_panic___at___00Lean_Compiler_LCNF_Decl_castPurity_x21_spec__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_castPurity_x21(uint8_t x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Compiler_LCNF_instDecidableEqPurity(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_17; lean_object* x_18; 
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_castPurity_x21___closed__0));
x_7 = lean_unsigned_to_nat(699u);
x_8 = lean_unsigned_to_nat(4u);
x_17 = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_castPurity_x21___closed__1));
if (x_1 == 0)
{
lean_object* x_25; 
x_25 = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__0));
x_18 = x_25;
goto block_24;
}
else
{
lean_object* x_26; 
x_26 = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__1));
x_18 = x_26;
goto block_24;
}
block_16:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_string_append(x_9, x_10);
lean_dec_ref(x_10);
x_12 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__2));
x_13 = lean_string_append(x_11, x_12);
x_14 = l_mkPanicMessageWithDecl(x_5, x_6, x_7, x_8, x_13);
lean_dec_ref(x_13);
x_15 = l_panic___at___00Lean_Compiler_LCNF_Decl_castPurity_x21_spec__0(x_3, x_14);
return x_15;
}
block_24:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_string_append(x_17, x_18);
lean_dec_ref(x_18);
x_20 = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_castPurity_x21___closed__2));
x_21 = lean_string_append(x_19, x_20);
if (x_3 == 0)
{
lean_object* x_22; 
x_22 = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__0));
x_9 = x_21;
x_10 = x_22;
goto block_16;
}
else
{
lean_object* x_23; 
x_23 = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPurity___lam__0___closed__1));
x_9 = x_21;
x_10 = x_23;
goto block_16;
}
}
}
else
{
lean_inc_ref(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_castPurity_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_3);
x_6 = l_Lean_Compiler_LCNF_Decl_castPurity_x21(x_4, x_2, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_instBEqFVarId_beq(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_2);
x_2 = x_3;
goto _start;
}
case 2:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_2 = x_5;
goto _start;
}
case 1:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_2);
x_2 = x_7;
goto _start;
}
case 4:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_findIdx_x3f_loop___redArg(x_11, x_10, x_12);
return x_13;
}
default: 
{
lean_object* x_14; 
lean_dec_ref(x_2);
x_14 = lean_box(0);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox(x_3);
x_7 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go(x_5, x_2, x_6, x_4);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f_go___redArg(x_1, x_3);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_box(0);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_Decl_isCasesOnParam_x3f(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_Expr_instantiateLevelParamsNoCache(x_4, x_3, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; uint8_t x_14; 
x_7 = lean_array_fget_borrowed(x_4, x_3);
x_8 = lean_ctor_get(x_7, 2);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_inc(x_9);
lean_inc_ref(x_8);
x_10 = l_Lean_Expr_instantiateLevelParamsNoCache(x_8, x_9, x_2);
lean_inc(x_7);
x_11 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateParamCoreImp___redArg(x_7, x_10);
x_12 = lean_ptr_addr(x_7);
x_13 = lean_ptr_addr(x_11);
x_14 = lean_usize_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
x_17 = lean_array_fset(x_4, x_3, x_11);
lean_dec(x_3);
x_3 = x_16;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_11);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_3, x_19);
lean_dec(x_3);
x_3 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_4);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams_spec__0___redArg(x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams_spec__0___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams_spec__0(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasLocalInst___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_12 = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(x_4, x_2);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_BinderInfo_isInstImplicit(x_6);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_BinderInfo_isImplicit(x_6);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
x_17 = lean_box(x_16);
lean_ctor_set(x_12, 0, x_17);
x_7 = x_12;
x_8 = x_16;
x_9 = lean_box(0);
goto block_11;
}
else
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_18; 
x_18 = lean_box(x_15);
lean_ctor_set(x_12, 0, x_18);
x_7 = x_12;
x_8 = x_15;
x_9 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_19; 
lean_dec_ref(x_14);
x_19 = lean_box(x_16);
lean_ctor_set(x_12, 0, x_19);
x_7 = x_12;
x_8 = x_16;
x_9 = lean_box(0);
goto block_11;
}
}
}
else
{
lean_object* x_20; 
lean_dec(x_14);
lean_dec_ref(x_5);
x_20 = lean_box(x_15);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
x_22 = l_Lean_BinderInfo_isInstImplicit(x_6);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_BinderInfo_isImplicit(x_6);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_7 = x_25;
x_8 = x_23;
x_9 = lean_box(0);
goto block_11;
}
else
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(x_22);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_7 = x_27;
x_8 = x_22;
x_9 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_21);
x_28 = lean_box(x_23);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_7 = x_29;
x_8 = x_23;
x_9 = lean_box(0);
goto block_11;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_21);
lean_dec_ref(x_5);
x_30 = lean_box(x_22);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec_ref(x_5);
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_12, 0);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
block_11:
{
if (x_8 == 0)
{
lean_dec_ref(x_7);
x_1 = x_5;
goto _start;
}
else
{
lean_dec_ref(x_5);
return x_7;
}
}
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec_ref(x_1);
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasLocalInst___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasLocalInst(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_hasLocalInst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_hasLocalInst(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Decl_isTemplateLike_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Lean_isInstanceReducibleCore(x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Decl_isTemplateLike_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Decl_isTemplateLike_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Decl_isTemplateLike_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Decl_isTemplateLike_spec__0___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Decl_isTemplateLike_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Decl_isTemplateLike_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_7);
x_8 = l_Lean_Compiler_LCNF_hasLocalInst___redArg(x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = 1;
x_12 = lean_unbox(x_10);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_free_object(x_8);
lean_inc(x_6);
x_13 = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Decl_isTemplateLike_spec__0___redArg(x_6, x_3);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Compiler_LCNF_Decl_inlineable___redArg(x_1);
lean_dec_ref(x_1);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_18);
lean_dec(x_5);
x_19 = l_Lean_Compiler_hasSpecializeAttribute(x_18, x_6);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_box(x_19);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; 
x_21 = lean_box(x_11);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
}
else
{
lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
x_22 = lean_box(x_11);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
}
else
{
lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_23 = lean_box(x_11);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Compiler_LCNF_Decl_inlineable___redArg(x_1);
lean_dec_ref(x_1);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_27);
lean_dec(x_5);
x_28 = l_Lean_Compiler_hasSpecializeAttribute(x_27, x_6);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(x_11);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_6);
lean_dec(x_5);
x_33 = lean_box(x_11);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_35 = lean_box(x_11);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_37 = lean_box(x_11);
lean_ctor_set(x_8, 0, x_37);
return x_8;
}
}
else
{
lean_object* x_38; uint8_t x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_8, 0);
lean_inc(x_38);
lean_dec(x_8);
x_39 = 1;
x_40 = lean_unbox(x_38);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_inc(x_6);
x_41 = l_Lean_isInstanceReducible___at___00Lean_Compiler_LCNF_Decl_isTemplateLike_spec__0___redArg(x_6, x_3);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
x_44 = lean_unbox(x_42);
lean_dec(x_42);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = l_Lean_Compiler_LCNF_Decl_inlineable___redArg(x_1);
lean_dec_ref(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_46);
lean_dec(x_5);
x_47 = l_Lean_Compiler_hasSpecializeAttribute(x_46, x_6);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(x_47);
if (lean_is_scalar(x_43)) {
 x_49 = lean_alloc_ctor(0, 1, 0);
} else {
 x_49 = x_43;
}
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(x_39);
if (lean_is_scalar(x_43)) {
 x_51 = lean_alloc_ctor(0, 1, 0);
} else {
 x_51 = x_43;
}
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_6);
lean_dec(x_5);
x_52 = lean_box(x_39);
if (lean_is_scalar(x_43)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_43;
}
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_54 = lean_box(x_39);
if (lean_is_scalar(x_43)) {
 x_55 = lean_alloc_ctor(0, 1, 0);
} else {
 x_55 = x_43;
}
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_56 = lean_box(x_39);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_Decl_isTemplateLike(x_6, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_instInhabitedFVarIdHashSet;
x_4 = lean_alloc_closure((void*)(l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_1(x_6, x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_instBEqFVarId_beq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_instHashableFVarId_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_instHashableFVarId_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1_spec__3_spec__4___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1_spec__3___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_instHashableFVarId_hash(x_2);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__0___redArg(x_2, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_19);
x_27 = lean_array_uset(x_5, x_18, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1___redArg(x_27);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_19);
x_38 = lean_array_uset(x_5, x_18, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_36, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1___redArg(x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__1));
x_2 = lean_unsigned_to_nat(27u);
x_3 = lean_unsigned_to_nat(763u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___closed__0));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_Purity_withAssertPurity___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_10);
lean_dec_ref(x_1);
x_3 = x_9;
x_4 = x_10;
x_5 = x_2;
goto block_8;
}
case 6:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_3 = x_11;
x_4 = x_12;
x_5 = x_2;
goto block_8;
}
case 5:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
x_15 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_14, x_2);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
case 1:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec_ref(x_1);
x_18 = lean_box(0);
x_19 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_2, x_17, x_18);
return x_19;
}
case 10:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_20);
lean_dec_ref(x_1);
x_1 = x_20;
goto _start;
}
case 11:
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_1);
x_22 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___closed__1;
x_23 = l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1(x_22, x_2);
return x_23;
}
case 8:
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_1);
x_24 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___closed__1;
x_25 = l_panic___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1(x_24, x_2);
return x_25;
}
default: 
{
lean_dec_ref(x_1);
return x_2;
}
}
block_8:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_3, x_5);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0_spec__1_spec__3_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArg___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_box(0);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_6, x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArg___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArg___redArg(x_6, x_4);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs_spec__0___redArg(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
if (x_6 == 0)
{
return x_3;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_5);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs_spec__0___redArg(x_2, x_8, x_9, x_3);
return x_10;
}
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs_spec__0___redArg(x_2, x_11, x_12, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs(x_4, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs_spec__0(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs_spec__0(x_6, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectLetValue(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_box(0);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_3, x_4, x_5);
return x_6;
}
case 3:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_7);
lean_dec_ref(x_2);
x_8 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs(x_1, x_7, x_3);
lean_dec_ref(x_7);
return x_8;
}
case 4:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_2);
x_11 = lean_box(0);
x_12 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_3, x_9, x_11);
x_13 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs(x_1, x_10, x_12);
lean_dec_ref(x_10);
return x_13;
}
default: 
{
lean_dec(x_2);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectLetValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectLetValue(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_7, x_4);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
if (x_5 == 0)
{
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams_spec__0(x_1, x_10, x_11, x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams(x_4, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_collectUsed_spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_14);
lean_dec_ref(x_12);
x_15 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams___redArg(x_13, x_5);
lean_dec_ref(x_13);
x_16 = l_Lean_Compiler_LCNF_Code_collectUsed(x_1, x_14, x_15);
x_6 = x_16;
goto block_10;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_12);
x_18 = l_Lean_Compiler_LCNF_Code_collectUsed(x_1, x_17, x_5);
x_6 = x_18;
goto block_10;
}
}
else
{
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_collectUsed(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_6, x_3);
x_9 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectLetValue(x_1, x_7, x_8);
x_2 = x_5;
x_3 = x_9;
goto _start;
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_2);
x_13 = lean_box(0);
x_14 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_3, x_11, x_13);
x_15 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectArgs(x_1, x_12, x_14);
lean_dec_ref(x_12);
return x_15;
}
case 4:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_2);
x_17 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 3);
lean_inc_ref(x_19);
lean_dec_ref(x_16);
x_20 = lean_box(0);
x_21 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_3, x_18, x_20);
x_22 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_17, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get_size(x_19);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_dec_ref(x_19);
return x_22;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_24, x_24);
if (x_26 == 0)
{
if (x_25 == 0)
{
lean_dec_ref(x_19);
return x_22;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_24);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_collectUsed_spec__1(x_1, x_19, x_27, x_28, x_22);
lean_dec_ref(x_19);
return x_29;
}
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_24);
x_32 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_collectUsed_spec__1(x_1, x_19, x_30, x_31, x_22);
lean_dec_ref(x_19);
return x_32;
}
}
}
case 5:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
lean_dec_ref(x_2);
x_34 = lean_box(0);
x_35 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_3, x_33, x_34);
return x_35;
}
case 6:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_36);
lean_dec_ref(x_2);
x_37 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_36, x_3);
return x_37;
}
default: 
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_39);
lean_dec_ref(x_2);
x_40 = l_Lean_Compiler_LCNF_FunDecl_collectUsed(x_1, x_38, x_3);
x_2 = x_39;
x_3 = x_40;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_collectUsed(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_6);
lean_dec_ref(x_2);
x_7 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_5, x_3);
x_8 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectParams___redArg(x_4, x_7);
lean_dec_ref(x_4);
x_9 = l_Lean_Compiler_LCNF_Code_collectUsed(x_1, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_collectUsed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_FunDecl_collectUsed(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_collectUsed_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Code_collectUsed_spec__1(x_6, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_collectUsed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lean_Compiler_LCNF_Code_collectUsed(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectUsedAtExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_8;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit_spec__0(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 3);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_4);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_dec(x_9);
x_4 = x_8;
goto _start;
}
else
{
if (x_12 == 0)
{
lean_dec(x_9);
x_4 = x_8;
goto _start;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_11);
x_17 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit_spec__0(x_9, x_2, x_15, x_16);
if (x_17 == 0)
{
lean_dec(x_9);
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_NameSet_insert(x_5, x_9);
x_4 = x_8;
x_5 = x_19;
goto _start;
}
}
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_21);
lean_dec_ref(x_4);
x_4 = x_21;
goto _start;
}
}
case 1:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_24);
lean_dec_ref(x_4);
x_25 = lean_ctor_get(x_23, 4);
lean_inc_ref(x_25);
lean_dec_ref(x_23);
x_26 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit(x_1, x_2, x_3, x_25, x_5);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_4 = x_24;
x_5 = x_27;
goto _start;
}
case 2:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_4);
x_31 = lean_ctor_get(x_29, 4);
lean_inc_ref(x_31);
lean_dec_ref(x_29);
x_32 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit(x_1, x_2, x_3, x_31, x_5);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_4 = x_30;
x_5 = x_33;
goto _start;
}
case 4:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_35);
lean_dec_ref(x_4);
x_36 = lean_ctor_get(x_35, 3);
lean_inc_ref(x_36);
lean_dec_ref(x_35);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_array_get_size(x_36);
x_39 = lean_box(0);
x_40 = lean_nat_dec_lt(x_37, x_38);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec_ref(x_36);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_5);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_38, x_38);
if (x_42 == 0)
{
if (x_40 == 0)
{
lean_object* x_43; 
lean_dec_ref(x_36);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_5);
return x_43;
}
else
{
size_t x_44; size_t x_45; lean_object* x_46; 
x_44 = 0;
x_45 = lean_usize_of_nat(x_38);
x_46 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit_spec__1(x_1, x_2, x_3, x_36, x_44, x_45, x_39, x_5);
lean_dec_ref(x_36);
return x_46;
}
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; 
x_47 = 0;
x_48 = lean_usize_of_nat(x_38);
x_49 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit_spec__1(x_1, x_2, x_3, x_36, x_47, x_48, x_39, x_5);
lean_dec_ref(x_36);
return x_49;
}
}
}
default: 
{
lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_4);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_5);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit_spec__1(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_5, x_6);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 2);
lean_inc_ref(x_18);
lean_dec_ref(x_17);
x_19 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit(x_1, x_2, x_3, x_18, x_8);
x_9 = x_19;
goto block_15;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_20);
lean_dec_ref(x_17);
x_21 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit(x_1, x_2, x_3, x_20, x_8);
x_9 = x_21;
goto block_15;
}
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
block_15:
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_5, x_12);
x_5 = x_13;
x_7 = x_10;
x_8 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox(x_3);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit_spec__1(x_9, x_2, x_10, x_4, x_11, x_12, x_7, x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox(x_3);
x_8 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit(x_6, x_2, x_7, x_4, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = lean_apply_2(x_1, x_4, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go_spec__0(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_4, x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_9 = lean_array_uget(x_3, x_4);
x_10 = lean_box(x_1);
x_11 = lean_box(x_1);
lean_inc_ref(x_2);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_visit___boxed), 5, 3);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_11);
x_13 = lean_ctor_get(x_9, 4);
lean_inc_ref(x_13);
lean_dec(x_9);
x_14 = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go_spec__0___redArg(x_12, x_13, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_6 = x_15;
x_7 = x_16;
goto _start;
}
else
{
lean_object* x_20; 
lean_dec_ref(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go_spec__1(x_8, x_2, x_3, x_9, x_10, x_6, x_7);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_2);
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
if (x_7 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_inc_ref(x_2);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go_spec__1(x_1, x_2, x_2, x_11, x_12, x_6, x_3);
lean_dec_ref(x_2);
return x_13;
}
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_5);
lean_inc_ref(x_2);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go_spec__1(x_1, x_2, x_2, x_14, x_15, x_6, x_3);
lean_dec_ref(x_2);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_markRecDecls_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_22; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_6, 4);
lean_inc_ref(x_11);
x_12 = lean_ctor_get_uint8(x_6, sizeof(void*)*6 + 1);
x_13 = lean_ctor_get(x_6, 5);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_4, x_3, x_14);
x_22 = l_Lean_NameSet_contains(x_1, x_7);
if (x_22 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_16 = x_6;
goto block_21;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_6, 5);
lean_dec(x_24);
x_25 = lean_ctor_get(x_6, 4);
lean_dec(x_25);
x_26 = lean_ctor_get(x_6, 3);
lean_dec(x_26);
x_27 = lean_ctor_get(x_6, 2);
lean_dec(x_27);
x_28 = lean_ctor_get(x_6, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_6, 0);
lean_dec(x_29);
lean_ctor_set_uint8(x_6, sizeof(void*)*6, x_22);
x_16 = x_6;
goto block_21;
}
else
{
lean_object* x_30; 
lean_dec(x_6);
x_30 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_8);
lean_ctor_set(x_30, 2, x_9);
lean_ctor_set(x_30, 3, x_10);
lean_ctor_set(x_30, 4, x_11);
lean_ctor_set(x_30, 5, x_13);
lean_ctor_set_uint8(x_30, sizeof(void*)*6, x_22);
lean_ctor_set_uint8(x_30, sizeof(void*)*6 + 1, x_12);
x_16 = x_30;
goto block_21;
}
}
block_21:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_array_uset(x_15, x_3, x_16);
x_3 = x_18;
x_4 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_markRecDecls_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_markRecDecls_spec__0___redArg(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markRecDecls(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_3 = l_Lean_NameSet_empty;
lean_inc_ref(x_2);
x_4 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_markRecDecls_go(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_array_size(x_2);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_markRecDecls_spec__0___redArg(x_5, x_6, x_7, x_2);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_markRecDecls___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Compiler_LCNF_markRecDecls(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_markRecDecls_spec__0(lean_object* x_1, uint8_t x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_markRecDecls_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_markRecDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_markRecDecls_spec__0(x_1, x_6, x_7, x_8, x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateRangeArgs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_5 == 0)
{
lean_dec_ref(x_4);
lean_inc_ref(x_1);
return x_1;
}
else
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_size(x_4);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LetValue_toExpr_spec__0___redArg(x_6, x_7, x_4);
x_9 = lean_expr_instantiate_range(x_1, x_2, x_3, x_8);
lean_dec_ref(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateRangeArgs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_instantiateRangeArgs___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateRangeArgs(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_instantiateRangeArgs___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateRangeArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_instantiateRangeArgs(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_5 == 0)
{
lean_dec_ref(x_4);
lean_inc_ref(x_1);
return x_1;
}
else
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_size(x_4);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_LetValue_toExpr_spec__0___redArg(x_6, x_7, x_4);
x_9 = lean_expr_instantiate_rev_range(x_1, x_2, x_3, x_8);
lean_dec_ref(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateRevRangeArgs(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_instantiateRevRangeArgs___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instantiateRevRangeArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_instantiateRevRangeArgs(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
lean_object* initialize_Lean_Meta_Instances(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Specialize(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Specialize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_instInhabitedPurity_default = _init_l_Lean_Compiler_LCNF_instInhabitedPurity_default();
l_Lean_Compiler_LCNF_instInhabitedPurity = _init_l_Lean_Compiler_LCNF_instInhabitedPurity();
l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__2 = _init_l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__2);
l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__3 = _init_l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedParam_default___closed__3);
l_Lean_Compiler_LCNF_LitValue_toExpr___closed__3 = _init_l_Lean_Compiler_LCNF_LitValue_toExpr___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_LitValue_toExpr___closed__3);
l_Lean_Compiler_LCNF_LitValue_toExpr___closed__6 = _init_l_Lean_Compiler_LCNF_LitValue_toExpr___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_LitValue_toExpr___closed__6);
l_Lean_Compiler_LCNF_LitValue_toExpr___closed__9 = _init_l_Lean_Compiler_LCNF_LitValue_toExpr___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_LitValue_toExpr___closed__9);
l_Lean_Compiler_LCNF_LitValue_toExpr___closed__12 = _init_l_Lean_Compiler_LCNF_LitValue_toExpr___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_LitValue_toExpr___closed__12);
l_Lean_Compiler_LCNF_LitValue_toExpr___closed__15 = _init_l_Lean_Compiler_LCNF_LitValue_toExpr___closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_LitValue_toExpr___closed__15);
l_Lean_Compiler_LCNF_Arg___auto__1___closed__0 = _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Arg___auto__1___closed__0);
l_Lean_Compiler_LCNF_Arg___auto__1___closed__1 = _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Arg___auto__1___closed__1);
l_Lean_Compiler_LCNF_Arg___auto__1___closed__2 = _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Arg___auto__1___closed__2);
l_Lean_Compiler_LCNF_Arg___auto__1___closed__3 = _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Arg___auto__1___closed__3);
l_Lean_Compiler_LCNF_Arg___auto__1___closed__4 = _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Arg___auto__1___closed__4);
l_Lean_Compiler_LCNF_Arg___auto__1___closed__5 = _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Arg___auto__1___closed__5);
l_Lean_Compiler_LCNF_Arg___auto__1___closed__6 = _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Arg___auto__1___closed__6);
l_Lean_Compiler_LCNF_Arg___auto__1___closed__7 = _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Arg___auto__1___closed__7);
l_Lean_Compiler_LCNF_Arg___auto__1___closed__8 = _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_Arg___auto__1___closed__8);
l_Lean_Compiler_LCNF_Arg___auto__1___closed__9 = _init_l_Lean_Compiler_LCNF_Arg___auto__1___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_Arg___auto__1___closed__9);
l_Lean_Compiler_LCNF_Arg___auto__1 = _init_l_Lean_Compiler_LCNF_Arg___auto__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Arg___auto__1);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__2 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp___closed__2);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg___closed__1 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp___redArg___closed__1);
l_Lean_Compiler_LCNF_LetValue___auto__1 = _init_l_Lean_Compiler_LCNF_LetValue___auto__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_LetValue___auto__1);
l_Lean_Compiler_LCNF_LetValue___auto__3 = _init_l_Lean_Compiler_LCNF_LetValue___auto__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_LetValue___auto__3);
l_Lean_Compiler_LCNF_Arg_toLetValue___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_Arg_toLetValue___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Arg_toLetValue___redArg___closed__0);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp___closed__1 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp___closed__1);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateConstImp___closed__1 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateConstImp___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateConstImp___closed__1);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___closed__1 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp___closed__1);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___closed__1 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp___closed__1);
l_Lean_Compiler_LCNF_Alt___auto__1 = _init_l_Lean_Compiler_LCNF_Alt___auto__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Alt___auto__1);
l_Lean_Compiler_LCNF_Alt___auto__3 = _init_l_Lean_Compiler_LCNF_Alt___auto__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Alt___auto__3);
l_Lean_Compiler_LCNF_instInhabitedCases_default__1___closed__0 = _init_l_Lean_Compiler_LCNF_instInhabitedCases_default__1___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedCases_default__1___closed__0);
l_Lean_Compiler_LCNF_instInhabitedCases_default__1___closed__1 = _init_l_Lean_Compiler_LCNF_instInhabitedCases_default__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedCases_default__1___closed__1);
l_Lean_Compiler_LCNF_instInhabitedCode_default__1___closed__0 = _init_l_Lean_Compiler_LCNF_instInhabitedCode_default__1___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedCode_default__1___closed__0);
l_Lean_Compiler_LCNF_instInhabitedCode_default__1___closed__1 = _init_l_Lean_Compiler_LCNF_instInhabitedCode_default__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedCode_default__1___closed__1);
l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1___closed__0 = _init_l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1___closed__0);
l_Lean_Compiler_LCNF_CodeDecl___auto__1 = _init_l_Lean_Compiler_LCNF_CodeDecl___auto__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_CodeDecl___auto__1);
l_Lean_Compiler_LCNF_Alt_getParams___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_Alt_getParams___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Alt_getParams___redArg___closed__0);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___closed__1 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp___closed__1);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp___closed__1 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp___closed__1);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp___closed__1 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateCasesImp___closed__1);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp___closed__1 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateLetImp___closed__1);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__1 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateContImp___closed__1);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp___closed__1 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateFunImp___closed__1);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp___closed__1 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateReturnImp___closed__1);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp___closed__1 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateJmpImp___closed__1);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp___closed__1 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateUnreachImp___closed__1);
l_Lean_Compiler_LCNF_Cases_extractAlt_x21___closed__2 = _init_l_Lean_Compiler_LCNF_Cases_extractAlt_x21___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Cases_extractAlt_x21___closed__2);
l_Lean_Compiler_LCNF_instInhabitedDecl_default___closed__0 = _init_l_Lean_Compiler_LCNF_instInhabitedDecl_default___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedDecl_default___closed__0);
l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___closed__1 = _init_l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
