// Lean compiler output
// Module: Init.Data.Rat.Basic
// Imports: public import Init.Data.Nat.Coprime public import Init.Data.OfScientific public import Init.Data.Int.DivMod.Basic public import Init.Data.String.Defs public import Init.Data.ToString.Macro public import Init.Data.ToString.Extra import Init.Data.Hashable import Init.Data.Int.DivMod.Bootstrap import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.Lemmas import Init.Data.Int.Order import Init.Data.Int.Pow import Init.Data.Nat.Dvd
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
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_div_exact(lean_object*, lean_object*);
lean_object* lean_nat_div_exact(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
static const lean_string_object l_Rat_den__nz___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Rat_den__nz___autoParam___closed__0 = (const lean_object*)&l_Rat_den__nz___autoParam___closed__0_value;
static const lean_string_object l_Rat_den__nz___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Rat_den__nz___autoParam___closed__1 = (const lean_object*)&l_Rat_den__nz___autoParam___closed__1_value;
static const lean_string_object l_Rat_den__nz___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Rat_den__nz___autoParam___closed__2 = (const lean_object*)&l_Rat_den__nz___autoParam___closed__2_value;
static const lean_string_object l_Rat_den__nz___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Rat_den__nz___autoParam___closed__3 = (const lean_object*)&l_Rat_den__nz___autoParam___closed__3_value;
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Rat_den__nz___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat_den__nz___autoParam___closed__4_value_aux_0),((lean_object*)&l_Rat_den__nz___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat_den__nz___autoParam___closed__4_value_aux_1),((lean_object*)&l_Rat_den__nz___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat_den__nz___autoParam___closed__4_value_aux_2),((lean_object*)&l_Rat_den__nz___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Rat_den__nz___autoParam___closed__4 = (const lean_object*)&l_Rat_den__nz___autoParam___closed__4_value;
static const lean_array_object l_Rat_den__nz___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Rat_den__nz___autoParam___closed__5 = (const lean_object*)&l_Rat_den__nz___autoParam___closed__5_value;
static const lean_string_object l_Rat_den__nz___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Rat_den__nz___autoParam___closed__6 = (const lean_object*)&l_Rat_den__nz___autoParam___closed__6_value;
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Rat_den__nz___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat_den__nz___autoParam___closed__7_value_aux_0),((lean_object*)&l_Rat_den__nz___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat_den__nz___autoParam___closed__7_value_aux_1),((lean_object*)&l_Rat_den__nz___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat_den__nz___autoParam___closed__7_value_aux_2),((lean_object*)&l_Rat_den__nz___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Rat_den__nz___autoParam___closed__7 = (const lean_object*)&l_Rat_den__nz___autoParam___closed__7_value;
static const lean_string_object l_Rat_den__nz___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Rat_den__nz___autoParam___closed__8 = (const lean_object*)&l_Rat_den__nz___autoParam___closed__8_value;
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Rat_den__nz___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Rat_den__nz___autoParam___closed__9 = (const lean_object*)&l_Rat_den__nz___autoParam___closed__9_value;
static const lean_string_object l_Rat_den__nz___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Rat_den__nz___autoParam___closed__10 = (const lean_object*)&l_Rat_den__nz___autoParam___closed__10_value;
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Rat_den__nz___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat_den__nz___autoParam___closed__11_value_aux_0),((lean_object*)&l_Rat_den__nz___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat_den__nz___autoParam___closed__11_value_aux_1),((lean_object*)&l_Rat_den__nz___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat_den__nz___autoParam___closed__11_value_aux_2),((lean_object*)&l_Rat_den__nz___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l_Rat_den__nz___autoParam___closed__11 = (const lean_object*)&l_Rat_den__nz___autoParam___closed__11_value;
static lean_once_cell_t l_Rat_den__nz___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Rat_den__nz___autoParam___closed__12;
static lean_once_cell_t l_Rat_den__nz___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Rat_den__nz___autoParam___closed__13;
static const lean_string_object l_Rat_den__nz___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Rat_den__nz___autoParam___closed__14 = (const lean_object*)&l_Rat_den__nz___autoParam___closed__14_value;
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Rat_den__nz___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat_den__nz___autoParam___closed__15_value_aux_0),((lean_object*)&l_Rat_den__nz___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat_den__nz___autoParam___closed__15_value_aux_1),((lean_object*)&l_Rat_den__nz___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat_den__nz___autoParam___closed__15_value_aux_2),((lean_object*)&l_Rat_den__nz___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Rat_den__nz___autoParam___closed__15 = (const lean_object*)&l_Rat_den__nz___autoParam___closed__15_value;
static const lean_ctor_object l_Rat_den__nz___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Rat_den__nz___autoParam___closed__9_value),((lean_object*)&l_Rat_den__nz___autoParam___closed__5_value)}};
static const lean_object* l_Rat_den__nz___autoParam___closed__16 = (const lean_object*)&l_Rat_den__nz___autoParam___closed__16_value;
static lean_once_cell_t l_Rat_den__nz___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Rat_den__nz___autoParam___closed__17;
static lean_once_cell_t l_Rat_den__nz___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Rat_den__nz___autoParam___closed__18;
static lean_once_cell_t l_Rat_den__nz___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Rat_den__nz___autoParam___closed__19;
static lean_once_cell_t l_Rat_den__nz___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Rat_den__nz___autoParam___closed__20;
static lean_once_cell_t l_Rat_den__nz___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Rat_den__nz___autoParam___closed__21;
static lean_once_cell_t l_Rat_den__nz___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Rat_den__nz___autoParam___closed__22;
static lean_once_cell_t l_Rat_den__nz___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Rat_den__nz___autoParam___closed__23;
static lean_once_cell_t l_Rat_den__nz___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Rat_den__nz___autoParam___closed__24;
static lean_once_cell_t l_Rat_den__nz___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Rat_den__nz___autoParam___closed__25;
static lean_once_cell_t l_Rat_den__nz___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Rat_den__nz___autoParam___closed__26;
LEAN_EXPORT lean_object* l_Rat_den__nz___autoParam;
LEAN_EXPORT lean_object* l_Rat_reduced___autoParam;
LEAN_EXPORT uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqRat_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqRat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqRat___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_instHashableRat_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instHashableRat_hash___closed__0;
LEAN_EXPORT uint64_t l_instHashableRat_hash(lean_object*);
LEAN_EXPORT lean_object* l_instHashableRat_hash___boxed(lean_object*);
static const lean_closure_object l_instHashableRat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableRat_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableRat___closed__0 = (const lean_object*)&l_instHashableRat___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableRat = (const lean_object*)&l_instHashableRat___closed__0_value;
static lean_once_cell_t l_instInhabitedRat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instInhabitedRat___closed__0;
LEAN_EXPORT lean_object* l_instInhabitedRat;
static const lean_string_object l_instToStringRat___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_instToStringRat___lam__0___closed__0 = (const lean_object*)&l_instToStringRat___lam__0___closed__0_value;
static const lean_string_object l_instToStringRat___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_instToStringRat___lam__0___closed__1 = (const lean_object*)&l_instToStringRat___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instToStringRat___lam__0(lean_object*);
static const lean_closure_object l_instToStringRat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringRat___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringRat___closed__0 = (const lean_object*)&l_instToStringRat___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringRat = (const lean_object*)&l_instToStringRat___closed__0_value;
static const lean_string_object l_instReprRat___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_instReprRat___lam__0___closed__0 = (const lean_object*)&l_instReprRat___lam__0___closed__0_value;
static const lean_string_object l_instReprRat___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " : Rat)/"};
static const lean_object* l_instReprRat___lam__0___closed__1 = (const lean_object*)&l_instReprRat___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instReprRat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprRat___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprRat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprRat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprRat___closed__0 = (const lean_object*)&l_instReprRat___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprRat = (const lean_object*)&l_instReprRat___closed__0_value;
LEAN_EXPORT lean_object* l_Rat_maybeNormalize___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_maybeNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_normalize___auto__1;
LEAN_EXPORT lean_object* l_Rat_normalize___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_normalize(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00mkRat_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_mkRat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Rat_instNatCast___lam__0(lean_object*);
static const lean_closure_object l_Rat_instNatCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_instNatCast___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Rat_instNatCast___closed__0 = (const lean_object*)&l_Rat_instNatCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Rat_instNatCast = (const lean_object*)&l_Rat_instNatCast___closed__0_value;
static const lean_closure_object l_Rat_instIntCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_ofInt, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Rat_instIntCast___closed__0 = (const lean_object*)&l_Rat_instIntCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Rat_instIntCast = (const lean_object*)&l_Rat_instIntCast___closed__0_value;
LEAN_EXPORT lean_object* l_Rat_instOfNat(lean_object*);
LEAN_EXPORT uint8_t l_Rat_isInt(lean_object*);
LEAN_EXPORT lean_object* l_Rat_isInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Rat_divInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_divInt___boxed(lean_object*, lean_object*);
static const lean_string_object l_Rat_term___x2f_x2e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rat"};
static const lean_object* l_Rat_term___x2f_x2e___00__closed__0 = (const lean_object*)&l_Rat_term___x2f_x2e___00__closed__0_value;
static const lean_string_object l_Rat_term___x2f_x2e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_/._"};
static const lean_object* l_Rat_term___x2f_x2e___00__closed__1 = (const lean_object*)&l_Rat_term___x2f_x2e___00__closed__1_value;
static const lean_ctor_object l_Rat_term___x2f_x2e___00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Rat_term___x2f_x2e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 55, 105, 214, 206, 30, 120, 51)}};
static const lean_ctor_object l_Rat_term___x2f_x2e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat_term___x2f_x2e___00__closed__2_value_aux_0),((lean_object*)&l_Rat_term___x2f_x2e___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(185, 2, 67, 148, 220, 156, 207, 35)}};
static const lean_object* l_Rat_term___x2f_x2e___00__closed__2 = (const lean_object*)&l_Rat_term___x2f_x2e___00__closed__2_value;
static const lean_string_object l_Rat_term___x2f_x2e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Rat_term___x2f_x2e___00__closed__3 = (const lean_object*)&l_Rat_term___x2f_x2e___00__closed__3_value;
static const lean_ctor_object l_Rat_term___x2f_x2e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Rat_term___x2f_x2e___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Rat_term___x2f_x2e___00__closed__4 = (const lean_object*)&l_Rat_term___x2f_x2e___00__closed__4_value;
static const lean_string_object l_Rat_term___x2f_x2e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " /. "};
static const lean_object* l_Rat_term___x2f_x2e___00__closed__5 = (const lean_object*)&l_Rat_term___x2f_x2e___00__closed__5_value;
static const lean_ctor_object l_Rat_term___x2f_x2e___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Rat_term___x2f_x2e___00__closed__5_value)}};
static const lean_object* l_Rat_term___x2f_x2e___00__closed__6 = (const lean_object*)&l_Rat_term___x2f_x2e___00__closed__6_value;
static const lean_string_object l_Rat_term___x2f_x2e___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Rat_term___x2f_x2e___00__closed__7 = (const lean_object*)&l_Rat_term___x2f_x2e___00__closed__7_value;
static const lean_ctor_object l_Rat_term___x2f_x2e___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Rat_term___x2f_x2e___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Rat_term___x2f_x2e___00__closed__8 = (const lean_object*)&l_Rat_term___x2f_x2e___00__closed__8_value;
static const lean_ctor_object l_Rat_term___x2f_x2e___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Rat_term___x2f_x2e___00__closed__8_value),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l_Rat_term___x2f_x2e___00__closed__9 = (const lean_object*)&l_Rat_term___x2f_x2e___00__closed__9_value;
static const lean_ctor_object l_Rat_term___x2f_x2e___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Rat_term___x2f_x2e___00__closed__4_value),((lean_object*)&l_Rat_term___x2f_x2e___00__closed__6_value),((lean_object*)&l_Rat_term___x2f_x2e___00__closed__9_value)}};
static const lean_object* l_Rat_term___x2f_x2e___00__closed__10 = (const lean_object*)&l_Rat_term___x2f_x2e___00__closed__10_value;
static const lean_ctor_object l_Rat_term___x2f_x2e___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Rat_term___x2f_x2e___00__closed__2_value),((lean_object*)(((size_t)(70) << 1) | 1)),((lean_object*)(((size_t)(70) << 1) | 1)),((lean_object*)&l_Rat_term___x2f_x2e___00__closed__10_value)}};
static const lean_object* l_Rat_term___x2f_x2e___00__closed__11 = (const lean_object*)&l_Rat_term___x2f_x2e___00__closed__11_value;
LEAN_EXPORT const lean_object* l_Rat_term___x2f_x2e__ = (const lean_object*)&l_Rat_term___x2f_x2e___00__closed__11_value;
static const lean_string_object l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__0 = (const lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__0_value;
static const lean_string_object l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__1 = (const lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__1_value;
static const lean_ctor_object l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Rat_den__nz___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2_value_aux_0),((lean_object*)&l_Rat_den__nz___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2_value_aux_1),((lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2_value_aux_2),((lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2 = (const lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2_value;
static const lean_string_object l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Rat.divInt"};
static const lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__3 = (const lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__3_value;
static lean_once_cell_t l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4;
static const lean_string_object l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "divInt"};
static const lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__5 = (const lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__5_value;
static const lean_ctor_object l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Rat_term___x2f_x2e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 55, 105, 214, 206, 30, 120, 51)}};
static const lean_ctor_object l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6_value_aux_0),((lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(173, 238, 192, 150, 219, 121, 176, 55)}};
static const lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6 = (const lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6_value;
static const lean_ctor_object l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__7 = (const lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__7_value;
static const lean_ctor_object l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6_value)}};
static const lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__8 = (const lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__8_value;
static const lean_ctor_object l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__9 = (const lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__9_value;
static const lean_ctor_object l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__7_value),((lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__9_value)}};
static const lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__10 = (const lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__10_value;
LEAN_EXPORT lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__0 = (const lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__0_value;
static const lean_ctor_object l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__1 = (const lean_object*)&l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__1_value;
LEAN_EXPORT lean_object* l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Rat_ofScientific_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Rat_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Rat_ofScientific___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Rat_instOfScientific___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_ofScientific___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Rat_instOfScientific___closed__0 = (const lean_object*)&l_Rat_instOfScientific___closed__0_value;
LEAN_EXPORT const lean_object* l_Rat_instOfScientific = (const lean_object*)&l_Rat_instOfScientific___closed__0_value;
LEAN_EXPORT uint8_t l_Rat_blt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_blt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_instLT;
LEAN_EXPORT uint8_t l_Rat_instDecidableLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_instDecidableLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_instLE;
LEAN_EXPORT uint8_t l_Rat_instDecidableLe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_instDecidableLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_instMin___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Rat_instMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_instMin___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Rat_instMin___closed__0 = (const lean_object*)&l_Rat_instMin___closed__0_value;
LEAN_EXPORT const lean_object* l_Rat_instMin = (const lean_object*)&l_Rat_instMin___closed__0_value;
LEAN_EXPORT lean_object* l_Rat_instMax___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Rat_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_instMax___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Rat_instMax___closed__0 = (const lean_object*)&l_Rat_instMax___closed__0_value;
LEAN_EXPORT const lean_object* l_Rat_instMax = (const lean_object*)&l_Rat_instMax___closed__0_value;
LEAN_EXPORT lean_object* l_Rat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_mul___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Rat_instMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Rat_instMul___closed__0 = (const lean_object*)&l_Rat_instMul___closed__0_value;
LEAN_EXPORT const lean_object* l_Rat_instMul = (const lean_object*)&l_Rat_instMul___closed__0_value;
LEAN_EXPORT lean_object* l_Rat_inv(lean_object*);
static const lean_closure_object l_Rat_instInv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_inv, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Rat_instInv___closed__0 = (const lean_object*)&l_Rat_instInv___closed__0_value;
LEAN_EXPORT const lean_object* l_Rat_instInv = (const lean_object*)&l_Rat_instInv___closed__0_value;
LEAN_EXPORT lean_object* l_Rat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_pow___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Rat_instPowNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Rat_instPowNat___closed__0 = (const lean_object*)&l_Rat_instPowNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Rat_instPowNat = (const lean_object*)&l_Rat_instPowNat___closed__0_value;
LEAN_EXPORT lean_object* l_Rat_zpow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_zpow___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Rat_instPowInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_zpow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Rat_instPowInt___closed__0 = (const lean_object*)&l_Rat_instPowInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Rat_instPowInt = (const lean_object*)&l_Rat_instPowInt___closed__0_value;
LEAN_EXPORT lean_object* l_Rat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_div___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Rat_instDiv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Rat_instDiv___closed__0 = (const lean_object*)&l_Rat_instDiv___closed__0_value;
LEAN_EXPORT const lean_object* l_Rat_instDiv = (const lean_object*)&l_Rat_instDiv___closed__0_value;
LEAN_EXPORT lean_object* l_Rat_add(lean_object*, lean_object*);
static const lean_closure_object l_Rat_instAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_add, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Rat_instAdd___closed__0 = (const lean_object*)&l_Rat_instAdd___closed__0_value;
LEAN_EXPORT const lean_object* l_Rat_instAdd = (const lean_object*)&l_Rat_instAdd___closed__0_value;
LEAN_EXPORT lean_object* l_Rat_neg(lean_object*);
static const lean_closure_object l_Rat_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_neg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Rat_instNeg___closed__0 = (const lean_object*)&l_Rat_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_Rat_instNeg = (const lean_object*)&l_Rat_instNeg___closed__0_value;
LEAN_EXPORT lean_object* l_Rat_sub(lean_object*, lean_object*);
static const lean_closure_object l_Rat_instSub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_sub, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Rat_instSub___closed__0 = (const lean_object*)&l_Rat_instSub___closed__0_value;
LEAN_EXPORT const lean_object* l_Rat_instSub = (const lean_object*)&l_Rat_instSub___closed__0_value;
LEAN_EXPORT lean_object* l_Rat_floor(lean_object*);
static lean_once_cell_t l_Rat_ceil___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Rat_ceil___closed__0;
LEAN_EXPORT lean_object* l_Rat_ceil(lean_object*);
static lean_once_cell_t l_Rat_abs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Rat_abs___closed__0;
LEAN_EXPORT lean_object* l_Rat_abs(lean_object*);
static lean_object* _init_l_Rat_den__nz___autoParam___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Rat_den__nz___autoParam___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Rat_den__nz___autoParam___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Rat_den__nz___autoParam___closed__12, &l_Rat_den__nz___autoParam___closed__12_once, _init_l_Rat_den__nz___autoParam___closed__12);
v___x_30_ = ((lean_object*)(l_Rat_den__nz___autoParam___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Rat_den__nz___autoParam___closed__17(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((lean_object*)(l_Rat_den__nz___autoParam___closed__16));
v___x_43_ = ((lean_object*)(l_Rat_den__nz___autoParam___closed__5));
v___x_44_ = lean_array_push(v___x_43_, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_l_Rat_den__nz___autoParam___closed__18(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_45_ = lean_obj_once(&l_Rat_den__nz___autoParam___closed__17, &l_Rat_den__nz___autoParam___closed__17_once, _init_l_Rat_den__nz___autoParam___closed__17);
v___x_46_ = ((lean_object*)(l_Rat_den__nz___autoParam___closed__15));
v___x_47_ = lean_box(2);
v___x_48_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
lean_ctor_set(v___x_48_, 2, v___x_45_);
return v___x_48_;
}
}
static lean_object* _init_l_Rat_den__nz___autoParam___closed__19(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l_Rat_den__nz___autoParam___closed__18, &l_Rat_den__nz___autoParam___closed__18_once, _init_l_Rat_den__nz___autoParam___closed__18);
v___x_50_ = lean_obj_once(&l_Rat_den__nz___autoParam___closed__13, &l_Rat_den__nz___autoParam___closed__13_once, _init_l_Rat_den__nz___autoParam___closed__13);
v___x_51_ = lean_array_push(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Rat_den__nz___autoParam___closed__20(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = lean_obj_once(&l_Rat_den__nz___autoParam___closed__19, &l_Rat_den__nz___autoParam___closed__19_once, _init_l_Rat_den__nz___autoParam___closed__19);
v___x_53_ = ((lean_object*)(l_Rat_den__nz___autoParam___closed__11));
v___x_54_ = lean_box(2);
v___x_55_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
lean_ctor_set(v___x_55_, 2, v___x_52_);
return v___x_55_;
}
}
static lean_object* _init_l_Rat_den__nz___autoParam___closed__21(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_obj_once(&l_Rat_den__nz___autoParam___closed__20, &l_Rat_den__nz___autoParam___closed__20_once, _init_l_Rat_den__nz___autoParam___closed__20);
v___x_57_ = ((lean_object*)(l_Rat_den__nz___autoParam___closed__5));
v___x_58_ = lean_array_push(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_l_Rat_den__nz___autoParam___closed__22(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = lean_obj_once(&l_Rat_den__nz___autoParam___closed__21, &l_Rat_den__nz___autoParam___closed__21_once, _init_l_Rat_den__nz___autoParam___closed__21);
v___x_60_ = ((lean_object*)(l_Rat_den__nz___autoParam___closed__9));
v___x_61_ = lean_box(2);
v___x_62_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
lean_ctor_set(v___x_62_, 2, v___x_59_);
return v___x_62_;
}
}
static lean_object* _init_l_Rat_den__nz___autoParam___closed__23(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_obj_once(&l_Rat_den__nz___autoParam___closed__22, &l_Rat_den__nz___autoParam___closed__22_once, _init_l_Rat_den__nz___autoParam___closed__22);
v___x_64_ = ((lean_object*)(l_Rat_den__nz___autoParam___closed__5));
v___x_65_ = lean_array_push(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Rat_den__nz___autoParam___closed__24(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_obj_once(&l_Rat_den__nz___autoParam___closed__23, &l_Rat_den__nz___autoParam___closed__23_once, _init_l_Rat_den__nz___autoParam___closed__23);
v___x_67_ = ((lean_object*)(l_Rat_den__nz___autoParam___closed__7));
v___x_68_ = lean_box(2);
v___x_69_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_66_);
return v___x_69_;
}
}
static lean_object* _init_l_Rat_den__nz___autoParam___closed__25(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_obj_once(&l_Rat_den__nz___autoParam___closed__24, &l_Rat_den__nz___autoParam___closed__24_once, _init_l_Rat_den__nz___autoParam___closed__24);
v___x_71_ = ((lean_object*)(l_Rat_den__nz___autoParam___closed__5));
v___x_72_ = lean_array_push(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Rat_den__nz___autoParam___closed__26(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = lean_obj_once(&l_Rat_den__nz___autoParam___closed__25, &l_Rat_den__nz___autoParam___closed__25_once, _init_l_Rat_den__nz___autoParam___closed__25);
v___x_74_ = ((lean_object*)(l_Rat_den__nz___autoParam___closed__4));
v___x_75_ = lean_box(2);
v___x_76_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
lean_ctor_set(v___x_76_, 2, v___x_73_);
return v___x_76_;
}
}
static lean_object* _init_l_Rat_den__nz___autoParam(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Rat_den__nz___autoParam___closed__26, &l_Rat_den__nz___autoParam___closed__26_once, _init_l_Rat_den__nz___autoParam___closed__26);
return v___x_77_;
}
}
static lean_object* _init_l_Rat_reduced___autoParam(void){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_obj_once(&l_Rat_den__nz___autoParam___closed__26, &l_Rat_den__nz___autoParam___closed__26_once, _init_l_Rat_den__nz___autoParam___closed__26);
return v___x_78_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqRat_decEq(lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
lean_object* v_num_81_; lean_object* v_den_82_; lean_object* v_num_83_; lean_object* v_den_84_; uint8_t v___x_85_; 
v_num_81_ = lean_ctor_get(v_x_79_, 0);
v_den_82_ = lean_ctor_get(v_x_79_, 1);
v_num_83_ = lean_ctor_get(v_x_80_, 0);
v_den_84_ = lean_ctor_get(v_x_80_, 1);
v___x_85_ = lean_int_dec_eq(v_num_81_, v_num_83_);
if (v___x_85_ == 0)
{
return v___x_85_;
}
else
{
uint8_t v___x_86_; 
v___x_86_ = lean_nat_dec_eq(v_den_82_, v_den_84_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_instDecidableEqRat_decEq___boxed(lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_instDecidableEqRat_decEq(v_x_87_, v_x_88_);
lean_dec_ref(v_x_88_);
lean_dec_ref(v_x_87_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqRat(lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = l_instDecidableEqRat_decEq(v_x_91_, v_x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqRat___boxed(lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
uint8_t v_res_96_; lean_object* v_r_97_; 
v_res_96_ = l_instDecidableEqRat(v_x_94_, v_x_95_);
lean_dec_ref(v_x_95_);
lean_dec_ref(v_x_94_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
static lean_object* _init_l_instHashableRat_hash___closed__0(void){
_start:
{
lean_object* v_natZero_98_; lean_object* v_intZero_99_; 
v_natZero_98_ = lean_unsigned_to_nat(0u);
v_intZero_99_ = lean_nat_to_int(v_natZero_98_);
return v_intZero_99_;
}
}
LEAN_EXPORT uint64_t l_instHashableRat_hash(lean_object* v_x_100_){
_start:
{
lean_object* v_num_101_; lean_object* v_den_102_; uint64_t v___x_103_; uint64_t v___y_105_; lean_object* v_intZero_111_; uint8_t v_isNeg_112_; 
v_num_101_ = lean_ctor_get(v_x_100_, 0);
v_den_102_ = lean_ctor_get(v_x_100_, 1);
v___x_103_ = 0ULL;
v_intZero_111_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v_isNeg_112_ = lean_int_dec_lt(v_num_101_, v_intZero_111_);
if (v_isNeg_112_ == 0)
{
lean_object* v_a_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint64_t v___x_116_; 
v_a_113_ = lean_nat_abs(v_num_101_);
v___x_114_ = lean_unsigned_to_nat(2u);
v___x_115_ = lean_nat_mul(v___x_114_, v_a_113_);
lean_dec(v_a_113_);
v___x_116_ = lean_uint64_of_nat(v___x_115_);
lean_dec(v___x_115_);
v___y_105_ = v___x_116_;
goto v___jp_104_;
}
else
{
lean_object* v_abs_117_; lean_object* v_one_118_; lean_object* v_a_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint64_t v___x_123_; 
v_abs_117_ = lean_nat_abs(v_num_101_);
v_one_118_ = lean_unsigned_to_nat(1u);
v_a_119_ = lean_nat_sub(v_abs_117_, v_one_118_);
lean_dec(v_abs_117_);
v___x_120_ = lean_unsigned_to_nat(2u);
v___x_121_ = lean_nat_mul(v___x_120_, v_a_119_);
lean_dec(v_a_119_);
v___x_122_ = lean_nat_add(v___x_121_, v_one_118_);
lean_dec(v___x_121_);
v___x_123_ = lean_uint64_of_nat(v___x_122_);
lean_dec(v___x_122_);
v___y_105_ = v___x_123_;
goto v___jp_104_;
}
v___jp_104_:
{
uint64_t v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; uint64_t v___x_109_; uint64_t v___x_110_; 
v___x_106_ = lean_uint64_mix_hash(v___x_103_, v___y_105_);
v___x_107_ = lean_uint64_of_nat(v_den_102_);
v___x_108_ = lean_uint64_mix_hash(v___x_106_, v___x_107_);
v___x_109_ = lean_uint64_mix_hash(v___x_108_, v___x_103_);
v___x_110_ = lean_uint64_mix_hash(v___x_109_, v___x_103_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l_instHashableRat_hash___boxed(lean_object* v_x_124_){
_start:
{
uint64_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l_instHashableRat_hash(v_x_124_);
lean_dec_ref(v_x_124_);
v_r_126_ = lean_box_uint64(v_res_125_);
return v_r_126_;
}
}
static lean_object* _init_l_instInhabitedRat___closed__0(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_129_);
return v___x_131_;
}
}
static lean_object* _init_l_instInhabitedRat(void){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&l_instInhabitedRat___closed__0, &l_instInhabitedRat___closed__0_once, _init_l_instInhabitedRat___closed__0);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_instToStringRat___lam__0(lean_object* v_a_135_){
_start:
{
lean_object* v_num_136_; lean_object* v_den_137_; lean_object* v___y_139_; lean_object* v___x_144_; uint8_t v___x_145_; 
v_num_136_ = lean_ctor_get(v_a_135_, 0);
lean_inc(v_num_136_);
v_den_137_ = lean_ctor_get(v_a_135_, 1);
lean_inc(v_den_137_);
lean_dec_ref(v_a_135_);
v___x_144_ = lean_unsigned_to_nat(1u);
v___x_145_ = lean_nat_dec_eq(v_den_137_, v___x_144_);
if (v___x_145_ == 0)
{
lean_object* v_intZero_146_; uint8_t v_isNeg_147_; 
v_intZero_146_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v_isNeg_147_ = lean_int_dec_lt(v_num_136_, v_intZero_146_);
if (v_isNeg_147_ == 0)
{
lean_object* v_a_148_; lean_object* v___x_149_; 
v_a_148_ = lean_nat_abs(v_num_136_);
lean_dec(v_num_136_);
v___x_149_ = l_Nat_reprFast(v_a_148_);
v___y_139_ = v___x_149_;
goto v___jp_138_;
}
else
{
lean_object* v_abs_150_; lean_object* v_a_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_abs_150_ = lean_nat_abs(v_num_136_);
lean_dec(v_num_136_);
v_a_151_ = lean_nat_sub(v_abs_150_, v___x_144_);
lean_dec(v_abs_150_);
v___x_152_ = ((lean_object*)(l_instToStringRat___lam__0___closed__1));
v___x_153_ = lean_nat_add(v_a_151_, v___x_144_);
lean_dec(v_a_151_);
v___x_154_ = l_Nat_reprFast(v___x_153_);
v___x_155_ = lean_string_append(v___x_152_, v___x_154_);
lean_dec_ref(v___x_154_);
v___y_139_ = v___x_155_;
goto v___jp_138_;
}
}
else
{
lean_object* v_intZero_156_; uint8_t v_isNeg_157_; 
lean_dec(v_den_137_);
v_intZero_156_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v_isNeg_157_ = lean_int_dec_lt(v_num_136_, v_intZero_156_);
if (v_isNeg_157_ == 0)
{
lean_object* v_a_158_; lean_object* v___x_159_; 
v_a_158_ = lean_nat_abs(v_num_136_);
lean_dec(v_num_136_);
v___x_159_ = l_Nat_reprFast(v_a_158_);
return v___x_159_;
}
else
{
lean_object* v_abs_160_; lean_object* v_a_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_abs_160_ = lean_nat_abs(v_num_136_);
lean_dec(v_num_136_);
v_a_161_ = lean_nat_sub(v_abs_160_, v___x_144_);
lean_dec(v_abs_160_);
v___x_162_ = ((lean_object*)(l_instToStringRat___lam__0___closed__1));
v___x_163_ = lean_nat_add(v_a_161_, v___x_144_);
lean_dec(v_a_161_);
v___x_164_ = l_Nat_reprFast(v___x_163_);
v___x_165_ = lean_string_append(v___x_162_, v___x_164_);
lean_dec_ref(v___x_164_);
return v___x_165_;
}
}
v___jp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_140_ = ((lean_object*)(l_instToStringRat___lam__0___closed__0));
v___x_141_ = lean_string_append(v___y_139_, v___x_140_);
v___x_142_ = l_Nat_reprFast(v_den_137_);
v___x_143_ = lean_string_append(v___x_141_, v___x_142_);
lean_dec_ref(v___x_142_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l_instReprRat___lam__0(lean_object* v_a_170_, lean_object* v_x_171_){
_start:
{
lean_object* v_num_172_; lean_object* v_den_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v_num_172_ = lean_ctor_get(v_a_170_, 0);
lean_inc(v_num_172_);
v_den_173_ = lean_ctor_get(v_a_170_, 1);
lean_inc(v_den_173_);
lean_dec_ref(v_a_170_);
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_dec_eq(v_den_173_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___y_178_; lean_object* v_intZero_185_; uint8_t v_isNeg_186_; 
v___x_176_ = ((lean_object*)(l_instReprRat___lam__0___closed__0));
v_intZero_185_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v_isNeg_186_ = lean_int_dec_lt(v_num_172_, v_intZero_185_);
if (v_isNeg_186_ == 0)
{
lean_object* v_a_187_; lean_object* v___x_188_; 
v_a_187_ = lean_nat_abs(v_num_172_);
lean_dec(v_num_172_);
v___x_188_ = l_Nat_reprFast(v_a_187_);
v___y_178_ = v___x_188_;
goto v___jp_177_;
}
else
{
lean_object* v_abs_189_; lean_object* v_a_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_abs_189_ = lean_nat_abs(v_num_172_);
lean_dec(v_num_172_);
v_a_190_ = lean_nat_sub(v_abs_189_, v___x_174_);
lean_dec(v_abs_189_);
v___x_191_ = ((lean_object*)(l_instToStringRat___lam__0___closed__1));
v___x_192_ = lean_nat_add(v_a_190_, v___x_174_);
lean_dec(v_a_190_);
v___x_193_ = l_Nat_reprFast(v___x_192_);
v___x_194_ = lean_string_append(v___x_191_, v___x_193_);
lean_dec_ref(v___x_193_);
v___y_178_ = v___x_194_;
goto v___jp_177_;
}
v___jp_177_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_179_ = lean_string_append(v___x_176_, v___y_178_);
lean_dec_ref(v___y_178_);
v___x_180_ = ((lean_object*)(l_instReprRat___lam__0___closed__1));
v___x_181_ = lean_string_append(v___x_179_, v___x_180_);
v___x_182_ = l_Nat_reprFast(v_den_173_);
v___x_183_ = lean_string_append(v___x_181_, v___x_182_);
lean_dec_ref(v___x_182_);
v___x_184_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
lean_dec(v_den_173_);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v___x_197_ = lean_int_dec_lt(v_num_172_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = l_Int_repr(v_num_172_);
lean_dec(v_num_172_);
v___x_199_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
return v___x_199_;
}
else
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = l_Int_repr(v_num_172_);
lean_dec(v_num_172_);
v___x_201_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
v___x_202_ = l_Repr_addAppParen(v___x_201_, v___x_195_);
return v___x_202_;
}
}
}
}
LEAN_EXPORT lean_object* l_instReprRat___lam__0___boxed(lean_object* v_a_203_, lean_object* v_x_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_instReprRat___lam__0(v_a_203_, v_x_204_);
lean_dec(v_x_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Rat_maybeNormalize___redArg(lean_object* v_num_208_, lean_object* v_den_209_, lean_object* v_g_210_){
_start:
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_dec_eq(v_g_210_, v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
lean_inc(v_g_210_);
v___x_213_ = lean_nat_to_int(v_g_210_);
v___x_214_ = lean_int_div_exact(v_num_208_, v___x_213_);
lean_dec(v___x_213_);
lean_dec(v_num_208_);
v___x_215_ = lean_nat_div_exact(v_den_209_, v_g_210_);
lean_dec(v_g_210_);
lean_dec(v_den_209_);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_214_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
return v___x_216_;
}
else
{
lean_object* v___x_217_; 
lean_dec(v_g_210_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v_num_208_);
lean_ctor_set(v___x_217_, 1, v_den_209_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_maybeNormalize(lean_object* v_num_218_, lean_object* v_den_219_, lean_object* v_g_220_, lean_object* v_dvd__num_221_, lean_object* v_dvd__den_222_, lean_object* v_den__nz_223_, lean_object* v_reduced_224_){
_start:
{
lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = lean_nat_dec_eq(v_g_220_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
lean_inc(v_g_220_);
v___x_227_ = lean_nat_to_int(v_g_220_);
v___x_228_ = lean_int_div_exact(v_num_218_, v___x_227_);
lean_dec(v___x_227_);
lean_dec(v_num_218_);
v___x_229_ = lean_nat_div_exact(v_den_219_, v_g_220_);
lean_dec(v_g_220_);
lean_dec(v_den_219_);
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
return v___x_230_;
}
else
{
lean_object* v___x_231_; 
lean_dec(v_g_220_);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v_num_218_);
lean_ctor_set(v___x_231_, 1, v_den_219_);
return v___x_231_;
}
}
}
static lean_object* _init_l_Rat_normalize___auto__1(void){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = lean_obj_once(&l_Rat_den__nz___autoParam___closed__26, &l_Rat_den__nz___autoParam___closed__26_once, _init_l_Rat_den__nz___autoParam___closed__26);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Rat_normalize___redArg(lean_object* v_num_233_, lean_object* v_den_234_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_235_ = lean_nat_abs(v_num_233_);
v___x_236_ = lean_nat_gcd(v___x_235_, v_den_234_);
lean_dec(v___x_235_);
v___x_237_ = lean_unsigned_to_nat(1u);
v___x_238_ = lean_nat_dec_eq(v___x_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
lean_inc(v___x_236_);
v___x_239_ = lean_nat_to_int(v___x_236_);
v___x_240_ = lean_int_div_exact(v_num_233_, v___x_239_);
lean_dec(v___x_239_);
lean_dec(v_num_233_);
v___x_241_ = lean_nat_div_exact(v_den_234_, v___x_236_);
lean_dec(v___x_236_);
lean_dec(v_den_234_);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
return v___x_242_;
}
else
{
lean_object* v___x_243_; 
lean_dec(v___x_236_);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v_num_233_);
lean_ctor_set(v___x_243_, 1, v_den_234_);
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_normalize(lean_object* v_num_244_, lean_object* v_den_245_, lean_object* v_den__nz_246_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_247_ = lean_nat_abs(v_num_244_);
v___x_248_ = lean_nat_gcd(v___x_247_, v_den_245_);
lean_dec(v___x_247_);
v___x_249_ = lean_unsigned_to_nat(1u);
v___x_250_ = lean_nat_dec_eq(v___x_248_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
lean_inc(v___x_248_);
v___x_251_ = lean_nat_to_int(v___x_248_);
v___x_252_ = lean_int_div_exact(v_num_244_, v___x_251_);
lean_dec(v___x_251_);
lean_dec(v_num_244_);
v___x_253_ = lean_nat_div_exact(v_den_245_, v___x_248_);
lean_dec(v___x_248_);
lean_dec(v_den_245_);
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; 
lean_dec(v___x_248_);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v_num_244_);
lean_ctor_set(v___x_255_, 1, v_den_245_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00mkRat_spec__0(lean_object* v_a_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_nat_to_int(v_a_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_mkRat(lean_object* v_num_258_, lean_object* v_den_259_){
_start:
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_nat_dec_eq(v_den_259_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_262_ = lean_nat_abs(v_num_258_);
v___x_263_ = lean_nat_gcd(v___x_262_, v_den_259_);
lean_dec(v___x_262_);
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = lean_nat_dec_eq(v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
lean_inc(v___x_263_);
v___x_266_ = lean_nat_to_int(v___x_263_);
v___x_267_ = lean_int_div_exact(v_num_258_, v___x_266_);
lean_dec(v___x_266_);
lean_dec(v_num_258_);
v___x_268_ = lean_nat_div_exact(v_den_259_, v___x_263_);
lean_dec(v___x_263_);
lean_dec(v_den_259_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
return v___x_269_;
}
else
{
lean_object* v___x_270_; 
lean_dec(v___x_263_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v_num_258_);
lean_ctor_set(v___x_270_, 1, v_den_259_);
return v___x_270_;
}
}
else
{
lean_object* v___x_271_; 
lean_dec(v_den_259_);
lean_dec(v_num_258_);
v___x_271_ = lean_obj_once(&l_instInhabitedRat___closed__0, &l_instInhabitedRat___closed__0_once, _init_l_instInhabitedRat___closed__0);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_ofInt(lean_object* v_num_272_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v_num_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Rat_instNatCast___lam__0(lean_object* v_n_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_nat_to_int(v_n_275_);
v___x_277_ = l_Rat_ofInt(v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Rat_instOfNat(lean_object* v_n_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Rat_instNatCast___lam__0(v_n_282_);
return v___x_283_;
}
}
LEAN_EXPORT uint8_t l_Rat_isInt(lean_object* v_a_284_){
_start:
{
lean_object* v_den_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v_den_285_ = lean_ctor_get(v_a_284_, 1);
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_dec_eq(v_den_285_, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Rat_isInt___boxed(lean_object* v_a_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Rat_isInt(v_a_288_);
lean_dec_ref(v_a_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT lean_object* l_Rat_divInt(lean_object* v_x_291_, lean_object* v_x_292_){
_start:
{
lean_object* v_natZero_293_; lean_object* v_intZero_294_; uint8_t v_isNeg_295_; 
v_natZero_293_ = lean_unsigned_to_nat(0u);
v_intZero_294_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v_isNeg_295_ = lean_int_dec_lt(v_x_292_, v_intZero_294_);
if (v_isNeg_295_ == 0)
{
lean_object* v_a_296_; uint8_t v___x_297_; 
v_a_296_ = lean_nat_abs(v_x_292_);
v___x_297_ = lean_nat_dec_eq(v_a_296_, v_natZero_293_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_298_ = lean_nat_abs(v_x_291_);
v___x_299_ = lean_nat_gcd(v___x_298_, v_a_296_);
lean_dec(v___x_298_);
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = lean_nat_dec_eq(v___x_299_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
lean_inc(v___x_299_);
v___x_302_ = lean_nat_to_int(v___x_299_);
v___x_303_ = lean_int_div_exact(v_x_291_, v___x_302_);
lean_dec(v___x_302_);
lean_dec(v_x_291_);
v___x_304_ = lean_nat_div_exact(v_a_296_, v___x_299_);
lean_dec(v___x_299_);
lean_dec(v_a_296_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
return v___x_305_;
}
else
{
lean_object* v___x_306_; 
lean_dec(v___x_299_);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v_x_291_);
lean_ctor_set(v___x_306_, 1, v_a_296_);
return v___x_306_;
}
}
else
{
lean_object* v___x_307_; 
lean_dec(v_a_296_);
lean_dec(v_x_291_);
v___x_307_ = lean_obj_once(&l_instInhabitedRat___closed__0, &l_instInhabitedRat___closed__0_once, _init_l_instInhabitedRat___closed__0);
return v___x_307_;
}
}
else
{
lean_object* v_abs_308_; lean_object* v_one_309_; lean_object* v_a_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_abs_308_ = lean_nat_abs(v_x_292_);
v_one_309_ = lean_unsigned_to_nat(1u);
v_a_310_ = lean_nat_sub(v_abs_308_, v_one_309_);
lean_dec(v_abs_308_);
v___x_311_ = lean_int_neg(v_x_291_);
lean_dec(v_x_291_);
v___x_312_ = lean_nat_add(v_a_310_, v_one_309_);
lean_dec(v_a_310_);
v___x_313_ = lean_nat_abs(v___x_311_);
v___x_314_ = lean_nat_gcd(v___x_313_, v___x_312_);
lean_dec(v___x_313_);
v___x_315_ = lean_nat_dec_eq(v___x_314_, v_one_309_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_inc(v___x_314_);
v___x_316_ = lean_nat_to_int(v___x_314_);
v___x_317_ = lean_int_div_exact(v___x_311_, v___x_316_);
lean_dec(v___x_316_);
lean_dec(v___x_311_);
v___x_318_ = lean_nat_div_exact(v___x_312_, v___x_314_);
lean_dec(v___x_314_);
lean_dec(v___x_312_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
return v___x_319_;
}
else
{
lean_object* v___x_320_; 
lean_dec(v___x_314_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_311_);
lean_ctor_set(v___x_320_, 1, v___x_312_);
return v___x_320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_divInt___boxed(lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Rat_divInt(v_x_321_, v_x_322_);
lean_dec(v_x_322_);
return v_res_323_;
}
}
static lean_object* _init_l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__3));
v___x_359_ = l_String_toRawSubstring_x27(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1(lean_object* v_x_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = ((lean_object*)(l_Rat_term___x2f_x2e___00__closed__2));
lean_inc(v_x_375_);
v___x_379_ = l_Lean_Syntax_isOfKind(v_x_375_, v___x_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec_ref(v_a_376_);
lean_dec(v_x_375_);
v___x_380_ = lean_box(1);
v___x_381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v_a_377_);
return v___x_381_;
}
else
{
lean_object* v_quotContext_382_; lean_object* v_currMacroScope_383_; lean_object* v_ref_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_quotContext_382_ = lean_ctor_get(v_a_376_, 1);
lean_inc(v_quotContext_382_);
v_currMacroScope_383_ = lean_ctor_get(v_a_376_, 2);
lean_inc(v_currMacroScope_383_);
v_ref_384_ = lean_ctor_get(v_a_376_, 5);
lean_inc(v_ref_384_);
lean_dec_ref(v_a_376_);
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = l_Lean_Syntax_getArg(v_x_375_, v___x_385_);
v___x_387_ = lean_unsigned_to_nat(2u);
v___x_388_ = l_Lean_Syntax_getArg(v_x_375_, v___x_387_);
lean_dec(v_x_375_);
v___x_389_ = 0;
v___x_390_ = l_Lean_SourceInfo_fromRef(v_ref_384_, v___x_389_);
lean_dec(v_ref_384_);
v___x_391_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2));
v___x_392_ = lean_obj_once(&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4, &l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4_once, _init_l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4);
v___x_393_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6));
v___x_394_ = l_Lean_addMacroScope(v_quotContext_382_, v___x_393_, v_currMacroScope_383_);
v___x_395_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__10));
lean_inc(v___x_390_);
v___x_396_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_396_, 0, v___x_390_);
lean_ctor_set(v___x_396_, 1, v___x_392_);
lean_ctor_set(v___x_396_, 2, v___x_394_);
lean_ctor_set(v___x_396_, 3, v___x_395_);
v___x_397_ = ((lean_object*)(l_Rat_den__nz___autoParam___closed__9));
lean_inc(v___x_390_);
v___x_398_ = l_Lean_Syntax_node2(v___x_390_, v___x_397_, v___x_386_, v___x_388_);
v___x_399_ = l_Lean_Syntax_node2(v___x_390_, v___x_391_, v___x_396_, v___x_398_);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v_a_377_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1(lean_object* v_x_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2));
lean_inc(v_x_404_);
v___x_408_ = l_Lean_Syntax_isOfKind(v_x_404_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec(v_x_404_);
v___x_409_ = lean_box(0);
v___x_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v_a_406_);
return v___x_410_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = l_Lean_Syntax_getArg(v_x_404_, v___x_411_);
v___x_413_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__1));
lean_inc(v___x_412_);
v___x_414_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; 
lean_dec(v___x_412_);
lean_dec(v_x_404_);
v___x_415_ = lean_box(0);
v___x_416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v_a_406_);
return v___x_416_;
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_417_ = lean_unsigned_to_nat(1u);
v___x_418_ = l_Lean_Syntax_getArg(v_x_404_, v___x_417_);
lean_dec(v_x_404_);
v___x_419_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_418_);
v___x_420_ = l_Lean_Syntax_matchesNull(v___x_418_, v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec(v___x_418_);
lean_dec(v___x_412_);
v___x_421_ = lean_box(0);
v___x_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v_a_406_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v_ref_425_; uint8_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_423_ = l_Lean_Syntax_getArg(v___x_418_, v___x_411_);
v___x_424_ = l_Lean_Syntax_getArg(v___x_418_, v___x_417_);
lean_dec(v___x_418_);
v_ref_425_ = l_Lean_replaceRef(v___x_412_, v_a_405_);
lean_dec(v___x_412_);
v___x_426_ = 0;
v___x_427_ = l_Lean_SourceInfo_fromRef(v_ref_425_, v___x_426_);
lean_dec(v_ref_425_);
v___x_428_ = ((lean_object*)(l_Rat_term___x2f_x2e___00__closed__2));
v___x_429_ = ((lean_object*)(l_Rat_term___x2f_x2e___00__closed__5));
lean_inc(v___x_427_);
v___x_430_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_427_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = l_Lean_Syntax_node3(v___x_427_, v___x_428_, v___x_423_, v___x_430_, v___x_424_);
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v_a_406_);
return v___x_432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___boxed(lean_object* v_x_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1(v_x_433_, v_a_434_, v_a_435_);
lean_dec(v_a_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Rat_ofScientific_spec__0(lean_object* v_a_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_nat_to_int(v_a_437_);
v___x_439_ = l_Rat_ofInt(v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Rat_ofScientific(lean_object* v_m_440_, uint8_t v_s_441_, lean_object* v_e_442_){
_start:
{
if (v_s_441_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_443_ = lean_unsigned_to_nat(10u);
v___x_444_ = lean_nat_pow(v___x_443_, v_e_442_);
v___x_445_ = lean_nat_mul(v_m_440_, v___x_444_);
lean_dec(v___x_444_);
lean_dec(v_m_440_);
v___x_446_ = l_Nat_cast___at___00Rat_ofScientific_spec__0(v___x_445_);
return v___x_446_;
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_447_ = lean_nat_to_int(v_m_440_);
v___x_448_ = lean_unsigned_to_nat(10u);
v___x_449_ = lean_nat_pow(v___x_448_, v_e_442_);
v___x_450_ = lean_nat_abs(v___x_447_);
v___x_451_ = lean_nat_gcd(v___x_450_, v___x_449_);
lean_dec(v___x_450_);
v___x_452_ = lean_unsigned_to_nat(1u);
v___x_453_ = lean_nat_dec_eq(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
lean_inc(v___x_451_);
v___x_454_ = lean_nat_to_int(v___x_451_);
v___x_455_ = lean_int_div_exact(v___x_447_, v___x_454_);
lean_dec(v___x_454_);
lean_dec(v___x_447_);
v___x_456_ = lean_nat_div_exact(v___x_449_, v___x_451_);
lean_dec(v___x_451_);
lean_dec(v___x_449_);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
return v___x_457_;
}
else
{
lean_object* v___x_458_; 
lean_dec(v___x_451_);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_447_);
lean_ctor_set(v___x_458_, 1, v___x_449_);
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_ofScientific___boxed(lean_object* v_m_459_, lean_object* v_s_460_, lean_object* v_e_461_){
_start:
{
uint8_t v_s_boxed_462_; lean_object* v_res_463_; 
v_s_boxed_462_ = lean_unbox(v_s_460_);
v_res_463_ = l_Rat_ofScientific(v_m_459_, v_s_boxed_462_, v_e_461_);
lean_dec(v_e_461_);
return v_res_463_;
}
}
LEAN_EXPORT uint8_t l_Rat_blt(lean_object* v_a_466_, lean_object* v_b_467_){
_start:
{
lean_object* v_num_468_; lean_object* v_den_469_; uint8_t v___y_471_; uint8_t v___y_472_; lean_object* v___x_480_; uint8_t v___y_482_; uint8_t v___x_489_; 
v_num_468_ = lean_ctor_get(v_a_466_, 0);
lean_inc(v_num_468_);
v_den_469_ = lean_ctor_get(v_a_466_, 1);
lean_inc(v_den_469_);
lean_dec_ref(v_a_466_);
v___x_480_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v___x_489_ = lean_int_dec_lt(v_num_468_, v___x_480_);
if (v___x_489_ == 0)
{
v___y_482_ = v___x_489_;
goto v___jp_481_;
}
else
{
lean_object* v_num_490_; uint8_t v___x_491_; 
v_num_490_ = lean_ctor_get(v_b_467_, 0);
v___x_491_ = lean_int_dec_le(v___x_480_, v_num_490_);
v___y_482_ = v___x_491_;
goto v___jp_481_;
}
v___jp_470_:
{
if (v___y_472_ == 0)
{
lean_object* v_num_473_; lean_object* v_den_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v_num_473_ = lean_ctor_get(v_b_467_, 0);
lean_inc(v_num_473_);
v_den_474_ = lean_ctor_get(v_b_467_, 1);
lean_inc(v_den_474_);
lean_dec_ref(v_b_467_);
v___x_475_ = lean_nat_to_int(v_den_474_);
v___x_476_ = lean_int_mul(v_num_468_, v___x_475_);
lean_dec(v___x_475_);
lean_dec(v_num_468_);
v___x_477_ = lean_nat_to_int(v_den_469_);
v___x_478_ = lean_int_mul(v_num_473_, v___x_477_);
lean_dec(v___x_477_);
lean_dec(v_num_473_);
v___x_479_ = lean_int_dec_lt(v___x_476_, v___x_478_);
lean_dec(v___x_478_);
lean_dec(v___x_476_);
return v___x_479_;
}
else
{
lean_dec(v_den_469_);
lean_dec(v_num_468_);
lean_dec_ref(v_b_467_);
return v___y_471_;
}
}
v___jp_481_:
{
if (v___y_482_ == 0)
{
uint8_t v___x_483_; 
v___x_483_ = lean_int_dec_eq(v_num_468_, v___x_480_);
if (v___x_483_ == 0)
{
uint8_t v___x_484_; 
v___x_484_ = lean_int_dec_lt(v___x_480_, v_num_468_);
if (v___x_484_ == 0)
{
v___y_471_ = v___y_482_;
v___y_472_ = v___x_484_;
goto v___jp_470_;
}
else
{
lean_object* v_num_485_; uint8_t v___x_486_; 
v_num_485_ = lean_ctor_get(v_b_467_, 0);
v___x_486_ = lean_int_dec_le(v_num_485_, v___x_480_);
v___y_471_ = v___y_482_;
v___y_472_ = v___x_486_;
goto v___jp_470_;
}
}
else
{
lean_object* v_num_487_; uint8_t v___x_488_; 
lean_dec(v_den_469_);
lean_dec(v_num_468_);
v_num_487_ = lean_ctor_get(v_b_467_, 0);
lean_inc(v_num_487_);
lean_dec_ref(v_b_467_);
v___x_488_ = lean_int_dec_lt(v___x_480_, v_num_487_);
lean_dec(v_num_487_);
return v___x_488_;
}
}
else
{
lean_dec(v_den_469_);
lean_dec(v_num_468_);
lean_dec_ref(v_b_467_);
return v___y_482_;
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_blt___boxed(lean_object* v_a_492_, lean_object* v_b_493_){
_start:
{
uint8_t v_res_494_; lean_object* v_r_495_; 
v_res_494_ = l_Rat_blt(v_a_492_, v_b_493_);
v_r_495_ = lean_box(v_res_494_);
return v_r_495_;
}
}
static lean_object* _init_l_Rat_instLT(void){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = lean_box(0);
return v___x_496_;
}
}
LEAN_EXPORT uint8_t l_Rat_instDecidableLt(lean_object* v_a_497_, lean_object* v_b_498_){
_start:
{
uint8_t v___x_499_; 
v___x_499_ = l_Rat_blt(v_a_497_, v_b_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Rat_instDecidableLt___boxed(lean_object* v_a_500_, lean_object* v_b_501_){
_start:
{
uint8_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = l_Rat_instDecidableLt(v_a_500_, v_b_501_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
static lean_object* _init_l_Rat_instLE(void){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = lean_box(0);
return v___x_504_;
}
}
LEAN_EXPORT uint8_t l_Rat_instDecidableLe(lean_object* v_a_505_, lean_object* v_b_506_){
_start:
{
uint8_t v___x_507_; 
v___x_507_ = l_Rat_blt(v_b_506_, v_a_505_);
if (v___x_507_ == 0)
{
uint8_t v___x_508_; 
v___x_508_ = 1;
return v___x_508_;
}
else
{
uint8_t v___x_509_; 
v___x_509_ = 0;
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_instDecidableLe___boxed(lean_object* v_a_510_, lean_object* v_b_511_){
_start:
{
uint8_t v_res_512_; lean_object* v_r_513_; 
v_res_512_ = l_Rat_instDecidableLe(v_a_510_, v_b_511_);
v_r_513_ = lean_box(v_res_512_);
return v_r_513_;
}
}
LEAN_EXPORT lean_object* l_Rat_instMin___lam__0(lean_object* v_x_514_, lean_object* v_y_515_){
_start:
{
uint8_t v___x_516_; 
lean_inc_ref(v_y_515_);
lean_inc_ref(v_x_514_);
v___x_516_ = l_Rat_instDecidableLe(v_x_514_, v_y_515_);
if (v___x_516_ == 0)
{
lean_dec_ref(v_x_514_);
return v_y_515_;
}
else
{
lean_dec_ref(v_y_515_);
return v_x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_instMax___lam__0(lean_object* v_x_519_, lean_object* v_y_520_){
_start:
{
uint8_t v___x_521_; 
lean_inc_ref(v_y_520_);
lean_inc_ref(v_x_519_);
v___x_521_ = l_Rat_instDecidableLe(v_x_519_, v_y_520_);
if (v___x_521_ == 0)
{
lean_dec_ref(v_y_520_);
return v_x_519_;
}
else
{
lean_dec_ref(v_x_519_);
return v_y_520_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_mul(lean_object* v_a_524_, lean_object* v_b_525_){
_start:
{
lean_object* v_num_526_; lean_object* v_den_527_; lean_object* v_num_528_; lean_object* v_den_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_548_; 
v_num_526_ = lean_ctor_get(v_a_524_, 0);
v_den_527_ = lean_ctor_get(v_a_524_, 1);
v_num_528_ = lean_ctor_get(v_b_525_, 0);
v_den_529_ = lean_ctor_get(v_b_525_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v_b_525_);
if (v_isSharedCheck_548_ == 0)
{
v___x_531_ = v_b_525_;
v_isShared_532_ = v_isSharedCheck_548_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_den_529_);
lean_inc(v_num_528_);
lean_dec(v_b_525_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_548_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v_g1_534_; lean_object* v___x_535_; lean_object* v_g2_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_533_ = lean_nat_abs(v_num_526_);
v_g1_534_ = lean_nat_gcd(v___x_533_, v_den_529_);
lean_dec(v___x_533_);
v___x_535_ = lean_nat_abs(v_num_528_);
v_g2_536_ = lean_nat_gcd(v___x_535_, v_den_527_);
lean_dec(v___x_535_);
lean_inc(v_g1_534_);
v___x_537_ = lean_nat_to_int(v_g1_534_);
v___x_538_ = lean_int_div_exact(v_num_526_, v___x_537_);
lean_dec(v___x_537_);
lean_inc(v_g2_536_);
v___x_539_ = lean_nat_to_int(v_g2_536_);
v___x_540_ = lean_int_div_exact(v_num_528_, v___x_539_);
lean_dec(v___x_539_);
lean_dec(v_num_528_);
v___x_541_ = lean_int_mul(v___x_538_, v___x_540_);
lean_dec(v___x_540_);
lean_dec(v___x_538_);
v___x_542_ = lean_nat_div_exact(v_den_527_, v_g2_536_);
lean_dec(v_g2_536_);
v___x_543_ = lean_nat_div_exact(v_den_529_, v_g1_534_);
lean_dec(v_g1_534_);
lean_dec(v_den_529_);
v___x_544_ = lean_nat_mul(v___x_542_, v___x_543_);
lean_dec(v___x_543_);
lean_dec(v___x_542_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 1, v___x_544_);
lean_ctor_set(v___x_531_, 0, v___x_541_);
v___x_546_ = v___x_531_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_mul___boxed(lean_object* v_a_549_, lean_object* v_b_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Rat_mul(v_a_549_, v_b_550_);
lean_dec_ref(v_a_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Rat_inv(lean_object* v_a_554_){
_start:
{
lean_object* v_num_555_; lean_object* v_den_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_num_555_ = lean_ctor_get(v_a_554_, 0);
v_den_556_ = lean_ctor_get(v_a_554_, 1);
v___x_557_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v___x_558_ = lean_int_dec_lt(v_num_555_, v___x_557_);
if (v___x_558_ == 0)
{
uint8_t v___x_559_; 
v___x_559_ = lean_int_dec_lt(v___x_557_, v_num_555_);
if (v___x_559_ == 0)
{
return v_a_554_;
}
else
{
lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_568_; 
lean_inc(v_den_556_);
lean_inc(v_num_555_);
v_isSharedCheck_568_ = !lean_is_exclusive(v_a_554_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; lean_object* v_unused_570_; 
v_unused_569_ = lean_ctor_get(v_a_554_, 1);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v_a_554_, 0);
lean_dec(v_unused_570_);
v___x_561_ = v_a_554_;
v_isShared_562_ = v_isSharedCheck_568_;
goto v_resetjp_560_;
}
else
{
lean_dec(v_a_554_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_568_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_563_ = lean_nat_to_int(v_den_556_);
v___x_564_ = lean_nat_abs(v_num_555_);
lean_dec(v_num_555_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 1, v___x_564_);
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_566_ = v___x_561_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v___x_564_);
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
else
{
lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_580_; 
lean_inc(v_den_556_);
lean_inc(v_num_555_);
v_isSharedCheck_580_ = !lean_is_exclusive(v_a_554_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; lean_object* v_unused_582_; 
v_unused_581_ = lean_ctor_get(v_a_554_, 1);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_a_554_, 0);
lean_dec(v_unused_582_);
v___x_572_ = v_a_554_;
v_isShared_573_ = v_isSharedCheck_580_;
goto v_resetjp_571_;
}
else
{
lean_dec(v_a_554_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_580_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_574_ = lean_nat_to_int(v_den_556_);
v___x_575_ = lean_int_neg(v___x_574_);
lean_dec(v___x_574_);
v___x_576_ = lean_nat_abs(v_num_555_);
lean_dec(v_num_555_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 1, v___x_576_);
lean_ctor_set(v___x_572_, 0, v___x_575_);
v___x_578_ = v___x_572_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_pow(lean_object* v_q_585_, lean_object* v_n_586_){
_start:
{
lean_object* v_num_587_; lean_object* v_den_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_597_; 
v_num_587_ = lean_ctor_get(v_q_585_, 0);
v_den_588_ = lean_ctor_get(v_q_585_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v_q_585_);
if (v_isSharedCheck_597_ == 0)
{
v___x_590_ = v_q_585_;
v_isShared_591_ = v_isSharedCheck_597_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_den_588_);
lean_inc(v_num_587_);
lean_dec(v_q_585_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_597_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_592_ = l_Int_pow(v_num_587_, v_n_586_);
lean_dec(v_num_587_);
v___x_593_ = lean_nat_pow(v_den_588_, v_n_586_);
lean_dec(v_den_588_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v___x_593_);
lean_ctor_set(v___x_590_, 0, v___x_592_);
v___x_595_ = v___x_590_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v___x_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_pow___boxed(lean_object* v_q_598_, lean_object* v_n_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Rat_pow(v_q_598_, v_n_599_);
lean_dec(v_n_599_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Rat_zpow(lean_object* v_q_603_, lean_object* v_i_604_){
_start:
{
lean_object* v_intZero_605_; uint8_t v_isNeg_606_; 
v_intZero_605_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v_isNeg_606_ = lean_int_dec_lt(v_i_604_, v_intZero_605_);
if (v_isNeg_606_ == 0)
{
lean_object* v_a_607_; lean_object* v___x_608_; 
v_a_607_ = lean_nat_abs(v_i_604_);
v___x_608_ = l_Rat_pow(v_q_603_, v_a_607_);
lean_dec(v_a_607_);
return v___x_608_;
}
else
{
lean_object* v_abs_609_; lean_object* v_one_610_; lean_object* v_a_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_abs_609_ = lean_nat_abs(v_i_604_);
v_one_610_ = lean_unsigned_to_nat(1u);
v_a_611_ = lean_nat_sub(v_abs_609_, v_one_610_);
lean_dec(v_abs_609_);
v___x_612_ = lean_nat_add(v_a_611_, v_one_610_);
lean_dec(v_a_611_);
v___x_613_ = l_Rat_pow(v_q_603_, v___x_612_);
lean_dec(v___x_612_);
v___x_614_ = l_Rat_inv(v___x_613_);
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_zpow___boxed(lean_object* v_q_615_, lean_object* v_i_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Rat_zpow(v_q_615_, v_i_616_);
lean_dec(v_i_616_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Rat_div(lean_object* v_x1_620_, lean_object* v_x2_621_){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = l_Rat_inv(v_x2_621_);
v___x_623_ = l_Rat_mul(v_x1_620_, v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Rat_div___boxed(lean_object* v_x1_624_, lean_object* v_x2_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Rat_div(v_x1_624_, v_x2_625_);
lean_dec_ref(v_x1_624_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Rat_add(lean_object* v_a_629_, lean_object* v_b_630_){
_start:
{
lean_object* v_num_631_; lean_object* v_den_632_; lean_object* v_num_633_; lean_object* v_den_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_670_; 
v_num_631_ = lean_ctor_get(v_a_629_, 0);
lean_inc(v_num_631_);
v_den_632_ = lean_ctor_get(v_a_629_, 1);
lean_inc(v_den_632_);
lean_dec_ref(v_a_629_);
v_num_633_ = lean_ctor_get(v_b_630_, 0);
v_den_634_ = lean_ctor_get(v_b_630_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_b_630_);
if (v_isSharedCheck_670_ == 0)
{
v___x_636_ = v_b_630_;
v_isShared_637_ = v_isSharedCheck_670_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_den_634_);
lean_inc(v_num_633_);
lean_dec(v_b_630_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_670_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_638_ = lean_nat_gcd(v_den_632_, v_den_634_);
v___x_639_ = lean_unsigned_to_nat(1u);
v___x_640_ = lean_nat_dec_eq(v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v_den_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_num_648_; lean_object* v___x_649_; lean_object* v_g1_650_; uint8_t v___x_651_; 
v___x_641_ = lean_nat_div(v_den_632_, v___x_638_);
lean_dec(v_den_632_);
v_den_642_ = lean_nat_mul(v___x_641_, v_den_634_);
v___x_643_ = lean_nat_div(v_den_634_, v___x_638_);
lean_dec(v_den_634_);
v___x_644_ = lean_nat_to_int(v___x_643_);
v___x_645_ = lean_int_mul(v_num_631_, v___x_644_);
lean_dec(v___x_644_);
lean_dec(v_num_631_);
v___x_646_ = lean_nat_to_int(v___x_641_);
v___x_647_ = lean_int_mul(v_num_633_, v___x_646_);
lean_dec(v___x_646_);
lean_dec(v_num_633_);
v_num_648_ = lean_int_add(v___x_645_, v___x_647_);
lean_dec(v___x_647_);
lean_dec(v___x_645_);
v___x_649_ = lean_nat_abs(v_num_648_);
v_g1_650_ = lean_nat_gcd(v___x_649_, v___x_638_);
lean_dec(v___x_638_);
lean_dec(v___x_649_);
v___x_651_ = lean_nat_dec_eq(v_g1_650_, v___x_639_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_656_; 
lean_inc(v_g1_650_);
v___x_652_ = lean_nat_to_int(v_g1_650_);
v___x_653_ = lean_int_div_exact(v_num_648_, v___x_652_);
lean_dec(v___x_652_);
lean_dec(v_num_648_);
v___x_654_ = lean_nat_div_exact(v_den_642_, v_g1_650_);
lean_dec(v_g1_650_);
lean_dec(v_den_642_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_654_);
lean_ctor_set(v___x_636_, 0, v___x_653_);
v___x_656_ = v___x_636_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
else
{
lean_object* v___x_659_; 
lean_dec(v_g1_650_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v_den_642_);
lean_ctor_set(v___x_636_, 0, v_num_648_);
v___x_659_ = v___x_636_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_num_648_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_den_642_);
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
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
lean_dec(v___x_638_);
lean_inc(v_den_634_);
v___x_661_ = lean_nat_to_int(v_den_634_);
v___x_662_ = lean_int_mul(v_num_631_, v___x_661_);
lean_dec(v___x_661_);
lean_dec(v_num_631_);
lean_inc(v_den_632_);
v___x_663_ = lean_nat_to_int(v_den_632_);
v___x_664_ = lean_int_mul(v_num_633_, v___x_663_);
lean_dec(v___x_663_);
lean_dec(v_num_633_);
v___x_665_ = lean_int_add(v___x_662_, v___x_664_);
lean_dec(v___x_664_);
lean_dec(v___x_662_);
v___x_666_ = lean_nat_mul(v_den_632_, v_den_634_);
lean_dec(v_den_634_);
lean_dec(v_den_632_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_666_);
lean_ctor_set(v___x_636_, 0, v___x_665_);
v___x_668_ = v___x_636_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_neg(lean_object* v_a_673_){
_start:
{
lean_object* v_num_674_; lean_object* v_den_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_683_; 
v_num_674_ = lean_ctor_get(v_a_673_, 0);
v_den_675_ = lean_ctor_get(v_a_673_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_a_673_);
if (v_isSharedCheck_683_ == 0)
{
v___x_677_ = v_a_673_;
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_den_675_);
lean_inc(v_num_674_);
lean_dec(v_a_673_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_679_ = lean_int_neg(v_num_674_);
lean_dec(v_num_674_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_679_);
v___x_681_ = v___x_677_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_den_675_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_sub(lean_object* v_a_686_, lean_object* v_b_687_){
_start:
{
lean_object* v_num_688_; lean_object* v_den_689_; lean_object* v_num_690_; lean_object* v_den_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_727_; 
v_num_688_ = lean_ctor_get(v_a_686_, 0);
lean_inc(v_num_688_);
v_den_689_ = lean_ctor_get(v_a_686_, 1);
lean_inc(v_den_689_);
lean_dec_ref(v_a_686_);
v_num_690_ = lean_ctor_get(v_b_687_, 0);
v_den_691_ = lean_ctor_get(v_b_687_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v_b_687_);
if (v_isSharedCheck_727_ == 0)
{
v___x_693_ = v_b_687_;
v_isShared_694_ = v_isSharedCheck_727_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_den_691_);
lean_inc(v_num_690_);
lean_dec(v_b_687_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_727_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_695_ = lean_nat_gcd(v_den_689_, v_den_691_);
v___x_696_ = lean_unsigned_to_nat(1u);
v___x_697_ = lean_nat_dec_eq(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v_den_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_num_705_; lean_object* v___x_706_; lean_object* v_g1_707_; uint8_t v___x_708_; 
v___x_698_ = lean_nat_div(v_den_689_, v___x_695_);
lean_dec(v_den_689_);
v_den_699_ = lean_nat_mul(v___x_698_, v_den_691_);
v___x_700_ = lean_nat_div(v_den_691_, v___x_695_);
lean_dec(v_den_691_);
v___x_701_ = lean_nat_to_int(v___x_700_);
v___x_702_ = lean_int_mul(v_num_688_, v___x_701_);
lean_dec(v___x_701_);
lean_dec(v_num_688_);
v___x_703_ = lean_nat_to_int(v___x_698_);
v___x_704_ = lean_int_mul(v_num_690_, v___x_703_);
lean_dec(v___x_703_);
lean_dec(v_num_690_);
v_num_705_ = lean_int_sub(v___x_702_, v___x_704_);
lean_dec(v___x_704_);
lean_dec(v___x_702_);
v___x_706_ = lean_nat_abs(v_num_705_);
v_g1_707_ = lean_nat_gcd(v___x_706_, v___x_695_);
lean_dec(v___x_695_);
lean_dec(v___x_706_);
v___x_708_ = lean_nat_dec_eq(v_g1_707_, v___x_696_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
lean_inc(v_g1_707_);
v___x_709_ = lean_nat_to_int(v_g1_707_);
v___x_710_ = lean_int_div_exact(v_num_705_, v___x_709_);
lean_dec(v___x_709_);
lean_dec(v_num_705_);
v___x_711_ = lean_nat_div_exact(v_den_699_, v_g1_707_);
lean_dec(v_g1_707_);
lean_dec(v_den_699_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v___x_711_);
lean_ctor_set(v___x_693_, 0, v___x_710_);
v___x_713_ = v___x_693_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
else
{
lean_object* v___x_716_; 
lean_dec(v_g1_707_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v_den_699_);
lean_ctor_set(v___x_693_, 0, v_num_705_);
v___x_716_ = v___x_693_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_num_705_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_den_699_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
lean_dec(v___x_695_);
lean_inc(v_den_691_);
v___x_718_ = lean_nat_to_int(v_den_691_);
v___x_719_ = lean_int_mul(v_num_688_, v___x_718_);
lean_dec(v___x_718_);
lean_dec(v_num_688_);
lean_inc(v_den_689_);
v___x_720_ = lean_nat_to_int(v_den_689_);
v___x_721_ = lean_int_mul(v_num_690_, v___x_720_);
lean_dec(v___x_720_);
lean_dec(v_num_690_);
v___x_722_ = lean_int_sub(v___x_719_, v___x_721_);
lean_dec(v___x_721_);
lean_dec(v___x_719_);
v___x_723_ = lean_nat_mul(v_den_689_, v_den_691_);
lean_dec(v_den_691_);
lean_dec(v_den_689_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v___x_723_);
lean_ctor_set(v___x_693_, 0, v___x_722_);
v___x_725_ = v___x_693_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_723_);
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
LEAN_EXPORT lean_object* l_Rat_floor(lean_object* v_a_730_){
_start:
{
lean_object* v_num_731_; lean_object* v_den_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v_num_731_ = lean_ctor_get(v_a_730_, 0);
lean_inc(v_num_731_);
v_den_732_ = lean_ctor_get(v_a_730_, 1);
lean_inc(v_den_732_);
lean_dec_ref(v_a_730_);
v___x_733_ = lean_unsigned_to_nat(1u);
v___x_734_ = lean_nat_dec_eq(v_den_732_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_nat_to_int(v_den_732_);
v___x_736_ = lean_int_ediv(v_num_731_, v___x_735_);
lean_dec(v___x_735_);
lean_dec(v_num_731_);
return v___x_736_;
}
else
{
lean_dec(v_den_732_);
return v_num_731_;
}
}
}
static lean_object* _init_l_Rat_ceil___closed__0(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = lean_nat_to_int(v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Rat_ceil(lean_object* v_a_739_){
_start:
{
lean_object* v_num_740_; lean_object* v_den_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v_num_740_ = lean_ctor_get(v_a_739_, 0);
lean_inc(v_num_740_);
v_den_741_ = lean_ctor_get(v_a_739_, 1);
lean_inc(v_den_741_);
lean_dec_ref(v_a_739_);
v___x_742_ = lean_unsigned_to_nat(1u);
v___x_743_ = lean_nat_dec_eq(v_den_741_, v___x_742_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_744_ = lean_nat_to_int(v_den_741_);
v___x_745_ = lean_int_ediv(v_num_740_, v___x_744_);
lean_dec(v___x_744_);
lean_dec(v_num_740_);
v___x_746_ = lean_obj_once(&l_Rat_ceil___closed__0, &l_Rat_ceil___closed__0_once, _init_l_Rat_ceil___closed__0);
v___x_747_ = lean_int_add(v___x_745_, v___x_746_);
lean_dec(v___x_745_);
return v___x_747_;
}
else
{
lean_dec(v_den_741_);
return v_num_740_;
}
}
}
static lean_object* _init_l_Rat_abs___closed__0(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = l_Nat_cast___at___00Rat_ofScientific_spec__0(v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Rat_abs(lean_object* v_a_750_){
_start:
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = lean_obj_once(&l_Rat_abs___closed__0, &l_Rat_abs___closed__0_once, _init_l_Rat_abs___closed__0);
lean_inc_ref(v_a_750_);
v___x_752_ = l_Rat_instDecidableLe(v___x_751_, v_a_750_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; 
v___x_753_ = l_Rat_neg(v_a_750_);
return v___x_753_;
}
else
{
return v_a_750_;
}
}
}
lean_object* runtime_initialize_Init_Data_Nat_Coprime(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_OfScientific(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Extra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Rat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Coprime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_OfScientific(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instInhabitedRat = _init_l_instInhabitedRat();
lean_mark_persistent(l_instInhabitedRat);
l_Rat_instLT = _init_l_Rat_instLT();
lean_mark_persistent(l_Rat_instLT);
l_Rat_instLE = _init_l_Rat_instLE();
lean_mark_persistent(l_Rat_instLE);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Rat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Rat_den__nz___autoParam = _init_l_Rat_den__nz___autoParam();
lean_mark_persistent(l_Rat_den__nz___autoParam);
l_Rat_reduced___autoParam = _init_l_Rat_reduced___autoParam();
lean_mark_persistent(l_Rat_reduced___autoParam);
l_Rat_normalize___auto__1 = _init_l_Rat_normalize___auto__1();
lean_mark_persistent(l_Rat_normalize___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Coprime(uint8_t builtin);
lean_object* initialize_Init_Data_OfScientific(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Extra(uint8_t builtin);
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Rat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Coprime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_OfScientific(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Rat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Rat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Rat_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
