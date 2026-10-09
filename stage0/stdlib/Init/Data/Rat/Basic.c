// Lean compiler output
// Module: Init.Data.Rat.Basic
// Imports: public import Init.Data.Nat.Coprime public import Init.Data.OfScientific.Basic public import Init.Data.Int.DivMod.Basic public import Init.Data.String.Defs public import Init.Data.ToString.Macro public import Init.Data.ToString.Extra import Init.Data.Hashable import Init.Data.Int.DivMod.Bootstrap import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.Lemmas import Init.Data.Int.Order import Init.Data.Int.Pow import Init.Data.Nat.Dvd
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
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
LEAN_EXPORT lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___boxed(lean_object*, lean_object*, lean_object*);
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
uint8_t l_instDecidableEqRat_decEq(lean_object* v_x_79_, lean_object* v_x_80_){
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
LEAN_EXPORT void l_instDecidableEqRat_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_79_ = stack[0].m_obj;
lean_object* v_x_80_ = stack[1].m_obj;
uint8_t v_res_87_;
v_res_87_ = l_instDecidableEqRat_decEq(v_x_79_, v_x_80_);
stack->m_num = v_res_87_;
}
LEAN_EXPORT lean_object* l_instDecidableEqRat_decEq___boxed(lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l_instDecidableEqRat_decEq(v_x_88_, v_x_89_);
lean_dec_ref(v_x_89_);
lean_dec_ref(v_x_88_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
uint8_t l_instDecidableEqRat(lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
uint8_t v___x_94_; 
v___x_94_ = l_instDecidableEqRat_decEq(v_x_92_, v_x_93_);
return v___x_94_;
}
}
LEAN_EXPORT void l_instDecidableEqRat_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_92_ = stack[0].m_obj;
lean_object* v_x_93_ = stack[1].m_obj;
uint8_t v_res_95_;
v_res_95_ = l_instDecidableEqRat(v_x_92_, v_x_93_);
stack->m_num = v_res_95_;
}
LEAN_EXPORT lean_object* l_instDecidableEqRat___boxed(lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_instDecidableEqRat(v_x_96_, v_x_97_);
lean_dec_ref(v_x_97_);
lean_dec_ref(v_x_96_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
static lean_object* _init_l_instHashableRat_hash___closed__0(void){
_start:
{
lean_object* v_natZero_100_; lean_object* v_intZero_101_; 
v_natZero_100_ = lean_unsigned_to_nat(0u);
v_intZero_101_ = lean_nat_to_int(v_natZero_100_);
return v_intZero_101_;
}
}
uint64_t l_instHashableRat_hash(lean_object* v_x_102_){
_start:
{
lean_object* v_num_103_; lean_object* v_den_104_; uint64_t v___x_105_; uint64_t v___y_107_; lean_object* v_intZero_113_; uint8_t v_isNeg_114_; 
v_num_103_ = lean_ctor_get(v_x_102_, 0);
v_den_104_ = lean_ctor_get(v_x_102_, 1);
v___x_105_ = 0ULL;
v_intZero_113_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v_isNeg_114_ = lean_int_dec_lt(v_num_103_, v_intZero_113_);
if (v_isNeg_114_ == 0)
{
lean_object* v_a_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint64_t v___x_118_; 
v_a_115_ = lean_nat_abs(v_num_103_);
v___x_116_ = lean_unsigned_to_nat(2u);
v___x_117_ = lean_nat_mul(v___x_116_, v_a_115_);
lean_dec(v_a_115_);
v___x_118_ = lean_uint64_of_nat(v___x_117_);
lean_dec(v___x_117_);
v___y_107_ = v___x_118_;
goto v___jp_106_;
}
else
{
lean_object* v_abs_119_; lean_object* v_one_120_; lean_object* v_a_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint64_t v___x_125_; 
v_abs_119_ = lean_nat_abs(v_num_103_);
v_one_120_ = lean_unsigned_to_nat(1u);
v_a_121_ = lean_nat_sub(v_abs_119_, v_one_120_);
lean_dec(v_abs_119_);
v___x_122_ = lean_unsigned_to_nat(2u);
v___x_123_ = lean_nat_mul(v___x_122_, v_a_121_);
lean_dec(v_a_121_);
v___x_124_ = lean_nat_add(v___x_123_, v_one_120_);
lean_dec(v___x_123_);
v___x_125_ = lean_uint64_of_nat(v___x_124_);
lean_dec(v___x_124_);
v___y_107_ = v___x_125_;
goto v___jp_106_;
}
v___jp_106_:
{
uint64_t v___x_108_; uint64_t v___x_109_; uint64_t v___x_110_; uint64_t v___x_111_; uint64_t v___x_112_; 
v___x_108_ = lean_uint64_mix_hash(v___x_105_, v___y_107_);
v___x_109_ = lean_uint64_of_nat(v_den_104_);
v___x_110_ = lean_uint64_mix_hash(v___x_108_, v___x_109_);
v___x_111_ = lean_uint64_mix_hash(v___x_110_, v___x_105_);
v___x_112_ = lean_uint64_mix_hash(v___x_111_, v___x_105_);
return v___x_112_;
}
}
}
LEAN_EXPORT void l_instHashableRat_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_102_ = stack[0].m_obj;
uint64_t v_res_126_;
v_res_126_ = l_instHashableRat_hash(v_x_102_);
stack->m_num = v_res_126_;
}
LEAN_EXPORT lean_object* l_instHashableRat_hash___boxed(lean_object* v_x_127_){
_start:
{
uint64_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_instHashableRat_hash(v_x_127_);
lean_dec_ref(v_x_127_);
v_r_129_ = lean_box_uint64(v_res_128_);
return v_r_129_;
}
}
static lean_object* _init_l_instInhabitedRat___closed__0(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_132_);
return v___x_134_;
}
}
static lean_object* _init_l_instInhabitedRat(void){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lean_obj_once(&l_instInhabitedRat___closed__0, &l_instInhabitedRat___closed__0_once, _init_l_instInhabitedRat___closed__0);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_instToStringRat___lam__0(lean_object* v_a_137_){
_start:
{
lean_object* v_num_138_; lean_object* v_den_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v_num_138_ = lean_ctor_get(v_a_137_, 0);
lean_inc(v_num_138_);
v_den_139_ = lean_ctor_get(v_a_137_, 1);
lean_inc(v_den_139_);
lean_dec_ref(v_a_137_);
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_dec_eq(v_den_139_, v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_142_ = l_Int_repr(v_num_138_);
lean_dec(v_num_138_);
v___x_143_ = ((lean_object*)(l_instToStringRat___lam__0___closed__0));
v___x_144_ = lean_string_append(v___x_142_, v___x_143_);
v___x_145_ = l_Nat_reprFast(v_den_139_);
v___x_146_ = lean_string_append(v___x_144_, v___x_145_);
lean_dec_ref(v___x_145_);
return v___x_146_;
}
else
{
lean_object* v___x_147_; 
lean_dec(v_den_139_);
v___x_147_ = l_Int_repr(v_num_138_);
lean_dec(v_num_138_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_instReprRat___lam__0(lean_object* v_a_152_, lean_object* v_x_153_){
_start:
{
lean_object* v_num_154_; lean_object* v_den_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v_num_154_ = lean_ctor_get(v_a_152_, 0);
lean_inc(v_num_154_);
v_den_155_ = lean_ctor_get(v_a_152_, 1);
lean_inc(v_den_155_);
lean_dec_ref(v_a_152_);
v___x_156_ = lean_unsigned_to_nat(1u);
v___x_157_ = lean_nat_dec_eq(v_den_155_, v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_158_ = ((lean_object*)(l_instReprRat___lam__0___closed__0));
v___x_159_ = l_Int_repr(v_num_154_);
lean_dec(v_num_154_);
v___x_160_ = lean_string_append(v___x_158_, v___x_159_);
lean_dec_ref(v___x_159_);
v___x_161_ = ((lean_object*)(l_instReprRat___lam__0___closed__1));
v___x_162_ = lean_string_append(v___x_160_, v___x_161_);
v___x_163_ = l_Nat_reprFast(v_den_155_);
v___x_164_ = lean_string_append(v___x_162_, v___x_163_);
lean_dec_ref(v___x_163_);
v___x_165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
else
{
lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
lean_dec(v_den_155_);
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v___x_168_ = lean_int_dec_lt(v_num_154_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = l_Int_repr(v_num_154_);
lean_dec(v_num_154_);
v___x_170_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = l_Int_repr(v_num_154_);
lean_dec(v_num_154_);
v___x_172_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
v___x_173_ = l_Repr_addAppParen(v___x_172_, v___x_166_);
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l_instReprRat___lam__0___boxed(lean_object* v_a_174_, lean_object* v_x_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_instReprRat___lam__0(v_a_174_, v_x_175_);
lean_dec(v_x_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Rat_maybeNormalize___redArg(lean_object* v_num_179_, lean_object* v_den_180_, lean_object* v_g_181_){
_start:
{
lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_nat_dec_eq(v_g_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
lean_inc(v_g_181_);
v___x_184_ = lean_nat_to_int(v_g_181_);
v___x_185_ = lean_int_div_exact(v_num_179_, v___x_184_);
lean_dec(v___x_184_);
lean_dec(v_num_179_);
v___x_186_ = lean_nat_div_exact(v_den_180_, v_g_181_);
lean_dec(v_g_181_);
lean_dec(v_den_180_);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_185_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
return v___x_187_;
}
else
{
lean_object* v___x_188_; 
lean_dec(v_g_181_);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v_num_179_);
lean_ctor_set(v___x_188_, 1, v_den_180_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_maybeNormalize(lean_object* v_num_189_, lean_object* v_den_190_, lean_object* v_g_191_, lean_object* v_dvd__num_192_, lean_object* v_dvd__den_193_, lean_object* v_den__nz_194_, lean_object* v_reduced_195_){
_start:
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_dec_eq(v_g_191_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
lean_inc(v_g_191_);
v___x_198_ = lean_nat_to_int(v_g_191_);
v___x_199_ = lean_int_div_exact(v_num_189_, v___x_198_);
lean_dec(v___x_198_);
lean_dec(v_num_189_);
v___x_200_ = lean_nat_div_exact(v_den_190_, v_g_191_);
lean_dec(v_g_191_);
lean_dec(v_den_190_);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
return v___x_201_;
}
else
{
lean_object* v___x_202_; 
lean_dec(v_g_191_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v_num_189_);
lean_ctor_set(v___x_202_, 1, v_den_190_);
return v___x_202_;
}
}
}
static lean_object* _init_l_Rat_normalize___auto__1(void){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_obj_once(&l_Rat_den__nz___autoParam___closed__26, &l_Rat_den__nz___autoParam___closed__26_once, _init_l_Rat_den__nz___autoParam___closed__26);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Rat_normalize___redArg(lean_object* v_num_204_, lean_object* v_den_205_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_206_ = lean_nat_abs(v_num_204_);
v___x_207_ = lean_nat_gcd(v___x_206_, v_den_205_);
lean_dec(v___x_206_);
v___x_208_ = lean_unsigned_to_nat(1u);
v___x_209_ = lean_nat_dec_eq(v___x_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
lean_inc(v___x_207_);
v___x_210_ = lean_nat_to_int(v___x_207_);
v___x_211_ = lean_int_div_exact(v_num_204_, v___x_210_);
lean_dec(v___x_210_);
lean_dec(v_num_204_);
v___x_212_ = lean_nat_div_exact(v_den_205_, v___x_207_);
lean_dec(v___x_207_);
lean_dec(v_den_205_);
v___x_213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_211_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; 
lean_dec(v___x_207_);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v_num_204_);
lean_ctor_set(v___x_214_, 1, v_den_205_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_normalize(lean_object* v_num_215_, lean_object* v_den_216_, lean_object* v_den__nz_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_218_ = lean_nat_abs(v_num_215_);
v___x_219_ = lean_nat_gcd(v___x_218_, v_den_216_);
lean_dec(v___x_218_);
v___x_220_ = lean_unsigned_to_nat(1u);
v___x_221_ = lean_nat_dec_eq(v___x_219_, v___x_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
lean_inc(v___x_219_);
v___x_222_ = lean_nat_to_int(v___x_219_);
v___x_223_ = lean_int_div_exact(v_num_215_, v___x_222_);
lean_dec(v___x_222_);
lean_dec(v_num_215_);
v___x_224_ = lean_nat_div_exact(v_den_216_, v___x_219_);
lean_dec(v___x_219_);
lean_dec(v_den_216_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; 
lean_dec(v___x_219_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v_num_215_);
lean_ctor_set(v___x_226_, 1, v_den_216_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00mkRat_spec__0(lean_object* v_a_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = lean_nat_to_int(v_a_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_mkRat(lean_object* v_num_229_, lean_object* v_den_230_){
_start:
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_nat_dec_eq(v_den_230_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_233_ = lean_nat_abs(v_num_229_);
v___x_234_ = lean_nat_gcd(v___x_233_, v_den_230_);
lean_dec(v___x_233_);
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = lean_nat_dec_eq(v___x_234_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
lean_inc(v___x_234_);
v___x_237_ = lean_nat_to_int(v___x_234_);
v___x_238_ = lean_int_div_exact(v_num_229_, v___x_237_);
lean_dec(v___x_237_);
lean_dec(v_num_229_);
v___x_239_ = lean_nat_div_exact(v_den_230_, v___x_234_);
lean_dec(v___x_234_);
lean_dec(v_den_230_);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
return v___x_240_;
}
else
{
lean_object* v___x_241_; 
lean_dec(v___x_234_);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v_num_229_);
lean_ctor_set(v___x_241_, 1, v_den_230_);
return v___x_241_;
}
}
else
{
lean_object* v___x_242_; 
lean_dec(v_den_230_);
lean_dec(v_num_229_);
v___x_242_ = lean_obj_once(&l_instInhabitedRat___closed__0, &l_instInhabitedRat___closed__0_once, _init_l_instInhabitedRat___closed__0);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_ofInt(lean_object* v_num_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v_num_243_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Rat_instNatCast___lam__0(lean_object* v_n_246_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_nat_to_int(v_n_246_);
v___x_248_ = l_Rat_ofInt(v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Rat_instOfNat(lean_object* v_n_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Rat_instNatCast___lam__0(v_n_253_);
return v___x_254_;
}
}
uint8_t l_Rat_isInt(lean_object* v_a_255_){
_start:
{
lean_object* v_den_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v_den_256_ = lean_ctor_get(v_a_255_, 1);
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_dec_eq(v_den_256_, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT void l_Rat_isInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_255_ = stack[0].m_obj;
uint8_t v_res_259_;
v_res_259_ = l_Rat_isInt(v_a_255_);
stack->m_num = v_res_259_;
}
LEAN_EXPORT lean_object* l_Rat_isInt___boxed(lean_object* v_a_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Rat_isInt(v_a_260_);
lean_dec_ref(v_a_260_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT lean_object* l_Rat_divInt(lean_object* v_x_263_, lean_object* v_x_264_){
_start:
{
lean_object* v_natZero_265_; lean_object* v_intZero_266_; uint8_t v_isNeg_267_; 
v_natZero_265_ = lean_unsigned_to_nat(0u);
v_intZero_266_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v_isNeg_267_ = lean_int_dec_lt(v_x_264_, v_intZero_266_);
if (v_isNeg_267_ == 0)
{
lean_object* v_a_268_; uint8_t v___x_269_; 
v_a_268_ = lean_nat_abs(v_x_264_);
v___x_269_ = lean_nat_dec_eq(v_a_268_, v_natZero_265_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_270_ = lean_nat_abs(v_x_263_);
v___x_271_ = lean_nat_gcd(v___x_270_, v_a_268_);
lean_dec(v___x_270_);
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_nat_dec_eq(v___x_271_, v___x_272_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
lean_inc(v___x_271_);
v___x_274_ = lean_nat_to_int(v___x_271_);
v___x_275_ = lean_int_div_exact(v_x_263_, v___x_274_);
lean_dec(v___x_274_);
lean_dec(v_x_263_);
v___x_276_ = lean_nat_div_exact(v_a_268_, v___x_271_);
lean_dec(v___x_271_);
lean_dec(v_a_268_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
return v___x_277_;
}
else
{
lean_object* v___x_278_; 
lean_dec(v___x_271_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v_x_263_);
lean_ctor_set(v___x_278_, 1, v_a_268_);
return v___x_278_;
}
}
else
{
lean_object* v___x_279_; 
lean_dec(v_a_268_);
lean_dec(v_x_263_);
v___x_279_ = lean_obj_once(&l_instInhabitedRat___closed__0, &l_instInhabitedRat___closed__0_once, _init_l_instInhabitedRat___closed__0);
return v___x_279_;
}
}
else
{
lean_object* v_abs_280_; lean_object* v_one_281_; lean_object* v_a_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v_abs_280_ = lean_nat_abs(v_x_264_);
v_one_281_ = lean_unsigned_to_nat(1u);
v_a_282_ = lean_nat_sub(v_abs_280_, v_one_281_);
lean_dec(v_abs_280_);
v___x_283_ = lean_int_neg(v_x_263_);
lean_dec(v_x_263_);
v___x_284_ = lean_nat_add(v_a_282_, v_one_281_);
lean_dec(v_a_282_);
v___x_285_ = lean_nat_abs(v___x_283_);
v___x_286_ = lean_nat_gcd(v___x_285_, v___x_284_);
lean_dec(v___x_285_);
v___x_287_ = lean_nat_dec_eq(v___x_286_, v_one_281_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
lean_inc(v___x_286_);
v___x_288_ = lean_nat_to_int(v___x_286_);
v___x_289_ = lean_int_div_exact(v___x_283_, v___x_288_);
lean_dec(v___x_288_);
lean_dec(v___x_283_);
v___x_290_ = lean_nat_div_exact(v___x_284_, v___x_286_);
lean_dec(v___x_286_);
lean_dec(v___x_284_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
return v___x_291_;
}
else
{
lean_object* v___x_292_; 
lean_dec(v___x_286_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_283_);
lean_ctor_set(v___x_292_, 1, v___x_284_);
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_divInt___boxed(lean_object* v_x_293_, lean_object* v_x_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Rat_divInt(v_x_293_, v_x_294_);
lean_dec(v_x_294_);
return v_res_295_;
}
}
static lean_object* _init_l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__3));
v___x_331_ = l_String_toRawSubstring_x27(v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1(lean_object* v_x_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = ((lean_object*)(l_Rat_term___x2f_x2e___00__closed__2));
lean_inc(v_x_347_);
v___x_351_ = l_Lean_Syntax_isOfKind(v_x_347_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
lean_dec(v_x_347_);
v___x_352_ = lean_box(1);
v___x_353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v_a_349_);
return v___x_353_;
}
else
{
lean_object* v_quotContext_354_; lean_object* v_currMacroScope_355_; lean_object* v_ref_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_quotContext_354_ = lean_ctor_get(v_a_348_, 1);
v_currMacroScope_355_ = lean_ctor_get(v_a_348_, 2);
v_ref_356_ = lean_ctor_get(v_a_348_, 5);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = l_Lean_Syntax_getArg(v_x_347_, v___x_357_);
v___x_359_ = lean_unsigned_to_nat(2u);
v___x_360_ = l_Lean_Syntax_getArg(v_x_347_, v___x_359_);
lean_dec(v_x_347_);
v___x_361_ = 0;
v___x_362_ = l_Lean_SourceInfo_fromRef(v_ref_356_, v___x_361_);
v___x_363_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2));
v___x_364_ = lean_obj_once(&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4, &l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4_once, _init_l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4);
v___x_365_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6));
lean_inc(v_currMacroScope_355_);
lean_inc(v_quotContext_354_);
v___x_366_ = l_Lean_addMacroScope(v_quotContext_354_, v___x_365_, v_currMacroScope_355_);
v___x_367_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__10));
lean_inc_n(v___x_362_, 2);
v___x_368_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_368_, 0, v___x_362_);
lean_ctor_set(v___x_368_, 1, v___x_364_);
lean_ctor_set(v___x_368_, 2, v___x_366_);
lean_ctor_set(v___x_368_, 3, v___x_367_);
v___x_369_ = ((lean_object*)(l_Rat_den__nz___autoParam___closed__9));
v___x_370_ = l_Lean_Syntax_node2(v___x_362_, v___x_369_, v___x_358_, v___x_360_);
v___x_371_ = l_Lean_Syntax_node2(v___x_362_, v___x_363_, v___x_368_, v___x_370_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v_a_349_);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___boxed(lean_object* v_x_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1(v_x_373_, v_a_374_, v_a_375_);
lean_dec_ref(v_a_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1(lean_object* v_x_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2));
lean_inc(v_x_380_);
v___x_384_ = l_Lean_Syntax_isOfKind(v_x_380_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v_x_380_);
v___x_385_ = lean_box(0);
v___x_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v_a_382_);
return v___x_386_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = l_Lean_Syntax_getArg(v_x_380_, v___x_387_);
v___x_389_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__1));
lean_inc(v___x_388_);
v___x_390_ = l_Lean_Syntax_isOfKind(v___x_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec(v___x_388_);
lean_dec(v_x_380_);
v___x_391_ = lean_box(0);
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_a_382_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = l_Lean_Syntax_getArg(v_x_380_, v___x_393_);
lean_dec(v_x_380_);
v___x_395_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_394_);
v___x_396_ = l_Lean_Syntax_matchesNull(v___x_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec(v___x_394_);
lean_dec(v___x_388_);
v___x_397_ = lean_box(0);
v___x_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v_a_382_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_ref_401_; uint8_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_399_ = l_Lean_Syntax_getArg(v___x_394_, v___x_387_);
v___x_400_ = l_Lean_Syntax_getArg(v___x_394_, v___x_393_);
lean_dec(v___x_394_);
v_ref_401_ = l_Lean_replaceRef(v___x_388_, v_a_381_);
lean_dec(v___x_388_);
v___x_402_ = 0;
v___x_403_ = l_Lean_SourceInfo_fromRef(v_ref_401_, v___x_402_);
lean_dec(v_ref_401_);
v___x_404_ = ((lean_object*)(l_Rat_term___x2f_x2e___00__closed__2));
v___x_405_ = ((lean_object*)(l_Rat_term___x2f_x2e___00__closed__5));
lean_inc(v___x_403_);
v___x_406_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_403_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = l_Lean_Syntax_node3(v___x_403_, v___x_404_, v___x_399_, v___x_406_, v___x_400_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v_a_382_);
return v___x_408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___boxed(lean_object* v_x_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1(v_x_409_, v_a_410_, v_a_411_);
lean_dec(v_a_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Rat_ofScientific_spec__0(lean_object* v_a_413_){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_nat_to_int(v_a_413_);
v___x_415_ = l_Rat_ofInt(v___x_414_);
return v___x_415_;
}
}
lean_object* l_Rat_ofScientific(lean_object* v_m_416_, uint8_t v_s_417_, lean_object* v_e_418_){
_start:
{
if (v_s_417_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_419_ = lean_unsigned_to_nat(10u);
v___x_420_ = lean_nat_pow(v___x_419_, v_e_418_);
v___x_421_ = lean_nat_mul(v_m_416_, v___x_420_);
lean_dec(v___x_420_);
lean_dec(v_m_416_);
v___x_422_ = l_Nat_cast___at___00Rat_ofScientific_spec__0(v___x_421_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_423_ = lean_nat_to_int(v_m_416_);
v___x_424_ = lean_unsigned_to_nat(10u);
v___x_425_ = lean_nat_pow(v___x_424_, v_e_418_);
v___x_426_ = lean_nat_abs(v___x_423_);
v___x_427_ = lean_nat_gcd(v___x_426_, v___x_425_);
lean_dec(v___x_426_);
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = lean_nat_dec_eq(v___x_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_inc(v___x_427_);
v___x_430_ = lean_nat_to_int(v___x_427_);
v___x_431_ = lean_int_div_exact(v___x_423_, v___x_430_);
lean_dec(v___x_430_);
lean_dec(v___x_423_);
v___x_432_ = lean_nat_div_exact(v___x_425_, v___x_427_);
lean_dec(v___x_427_);
lean_dec(v___x_425_);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
return v___x_433_;
}
else
{
lean_object* v___x_434_; 
lean_dec(v___x_427_);
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_423_);
lean_ctor_set(v___x_434_, 1, v___x_425_);
return v___x_434_;
}
}
}
}
LEAN_EXPORT void l_Rat_ofScientific_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_416_ = stack[0].m_obj;
uint8_t v_s_417_ = stack[1].m_num;
lean_object* v_e_418_ = stack[2].m_obj;
lean_object* v_res_435_;
v_res_435_ = l_Rat_ofScientific(v_m_416_, v_s_417_, v_e_418_);
stack->m_obj
 = v_res_435_;
}
LEAN_EXPORT lean_object* l_Rat_ofScientific___boxed(lean_object* v_m_436_, lean_object* v_s_437_, lean_object* v_e_438_){
_start:
{
uint8_t v_s_boxed_439_; lean_object* v_res_440_; 
v_s_boxed_439_ = lean_unbox(v_s_437_);
v_res_440_ = l_Rat_ofScientific(v_m_436_, v_s_boxed_439_, v_e_438_);
lean_dec(v_e_438_);
return v_res_440_;
}
}
uint8_t l_Rat_blt(lean_object* v_a_443_, lean_object* v_b_444_){
_start:
{
lean_object* v_num_445_; lean_object* v_den_446_; lean_object* v___x_455_; uint8_t v___x_463_; 
v_num_445_ = lean_ctor_get(v_a_443_, 0);
lean_inc(v_num_445_);
v_den_446_ = lean_ctor_get(v_a_443_, 1);
lean_inc(v_den_446_);
lean_dec_ref(v_a_443_);
v___x_455_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v___x_463_ = lean_int_dec_lt(v_num_445_, v___x_455_);
if (v___x_463_ == 0)
{
goto v___jp_456_;
}
else
{
lean_object* v_num_464_; uint8_t v___x_465_; 
v_num_464_ = lean_ctor_get(v_b_444_, 0);
v___x_465_ = lean_int_dec_le(v___x_455_, v_num_464_);
if (v___x_465_ == 0)
{
goto v___jp_456_;
}
else
{
lean_dec(v_den_446_);
lean_dec(v_num_445_);
lean_dec_ref(v_b_444_);
return v___x_463_;
}
}
v___jp_447_:
{
lean_object* v_num_448_; lean_object* v_den_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v_num_448_ = lean_ctor_get(v_b_444_, 0);
lean_inc(v_num_448_);
v_den_449_ = lean_ctor_get(v_b_444_, 1);
lean_inc(v_den_449_);
lean_dec_ref(v_b_444_);
v___x_450_ = lean_nat_to_int(v_den_449_);
v___x_451_ = lean_int_mul(v_num_445_, v___x_450_);
lean_dec(v___x_450_);
lean_dec(v_num_445_);
v___x_452_ = lean_nat_to_int(v_den_446_);
v___x_453_ = lean_int_mul(v_num_448_, v___x_452_);
lean_dec(v___x_452_);
lean_dec(v_num_448_);
v___x_454_ = lean_int_dec_lt(v___x_451_, v___x_453_);
lean_dec(v___x_453_);
lean_dec(v___x_451_);
return v___x_454_;
}
v___jp_456_:
{
uint8_t v___x_457_; 
v___x_457_ = lean_int_dec_eq(v_num_445_, v___x_455_);
if (v___x_457_ == 0)
{
uint8_t v___x_458_; 
v___x_458_ = lean_int_dec_lt(v___x_455_, v_num_445_);
if (v___x_458_ == 0)
{
goto v___jp_447_;
}
else
{
lean_object* v_num_459_; uint8_t v___x_460_; 
v_num_459_ = lean_ctor_get(v_b_444_, 0);
v___x_460_ = lean_int_dec_le(v_num_459_, v___x_455_);
if (v___x_460_ == 0)
{
goto v___jp_447_;
}
else
{
lean_dec(v_den_446_);
lean_dec(v_num_445_);
lean_dec_ref(v_b_444_);
return v___x_457_;
}
}
}
else
{
lean_object* v_num_461_; uint8_t v___x_462_; 
lean_dec(v_den_446_);
lean_dec(v_num_445_);
v_num_461_ = lean_ctor_get(v_b_444_, 0);
lean_inc(v_num_461_);
lean_dec_ref(v_b_444_);
v___x_462_ = lean_int_dec_lt(v___x_455_, v_num_461_);
lean_dec(v_num_461_);
return v___x_462_;
}
}
}
}
LEAN_EXPORT void l_Rat_blt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_443_ = stack[0].m_obj;
lean_object* v_b_444_ = stack[1].m_obj;
uint8_t v_res_466_;
v_res_466_ = l_Rat_blt(v_a_443_, v_b_444_);
stack->m_num = v_res_466_;
}
LEAN_EXPORT lean_object* l_Rat_blt___boxed(lean_object* v_a_467_, lean_object* v_b_468_){
_start:
{
uint8_t v_res_469_; lean_object* v_r_470_; 
v_res_469_ = l_Rat_blt(v_a_467_, v_b_468_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
static lean_object* _init_l_Rat_instLT(void){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = lean_box(0);
return v___x_471_;
}
}
uint8_t l_Rat_instDecidableLt(lean_object* v_a_472_, lean_object* v_b_473_){
_start:
{
uint8_t v___x_474_; 
v___x_474_ = l_Rat_blt(v_a_472_, v_b_473_);
return v___x_474_;
}
}
LEAN_EXPORT void l_Rat_instDecidableLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_472_ = stack[0].m_obj;
lean_object* v_b_473_ = stack[1].m_obj;
uint8_t v_res_475_;
v_res_475_ = l_Rat_instDecidableLt(v_a_472_, v_b_473_);
stack->m_num = v_res_475_;
}
LEAN_EXPORT lean_object* l_Rat_instDecidableLt___boxed(lean_object* v_a_476_, lean_object* v_b_477_){
_start:
{
uint8_t v_res_478_; lean_object* v_r_479_; 
v_res_478_ = l_Rat_instDecidableLt(v_a_476_, v_b_477_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
static lean_object* _init_l_Rat_instLE(void){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = lean_box(0);
return v___x_480_;
}
}
uint8_t l_Rat_instDecidableLe(lean_object* v_a_481_, lean_object* v_b_482_){
_start:
{
uint8_t v___x_483_; 
v___x_483_ = l_Rat_blt(v_b_482_, v_a_481_);
if (v___x_483_ == 0)
{
uint8_t v___x_484_; 
v___x_484_ = 1;
return v___x_484_;
}
else
{
uint8_t v___x_485_; 
v___x_485_ = 0;
return v___x_485_;
}
}
}
LEAN_EXPORT void l_Rat_instDecidableLe_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_481_ = stack[0].m_obj;
lean_object* v_b_482_ = stack[1].m_obj;
uint8_t v_res_486_;
v_res_486_ = l_Rat_instDecidableLe(v_a_481_, v_b_482_);
stack->m_num = v_res_486_;
}
LEAN_EXPORT lean_object* l_Rat_instDecidableLe___boxed(lean_object* v_a_487_, lean_object* v_b_488_){
_start:
{
uint8_t v_res_489_; lean_object* v_r_490_; 
v_res_489_ = l_Rat_instDecidableLe(v_a_487_, v_b_488_);
v_r_490_ = lean_box(v_res_489_);
return v_r_490_;
}
}
LEAN_EXPORT lean_object* l_Rat_instMin___lam__0(lean_object* v_x_491_, lean_object* v_y_492_){
_start:
{
uint8_t v___x_493_; 
lean_inc_ref(v_y_492_);
lean_inc_ref(v_x_491_);
v___x_493_ = l_Rat_instDecidableLe(v_x_491_, v_y_492_);
if (v___x_493_ == 0)
{
lean_dec_ref(v_x_491_);
return v_y_492_;
}
else
{
lean_dec_ref(v_y_492_);
return v_x_491_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_instMax___lam__0(lean_object* v_x_496_, lean_object* v_y_497_){
_start:
{
uint8_t v___x_498_; 
lean_inc_ref(v_y_497_);
lean_inc_ref(v_x_496_);
v___x_498_ = l_Rat_instDecidableLe(v_x_496_, v_y_497_);
if (v___x_498_ == 0)
{
lean_dec_ref(v_y_497_);
return v_x_496_;
}
else
{
lean_dec_ref(v_x_496_);
return v_y_497_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_mul(lean_object* v_a_501_, lean_object* v_b_502_){
_start:
{
lean_object* v_num_503_; lean_object* v_den_504_; lean_object* v_num_505_; lean_object* v_den_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_525_; 
v_num_503_ = lean_ctor_get(v_a_501_, 0);
v_den_504_ = lean_ctor_get(v_a_501_, 1);
v_num_505_ = lean_ctor_get(v_b_502_, 0);
v_den_506_ = lean_ctor_get(v_b_502_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v_b_502_);
if (v_isSharedCheck_525_ == 0)
{
v___x_508_ = v_b_502_;
v_isShared_509_ = v_isSharedCheck_525_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_den_506_);
lean_inc(v_num_505_);
lean_dec(v_b_502_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_525_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v_g1_511_; lean_object* v___x_512_; lean_object* v_g2_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_510_ = lean_nat_abs(v_num_503_);
v_g1_511_ = lean_nat_gcd(v___x_510_, v_den_506_);
lean_dec(v___x_510_);
v___x_512_ = lean_nat_abs(v_num_505_);
v_g2_513_ = lean_nat_gcd(v___x_512_, v_den_504_);
lean_dec(v___x_512_);
lean_inc(v_g1_511_);
v___x_514_ = lean_nat_to_int(v_g1_511_);
v___x_515_ = lean_int_div_exact(v_num_503_, v___x_514_);
lean_dec(v___x_514_);
lean_inc(v_g2_513_);
v___x_516_ = lean_nat_to_int(v_g2_513_);
v___x_517_ = lean_int_div_exact(v_num_505_, v___x_516_);
lean_dec(v___x_516_);
lean_dec(v_num_505_);
v___x_518_ = lean_int_mul(v___x_515_, v___x_517_);
lean_dec(v___x_517_);
lean_dec(v___x_515_);
v___x_519_ = lean_nat_div_exact(v_den_504_, v_g2_513_);
lean_dec(v_g2_513_);
v___x_520_ = lean_nat_div_exact(v_den_506_, v_g1_511_);
lean_dec(v_g1_511_);
lean_dec(v_den_506_);
v___x_521_ = lean_nat_mul(v___x_519_, v___x_520_);
lean_dec(v___x_520_);
lean_dec(v___x_519_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v___x_521_);
lean_ctor_set(v___x_508_, 0, v___x_518_);
v___x_523_ = v___x_508_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_mul___boxed(lean_object* v_a_526_, lean_object* v_b_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Rat_mul(v_a_526_, v_b_527_);
lean_dec_ref(v_a_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Rat_inv(lean_object* v_a_531_){
_start:
{
lean_object* v_num_532_; lean_object* v_den_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v_num_532_ = lean_ctor_get(v_a_531_, 0);
v_den_533_ = lean_ctor_get(v_a_531_, 1);
v___x_534_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v___x_535_ = lean_int_dec_lt(v_num_532_, v___x_534_);
if (v___x_535_ == 0)
{
uint8_t v___x_536_; 
v___x_536_ = lean_int_dec_lt(v___x_534_, v_num_532_);
if (v___x_536_ == 0)
{
return v_a_531_;
}
else
{
lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_545_; 
lean_inc(v_den_533_);
lean_inc(v_num_532_);
v_isSharedCheck_545_ = !lean_is_exclusive(v_a_531_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; lean_object* v_unused_547_; 
v_unused_546_ = lean_ctor_get(v_a_531_, 1);
lean_dec(v_unused_546_);
v_unused_547_ = lean_ctor_get(v_a_531_, 0);
lean_dec(v_unused_547_);
v___x_538_ = v_a_531_;
v_isShared_539_ = v_isSharedCheck_545_;
goto v_resetjp_537_;
}
else
{
lean_dec(v_a_531_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_545_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_540_ = lean_nat_to_int(v_den_533_);
v___x_541_ = lean_nat_abs(v_num_532_);
lean_dec(v_num_532_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v___x_541_);
lean_ctor_set(v___x_538_, 0, v___x_540_);
v___x_543_ = v___x_538_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
else
{
lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_557_; 
lean_inc(v_den_533_);
lean_inc(v_num_532_);
v_isSharedCheck_557_ = !lean_is_exclusive(v_a_531_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; lean_object* v_unused_559_; 
v_unused_558_ = lean_ctor_get(v_a_531_, 1);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_a_531_, 0);
lean_dec(v_unused_559_);
v___x_549_ = v_a_531_;
v_isShared_550_ = v_isSharedCheck_557_;
goto v_resetjp_548_;
}
else
{
lean_dec(v_a_531_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_557_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_551_ = lean_nat_to_int(v_den_533_);
v___x_552_ = lean_int_neg(v___x_551_);
lean_dec(v___x_551_);
v___x_553_ = lean_nat_abs(v_num_532_);
lean_dec(v_num_532_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v___x_553_);
lean_ctor_set(v___x_549_, 0, v___x_552_);
v___x_555_ = v___x_549_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_pow(lean_object* v_q_562_, lean_object* v_n_563_){
_start:
{
lean_object* v_num_564_; lean_object* v_den_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_574_; 
v_num_564_ = lean_ctor_get(v_q_562_, 0);
v_den_565_ = lean_ctor_get(v_q_562_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v_q_562_);
if (v_isSharedCheck_574_ == 0)
{
v___x_567_ = v_q_562_;
v_isShared_568_ = v_isSharedCheck_574_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_den_565_);
lean_inc(v_num_564_);
lean_dec(v_q_562_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_574_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_569_ = l_Int_pow(v_num_564_, v_n_563_);
lean_dec(v_num_564_);
v___x_570_ = lean_nat_pow(v_den_565_, v_n_563_);
lean_dec(v_den_565_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v___x_570_);
lean_ctor_set(v___x_567_, 0, v___x_569_);
v___x_572_ = v___x_567_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_570_);
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
LEAN_EXPORT lean_object* l_Rat_pow___boxed(lean_object* v_q_575_, lean_object* v_n_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Rat_pow(v_q_575_, v_n_576_);
lean_dec(v_n_576_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Rat_zpow(lean_object* v_q_580_, lean_object* v_i_581_){
_start:
{
lean_object* v_intZero_582_; uint8_t v_isNeg_583_; 
v_intZero_582_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v_isNeg_583_ = lean_int_dec_lt(v_i_581_, v_intZero_582_);
if (v_isNeg_583_ == 0)
{
lean_object* v_a_584_; lean_object* v___x_585_; 
v_a_584_ = lean_nat_abs(v_i_581_);
v___x_585_ = l_Rat_pow(v_q_580_, v_a_584_);
lean_dec(v_a_584_);
return v___x_585_;
}
else
{
lean_object* v_abs_586_; lean_object* v_one_587_; lean_object* v_a_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_abs_586_ = lean_nat_abs(v_i_581_);
v_one_587_ = lean_unsigned_to_nat(1u);
v_a_588_ = lean_nat_sub(v_abs_586_, v_one_587_);
lean_dec(v_abs_586_);
v___x_589_ = lean_nat_add(v_a_588_, v_one_587_);
lean_dec(v_a_588_);
v___x_590_ = l_Rat_pow(v_q_580_, v___x_589_);
lean_dec(v___x_589_);
v___x_591_ = l_Rat_inv(v___x_590_);
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_zpow___boxed(lean_object* v_q_592_, lean_object* v_i_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Rat_zpow(v_q_592_, v_i_593_);
lean_dec(v_i_593_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Rat_div(lean_object* v_x1_597_, lean_object* v_x2_598_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = l_Rat_inv(v_x2_598_);
v___x_600_ = l_Rat_mul(v_x1_597_, v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Rat_div___boxed(lean_object* v_x1_601_, lean_object* v_x2_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Rat_div(v_x1_601_, v_x2_602_);
lean_dec_ref(v_x1_601_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Rat_add(lean_object* v_a_606_, lean_object* v_b_607_){
_start:
{
lean_object* v_num_608_; lean_object* v_den_609_; lean_object* v_num_610_; lean_object* v_den_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_647_; 
v_num_608_ = lean_ctor_get(v_a_606_, 0);
lean_inc(v_num_608_);
v_den_609_ = lean_ctor_get(v_a_606_, 1);
lean_inc(v_den_609_);
lean_dec_ref(v_a_606_);
v_num_610_ = lean_ctor_get(v_b_607_, 0);
v_den_611_ = lean_ctor_get(v_b_607_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_b_607_);
if (v_isSharedCheck_647_ == 0)
{
v___x_613_ = v_b_607_;
v_isShared_614_ = v_isSharedCheck_647_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_den_611_);
lean_inc(v_num_610_);
lean_dec(v_b_607_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_647_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_615_ = lean_nat_gcd(v_den_609_, v_den_611_);
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_nat_dec_eq(v___x_615_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v_den_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v_num_625_; lean_object* v___x_626_; lean_object* v_g1_627_; uint8_t v___x_628_; 
v___x_618_ = lean_nat_div(v_den_609_, v___x_615_);
lean_dec(v_den_609_);
v_den_619_ = lean_nat_mul(v___x_618_, v_den_611_);
v___x_620_ = lean_nat_div(v_den_611_, v___x_615_);
lean_dec(v_den_611_);
v___x_621_ = lean_nat_to_int(v___x_620_);
v___x_622_ = lean_int_mul(v_num_608_, v___x_621_);
lean_dec(v___x_621_);
lean_dec(v_num_608_);
v___x_623_ = lean_nat_to_int(v___x_618_);
v___x_624_ = lean_int_mul(v_num_610_, v___x_623_);
lean_dec(v___x_623_);
lean_dec(v_num_610_);
v_num_625_ = lean_int_add(v___x_622_, v___x_624_);
lean_dec(v___x_624_);
lean_dec(v___x_622_);
v___x_626_ = lean_nat_abs(v_num_625_);
v_g1_627_ = lean_nat_gcd(v___x_626_, v___x_615_);
lean_dec(v___x_615_);
lean_dec(v___x_626_);
v___x_628_ = lean_nat_dec_eq(v_g1_627_, v___x_616_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
lean_inc(v_g1_627_);
v___x_629_ = lean_nat_to_int(v_g1_627_);
v___x_630_ = lean_int_div_exact(v_num_625_, v___x_629_);
lean_dec(v___x_629_);
lean_dec(v_num_625_);
v___x_631_ = lean_nat_div_exact(v_den_619_, v_g1_627_);
lean_dec(v_g1_627_);
lean_dec(v_den_619_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___x_631_);
lean_ctor_set(v___x_613_, 0, v___x_630_);
v___x_633_ = v___x_613_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
else
{
lean_object* v___x_636_; 
lean_dec(v_g1_627_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v_den_619_);
lean_ctor_set(v___x_613_, 0, v_num_625_);
v___x_636_ = v___x_613_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_num_625_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_den_619_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
lean_dec(v___x_615_);
lean_inc(v_den_611_);
v___x_638_ = lean_nat_to_int(v_den_611_);
v___x_639_ = lean_int_mul(v_num_608_, v___x_638_);
lean_dec(v___x_638_);
lean_dec(v_num_608_);
lean_inc(v_den_609_);
v___x_640_ = lean_nat_to_int(v_den_609_);
v___x_641_ = lean_int_mul(v_num_610_, v___x_640_);
lean_dec(v___x_640_);
lean_dec(v_num_610_);
v___x_642_ = lean_int_add(v___x_639_, v___x_641_);
lean_dec(v___x_641_);
lean_dec(v___x_639_);
v___x_643_ = lean_nat_mul(v_den_609_, v_den_611_);
lean_dec(v_den_611_);
lean_dec(v_den_609_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___x_643_);
lean_ctor_set(v___x_613_, 0, v___x_642_);
v___x_645_ = v___x_613_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_neg(lean_object* v_a_650_){
_start:
{
lean_object* v_num_651_; lean_object* v_den_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_660_; 
v_num_651_ = lean_ctor_get(v_a_650_, 0);
v_den_652_ = lean_ctor_get(v_a_650_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v_a_650_);
if (v_isSharedCheck_660_ == 0)
{
v___x_654_ = v_a_650_;
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_den_652_);
lean_inc(v_num_651_);
lean_dec(v_a_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_656_ = lean_int_neg(v_num_651_);
lean_dec(v_num_651_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_den_652_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_sub(lean_object* v_a_663_, lean_object* v_b_664_){
_start:
{
lean_object* v_num_665_; lean_object* v_den_666_; lean_object* v_num_667_; lean_object* v_den_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_704_; 
v_num_665_ = lean_ctor_get(v_a_663_, 0);
lean_inc(v_num_665_);
v_den_666_ = lean_ctor_get(v_a_663_, 1);
lean_inc(v_den_666_);
lean_dec_ref(v_a_663_);
v_num_667_ = lean_ctor_get(v_b_664_, 0);
v_den_668_ = lean_ctor_get(v_b_664_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_b_664_);
if (v_isSharedCheck_704_ == 0)
{
v___x_670_ = v_b_664_;
v_isShared_671_ = v_isSharedCheck_704_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_den_668_);
lean_inc(v_num_667_);
lean_dec(v_b_664_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_704_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_672_ = lean_nat_gcd(v_den_666_, v_den_668_);
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_nat_dec_eq(v___x_672_, v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v_den_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v_num_682_; lean_object* v___x_683_; lean_object* v_g1_684_; uint8_t v___x_685_; 
v___x_675_ = lean_nat_div(v_den_666_, v___x_672_);
lean_dec(v_den_666_);
v_den_676_ = lean_nat_mul(v___x_675_, v_den_668_);
v___x_677_ = lean_nat_div(v_den_668_, v___x_672_);
lean_dec(v_den_668_);
v___x_678_ = lean_nat_to_int(v___x_677_);
v___x_679_ = lean_int_mul(v_num_665_, v___x_678_);
lean_dec(v___x_678_);
lean_dec(v_num_665_);
v___x_680_ = lean_nat_to_int(v___x_675_);
v___x_681_ = lean_int_mul(v_num_667_, v___x_680_);
lean_dec(v___x_680_);
lean_dec(v_num_667_);
v_num_682_ = lean_int_sub(v___x_679_, v___x_681_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
v___x_683_ = lean_nat_abs(v_num_682_);
v_g1_684_ = lean_nat_gcd(v___x_683_, v___x_672_);
lean_dec(v___x_672_);
lean_dec(v___x_683_);
v___x_685_ = lean_nat_dec_eq(v_g1_684_, v___x_673_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
lean_inc(v_g1_684_);
v___x_686_ = lean_nat_to_int(v_g1_684_);
v___x_687_ = lean_int_div_exact(v_num_682_, v___x_686_);
lean_dec(v___x_686_);
lean_dec(v_num_682_);
v___x_688_ = lean_nat_div_exact(v_den_676_, v_g1_684_);
lean_dec(v_g1_684_);
lean_dec(v_den_676_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v___x_688_);
lean_ctor_set(v___x_670_, 0, v___x_687_);
v___x_690_ = v___x_670_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
else
{
lean_object* v___x_693_; 
lean_dec(v_g1_684_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v_den_676_);
lean_ctor_set(v___x_670_, 0, v_num_682_);
v___x_693_ = v___x_670_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_num_682_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_den_676_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
lean_dec(v___x_672_);
lean_inc(v_den_668_);
v___x_695_ = lean_nat_to_int(v_den_668_);
v___x_696_ = lean_int_mul(v_num_665_, v___x_695_);
lean_dec(v___x_695_);
lean_dec(v_num_665_);
lean_inc(v_den_666_);
v___x_697_ = lean_nat_to_int(v_den_666_);
v___x_698_ = lean_int_mul(v_num_667_, v___x_697_);
lean_dec(v___x_697_);
lean_dec(v_num_667_);
v___x_699_ = lean_int_sub(v___x_696_, v___x_698_);
lean_dec(v___x_698_);
lean_dec(v___x_696_);
v___x_700_ = lean_nat_mul(v_den_666_, v_den_668_);
lean_dec(v_den_668_);
lean_dec(v_den_666_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v___x_700_);
lean_ctor_set(v___x_670_, 0, v___x_699_);
v___x_702_ = v___x_670_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_floor(lean_object* v_a_707_){
_start:
{
lean_object* v_num_708_; lean_object* v_den_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_num_708_ = lean_ctor_get(v_a_707_, 0);
lean_inc(v_num_708_);
v_den_709_ = lean_ctor_get(v_a_707_, 1);
lean_inc(v_den_709_);
lean_dec_ref(v_a_707_);
v___x_710_ = lean_unsigned_to_nat(1u);
v___x_711_ = lean_nat_dec_eq(v_den_709_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_nat_to_int(v_den_709_);
v___x_713_ = lean_int_ediv(v_num_708_, v___x_712_);
lean_dec(v___x_712_);
lean_dec(v_num_708_);
return v___x_713_;
}
else
{
lean_dec(v_den_709_);
return v_num_708_;
}
}
}
static lean_object* _init_l_Rat_ceil___closed__0(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_unsigned_to_nat(1u);
v___x_715_ = lean_nat_to_int(v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Rat_ceil(lean_object* v_a_716_){
_start:
{
lean_object* v_num_717_; lean_object* v_den_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v_num_717_ = lean_ctor_get(v_a_716_, 0);
lean_inc(v_num_717_);
v_den_718_ = lean_ctor_get(v_a_716_, 1);
lean_inc(v_den_718_);
lean_dec_ref(v_a_716_);
v___x_719_ = lean_unsigned_to_nat(1u);
v___x_720_ = lean_nat_dec_eq(v_den_718_, v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_721_ = lean_nat_to_int(v_den_718_);
v___x_722_ = lean_int_ediv(v_num_717_, v___x_721_);
lean_dec(v___x_721_);
lean_dec(v_num_717_);
v___x_723_ = lean_obj_once(&l_Rat_ceil___closed__0, &l_Rat_ceil___closed__0_once, _init_l_Rat_ceil___closed__0);
v___x_724_ = lean_int_add(v___x_722_, v___x_723_);
lean_dec(v___x_722_);
return v___x_724_;
}
else
{
lean_dec(v_den_718_);
return v_num_717_;
}
}
}
static lean_object* _init_l_Rat_abs___closed__0(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_unsigned_to_nat(0u);
v___x_726_ = l_Nat_cast___at___00Rat_ofScientific_spec__0(v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Rat_abs(lean_object* v_a_727_){
_start:
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = lean_obj_once(&l_Rat_abs___closed__0, &l_Rat_abs___closed__0_once, _init_l_Rat_abs___closed__0);
lean_inc_ref(v_a_727_);
v___x_729_ = l_Rat_instDecidableLe(v___x_728_, v_a_727_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; 
v___x_730_ = l_Rat_neg(v_a_727_);
return v___x_730_;
}
else
{
return v_a_727_;
}
}
}
lean_object* runtime_initialize_Init_Data_Nat_Coprime(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_OfScientific_Basic(uint8_t builtin);
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Rat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Nat_Coprime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_OfScientific_Basic(builtin);
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
lean_object* initialize_Init_Data_OfScientific_Basic(uint8_t builtin);
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
res = initialize_Init_Data_OfScientific_Basic(builtin);
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
