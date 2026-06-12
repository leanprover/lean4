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
LEAN_EXPORT lean_object* l_instToStringRat___lam__0(lean_object* v_a_134_){
_start:
{
lean_object* v_num_135_; lean_object* v_den_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v_num_135_ = lean_ctor_get(v_a_134_, 0);
lean_inc(v_num_135_);
v_den_136_ = lean_ctor_get(v_a_134_, 1);
lean_inc(v_den_136_);
lean_dec_ref(v_a_134_);
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = lean_nat_dec_eq(v_den_136_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_139_ = l_Int_repr(v_num_135_);
lean_dec(v_num_135_);
v___x_140_ = ((lean_object*)(l_instToStringRat___lam__0___closed__0));
v___x_141_ = lean_string_append(v___x_139_, v___x_140_);
v___x_142_ = l_Nat_reprFast(v_den_136_);
v___x_143_ = lean_string_append(v___x_141_, v___x_142_);
lean_dec_ref(v___x_142_);
return v___x_143_;
}
else
{
lean_object* v___x_144_; 
lean_dec(v_den_136_);
v___x_144_ = l_Int_repr(v_num_135_);
lean_dec(v_num_135_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_instReprRat___lam__0(lean_object* v_a_149_, lean_object* v_x_150_){
_start:
{
lean_object* v_num_151_; lean_object* v_den_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_num_151_ = lean_ctor_get(v_a_149_, 0);
lean_inc(v_num_151_);
v_den_152_ = lean_ctor_get(v_a_149_, 1);
lean_inc(v_den_152_);
lean_dec_ref(v_a_149_);
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = lean_nat_dec_eq(v_den_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_155_ = ((lean_object*)(l_instReprRat___lam__0___closed__0));
v___x_156_ = l_Int_repr(v_num_151_);
lean_dec(v_num_151_);
v___x_157_ = lean_string_append(v___x_155_, v___x_156_);
lean_dec_ref(v___x_156_);
v___x_158_ = ((lean_object*)(l_instReprRat___lam__0___closed__1));
v___x_159_ = lean_string_append(v___x_157_, v___x_158_);
v___x_160_ = l_Nat_reprFast(v_den_152_);
v___x_161_ = lean_string_append(v___x_159_, v___x_160_);
lean_dec_ref(v___x_160_);
v___x_162_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
lean_dec(v_den_152_);
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v___x_165_ = lean_int_dec_lt(v_num_151_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = l_Int_repr(v_num_151_);
lean_dec(v_num_151_);
v___x_167_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = l_Int_repr(v_num_151_);
lean_dec(v_num_151_);
v___x_169_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
v___x_170_ = l_Repr_addAppParen(v___x_169_, v___x_163_);
return v___x_170_;
}
}
}
}
LEAN_EXPORT lean_object* l_instReprRat___lam__0___boxed(lean_object* v_a_171_, lean_object* v_x_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_instReprRat___lam__0(v_a_171_, v_x_172_);
lean_dec(v_x_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Rat_maybeNormalize___redArg(lean_object* v_num_176_, lean_object* v_den_177_, lean_object* v_g_178_){
_start:
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = lean_nat_dec_eq(v_g_178_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
lean_inc(v_g_178_);
v___x_181_ = lean_nat_to_int(v_g_178_);
v___x_182_ = lean_int_div_exact(v_num_176_, v___x_181_);
lean_dec(v___x_181_);
lean_dec(v_num_176_);
v___x_183_ = lean_nat_div_exact(v_den_177_, v_g_178_);
lean_dec(v_g_178_);
lean_dec(v_den_177_);
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
return v___x_184_;
}
else
{
lean_object* v___x_185_; 
lean_dec(v_g_178_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v_num_176_);
lean_ctor_set(v___x_185_, 1, v_den_177_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_maybeNormalize(lean_object* v_num_186_, lean_object* v_den_187_, lean_object* v_g_188_, lean_object* v_dvd__num_189_, lean_object* v_dvd__den_190_, lean_object* v_den__nz_191_, lean_object* v_reduced_192_){
_start:
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(1u);
v___x_194_ = lean_nat_dec_eq(v_g_188_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
lean_inc(v_g_188_);
v___x_195_ = lean_nat_to_int(v_g_188_);
v___x_196_ = lean_int_div_exact(v_num_186_, v___x_195_);
lean_dec(v___x_195_);
lean_dec(v_num_186_);
v___x_197_ = lean_nat_div_exact(v_den_187_, v_g_188_);
lean_dec(v_g_188_);
lean_dec(v_den_187_);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
return v___x_198_;
}
else
{
lean_object* v___x_199_; 
lean_dec(v_g_188_);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v_num_186_);
lean_ctor_set(v___x_199_, 1, v_den_187_);
return v___x_199_;
}
}
}
static lean_object* _init_l_Rat_normalize___auto__1(void){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Rat_den__nz___autoParam___closed__26, &l_Rat_den__nz___autoParam___closed__26_once, _init_l_Rat_den__nz___autoParam___closed__26);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Rat_normalize___redArg(lean_object* v_num_201_, lean_object* v_den_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_203_ = lean_nat_abs(v_num_201_);
v___x_204_ = lean_nat_gcd(v___x_203_, v_den_202_);
lean_dec(v___x_203_);
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = lean_nat_dec_eq(v___x_204_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
lean_inc(v___x_204_);
v___x_207_ = lean_nat_to_int(v___x_204_);
v___x_208_ = lean_int_div_exact(v_num_201_, v___x_207_);
lean_dec(v___x_207_);
lean_dec(v_num_201_);
v___x_209_ = lean_nat_div_exact(v_den_202_, v___x_204_);
lean_dec(v___x_204_);
lean_dec(v_den_202_);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
return v___x_210_;
}
else
{
lean_object* v___x_211_; 
lean_dec(v___x_204_);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v_num_201_);
lean_ctor_set(v___x_211_, 1, v_den_202_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_normalize(lean_object* v_num_212_, lean_object* v_den_213_, lean_object* v_den__nz_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_215_ = lean_nat_abs(v_num_212_);
v___x_216_ = lean_nat_gcd(v___x_215_, v_den_213_);
lean_dec(v___x_215_);
v___x_217_ = lean_unsigned_to_nat(1u);
v___x_218_ = lean_nat_dec_eq(v___x_216_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
lean_inc(v___x_216_);
v___x_219_ = lean_nat_to_int(v___x_216_);
v___x_220_ = lean_int_div_exact(v_num_212_, v___x_219_);
lean_dec(v___x_219_);
lean_dec(v_num_212_);
v___x_221_ = lean_nat_div_exact(v_den_213_, v___x_216_);
lean_dec(v___x_216_);
lean_dec(v_den_213_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; 
lean_dec(v___x_216_);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v_num_212_);
lean_ctor_set(v___x_223_, 1, v_den_213_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00mkRat_spec__0(lean_object* v_a_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = lean_nat_to_int(v_a_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_mkRat(lean_object* v_num_226_, lean_object* v_den_227_){
_start:
{
lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_nat_dec_eq(v_den_227_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_230_ = lean_nat_abs(v_num_226_);
v___x_231_ = lean_nat_gcd(v___x_230_, v_den_227_);
lean_dec(v___x_230_);
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = lean_nat_dec_eq(v___x_231_, v___x_232_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
lean_inc(v___x_231_);
v___x_234_ = lean_nat_to_int(v___x_231_);
v___x_235_ = lean_int_div_exact(v_num_226_, v___x_234_);
lean_dec(v___x_234_);
lean_dec(v_num_226_);
v___x_236_ = lean_nat_div_exact(v_den_227_, v___x_231_);
lean_dec(v___x_231_);
lean_dec(v_den_227_);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
return v___x_237_;
}
else
{
lean_object* v___x_238_; 
lean_dec(v___x_231_);
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v_num_226_);
lean_ctor_set(v___x_238_, 1, v_den_227_);
return v___x_238_;
}
}
else
{
lean_object* v___x_239_; 
lean_dec(v_den_227_);
lean_dec(v_num_226_);
v___x_239_ = lean_obj_once(&l_instInhabitedRat___closed__0, &l_instInhabitedRat___closed__0_once, _init_l_instInhabitedRat___closed__0);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_ofInt(lean_object* v_num_240_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_242_, 0, v_num_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Rat_instNatCast___lam__0(lean_object* v_n_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_nat_to_int(v_n_243_);
v___x_245_ = l_Rat_ofInt(v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Rat_instOfNat(lean_object* v_n_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Rat_instNatCast___lam__0(v_n_250_);
return v___x_251_;
}
}
LEAN_EXPORT uint8_t l_Rat_isInt(lean_object* v_a_252_){
_start:
{
lean_object* v_den_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_den_253_ = lean_ctor_get(v_a_252_, 1);
v___x_254_ = lean_unsigned_to_nat(1u);
v___x_255_ = lean_nat_dec_eq(v_den_253_, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Rat_isInt___boxed(lean_object* v_a_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Rat_isInt(v_a_256_);
lean_dec_ref(v_a_256_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT lean_object* l_Rat_divInt(lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
lean_object* v_natZero_261_; lean_object* v_intZero_262_; uint8_t v_isNeg_263_; 
v_natZero_261_ = lean_unsigned_to_nat(0u);
v_intZero_262_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v_isNeg_263_ = lean_int_dec_lt(v_x_260_, v_intZero_262_);
if (v_isNeg_263_ == 0)
{
lean_object* v_a_264_; uint8_t v___x_265_; 
v_a_264_ = lean_nat_abs(v_x_260_);
v___x_265_ = lean_nat_dec_eq(v_a_264_, v_natZero_261_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_266_ = lean_nat_abs(v_x_259_);
v___x_267_ = lean_nat_gcd(v___x_266_, v_a_264_);
lean_dec(v___x_266_);
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_dec_eq(v___x_267_, v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
lean_inc(v___x_267_);
v___x_270_ = lean_nat_to_int(v___x_267_);
v___x_271_ = lean_int_div_exact(v_x_259_, v___x_270_);
lean_dec(v___x_270_);
lean_dec(v_x_259_);
v___x_272_ = lean_nat_div_exact(v_a_264_, v___x_267_);
lean_dec(v___x_267_);
lean_dec(v_a_264_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; 
lean_dec(v___x_267_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v_x_259_);
lean_ctor_set(v___x_274_, 1, v_a_264_);
return v___x_274_;
}
}
else
{
lean_object* v___x_275_; 
lean_dec(v_a_264_);
lean_dec(v_x_259_);
v___x_275_ = lean_obj_once(&l_instInhabitedRat___closed__0, &l_instInhabitedRat___closed__0_once, _init_l_instInhabitedRat___closed__0);
return v___x_275_;
}
}
else
{
lean_object* v_abs_276_; lean_object* v_one_277_; lean_object* v_a_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_abs_276_ = lean_nat_abs(v_x_260_);
v_one_277_ = lean_unsigned_to_nat(1u);
v_a_278_ = lean_nat_sub(v_abs_276_, v_one_277_);
lean_dec(v_abs_276_);
v___x_279_ = lean_int_neg(v_x_259_);
lean_dec(v_x_259_);
v___x_280_ = lean_nat_add(v_a_278_, v_one_277_);
lean_dec(v_a_278_);
v___x_281_ = lean_nat_abs(v___x_279_);
v___x_282_ = lean_nat_gcd(v___x_281_, v___x_280_);
lean_dec(v___x_281_);
v___x_283_ = lean_nat_dec_eq(v___x_282_, v_one_277_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
lean_inc(v___x_282_);
v___x_284_ = lean_nat_to_int(v___x_282_);
v___x_285_ = lean_int_div_exact(v___x_279_, v___x_284_);
lean_dec(v___x_284_);
lean_dec(v___x_279_);
v___x_286_ = lean_nat_div_exact(v___x_280_, v___x_282_);
lean_dec(v___x_282_);
lean_dec(v___x_280_);
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
return v___x_287_;
}
else
{
lean_object* v___x_288_; 
lean_dec(v___x_282_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_279_);
lean_ctor_set(v___x_288_, 1, v___x_280_);
return v___x_288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_divInt___boxed(lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Rat_divInt(v_x_289_, v_x_290_);
lean_dec(v_x_290_);
return v_res_291_;
}
}
static lean_object* _init_l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__3));
v___x_327_ = l_String_toRawSubstring_x27(v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1(lean_object* v_x_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = ((lean_object*)(l_Rat_term___x2f_x2e___00__closed__2));
lean_inc(v_x_343_);
v___x_347_ = l_Lean_Syntax_isOfKind(v_x_343_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec(v_x_343_);
v___x_348_ = lean_box(1);
v___x_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v_a_345_);
return v___x_349_;
}
else
{
lean_object* v_quotContext_350_; lean_object* v_currMacroScope_351_; lean_object* v_ref_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_quotContext_350_ = lean_ctor_get(v_a_344_, 1);
v_currMacroScope_351_ = lean_ctor_get(v_a_344_, 2);
v_ref_352_ = lean_ctor_get(v_a_344_, 5);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = l_Lean_Syntax_getArg(v_x_343_, v___x_353_);
v___x_355_ = lean_unsigned_to_nat(2u);
v___x_356_ = l_Lean_Syntax_getArg(v_x_343_, v___x_355_);
lean_dec(v_x_343_);
v___x_357_ = 0;
v___x_358_ = l_Lean_SourceInfo_fromRef(v_ref_352_, v___x_357_);
v___x_359_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2));
v___x_360_ = lean_obj_once(&l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4, &l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4_once, _init_l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__4);
v___x_361_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__6));
lean_inc(v_currMacroScope_351_);
lean_inc(v_quotContext_350_);
v___x_362_ = l_Lean_addMacroScope(v_quotContext_350_, v___x_361_, v_currMacroScope_351_);
v___x_363_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__10));
lean_inc_n(v___x_358_, 2);
v___x_364_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_364_, 0, v___x_358_);
lean_ctor_set(v___x_364_, 1, v___x_360_);
lean_ctor_set(v___x_364_, 2, v___x_362_);
lean_ctor_set(v___x_364_, 3, v___x_363_);
v___x_365_ = ((lean_object*)(l_Rat_den__nz___autoParam___closed__9));
v___x_366_ = l_Lean_Syntax_node2(v___x_358_, v___x_365_, v___x_354_, v___x_356_);
v___x_367_ = l_Lean_Syntax_node2(v___x_358_, v___x_359_, v___x_364_, v___x_366_);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v_a_345_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___boxed(lean_object* v_x_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1(v_x_369_, v_a_370_, v_a_371_);
lean_dec_ref(v_a_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1(lean_object* v_x_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______macroRules__Rat__term___x2f_x2e____1___closed__2));
lean_inc(v_x_376_);
v___x_380_ = l_Lean_Syntax_isOfKind(v_x_376_, v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec(v_x_376_);
v___x_381_ = lean_box(0);
v___x_382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v_a_378_);
return v___x_382_;
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = l_Lean_Syntax_getArg(v_x_376_, v___x_383_);
v___x_385_ = ((lean_object*)(l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___closed__1));
lean_inc(v___x_384_);
v___x_386_ = l_Lean_Syntax_isOfKind(v___x_384_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec(v___x_384_);
lean_dec(v_x_376_);
v___x_387_ = lean_box(0);
v___x_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v_a_378_);
return v___x_388_;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = l_Lean_Syntax_getArg(v_x_376_, v___x_389_);
lean_dec(v_x_376_);
v___x_391_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_390_);
v___x_392_ = l_Lean_Syntax_matchesNull(v___x_390_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec(v___x_390_);
lean_dec(v___x_384_);
v___x_393_ = lean_box(0);
v___x_394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v_a_378_);
return v___x_394_;
}
else
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v_ref_397_; uint8_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_395_ = l_Lean_Syntax_getArg(v___x_390_, v___x_383_);
v___x_396_ = l_Lean_Syntax_getArg(v___x_390_, v___x_389_);
lean_dec(v___x_390_);
v_ref_397_ = l_Lean_replaceRef(v___x_384_, v_a_377_);
lean_dec(v___x_384_);
v___x_398_ = 0;
v___x_399_ = l_Lean_SourceInfo_fromRef(v_ref_397_, v___x_398_);
lean_dec(v_ref_397_);
v___x_400_ = ((lean_object*)(l_Rat_term___x2f_x2e___00__closed__2));
v___x_401_ = ((lean_object*)(l_Rat_term___x2f_x2e___00__closed__5));
lean_inc(v___x_399_);
v___x_402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_399_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = l_Lean_Syntax_node3(v___x_399_, v___x_400_, v___x_395_, v___x_402_, v___x_396_);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v_a_378_);
return v___x_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1___boxed(lean_object* v_x_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Rat___aux__Init__Data__Rat__Basic______unexpand__Rat__divInt__1(v_x_405_, v_a_406_, v_a_407_);
lean_dec(v_a_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Rat_ofScientific_spec__0(lean_object* v_a_409_){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = lean_nat_to_int(v_a_409_);
v___x_411_ = l_Rat_ofInt(v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Rat_ofScientific(lean_object* v_m_412_, uint8_t v_s_413_, lean_object* v_e_414_){
_start:
{
if (v_s_413_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_415_ = lean_unsigned_to_nat(10u);
v___x_416_ = lean_nat_pow(v___x_415_, v_e_414_);
v___x_417_ = lean_nat_mul(v_m_412_, v___x_416_);
lean_dec(v___x_416_);
lean_dec(v_m_412_);
v___x_418_ = l_Nat_cast___at___00Rat_ofScientific_spec__0(v___x_417_);
return v___x_418_;
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_419_ = lean_nat_to_int(v_m_412_);
v___x_420_ = lean_unsigned_to_nat(10u);
v___x_421_ = lean_nat_pow(v___x_420_, v_e_414_);
v___x_422_ = lean_nat_abs(v___x_419_);
v___x_423_ = lean_nat_gcd(v___x_422_, v___x_421_);
lean_dec(v___x_422_);
v___x_424_ = lean_unsigned_to_nat(1u);
v___x_425_ = lean_nat_dec_eq(v___x_423_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
lean_inc(v___x_423_);
v___x_426_ = lean_nat_to_int(v___x_423_);
v___x_427_ = lean_int_div_exact(v___x_419_, v___x_426_);
lean_dec(v___x_426_);
lean_dec(v___x_419_);
v___x_428_ = lean_nat_div_exact(v___x_421_, v___x_423_);
lean_dec(v___x_423_);
lean_dec(v___x_421_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_427_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; 
lean_dec(v___x_423_);
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_419_);
lean_ctor_set(v___x_430_, 1, v___x_421_);
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_ofScientific___boxed(lean_object* v_m_431_, lean_object* v_s_432_, lean_object* v_e_433_){
_start:
{
uint8_t v_s_boxed_434_; lean_object* v_res_435_; 
v_s_boxed_434_ = lean_unbox(v_s_432_);
v_res_435_ = l_Rat_ofScientific(v_m_431_, v_s_boxed_434_, v_e_433_);
lean_dec(v_e_433_);
return v_res_435_;
}
}
LEAN_EXPORT uint8_t l_Rat_blt(lean_object* v_a_438_, lean_object* v_b_439_){
_start:
{
lean_object* v_num_440_; lean_object* v_den_441_; uint8_t v___y_443_; uint8_t v___y_444_; lean_object* v___x_452_; uint8_t v___y_454_; uint8_t v___x_461_; 
v_num_440_ = lean_ctor_get(v_a_438_, 0);
lean_inc(v_num_440_);
v_den_441_ = lean_ctor_get(v_a_438_, 1);
lean_inc(v_den_441_);
lean_dec_ref(v_a_438_);
v___x_452_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v___x_461_ = lean_int_dec_lt(v_num_440_, v___x_452_);
if (v___x_461_ == 0)
{
v___y_454_ = v___x_461_;
goto v___jp_453_;
}
else
{
lean_object* v_num_462_; uint8_t v___x_463_; 
v_num_462_ = lean_ctor_get(v_b_439_, 0);
v___x_463_ = lean_int_dec_le(v___x_452_, v_num_462_);
v___y_454_ = v___x_463_;
goto v___jp_453_;
}
v___jp_442_:
{
if (v___y_444_ == 0)
{
lean_object* v_num_445_; lean_object* v_den_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v_num_445_ = lean_ctor_get(v_b_439_, 0);
lean_inc(v_num_445_);
v_den_446_ = lean_ctor_get(v_b_439_, 1);
lean_inc(v_den_446_);
lean_dec_ref(v_b_439_);
v___x_447_ = lean_nat_to_int(v_den_446_);
v___x_448_ = lean_int_mul(v_num_440_, v___x_447_);
lean_dec(v___x_447_);
lean_dec(v_num_440_);
v___x_449_ = lean_nat_to_int(v_den_441_);
v___x_450_ = lean_int_mul(v_num_445_, v___x_449_);
lean_dec(v___x_449_);
lean_dec(v_num_445_);
v___x_451_ = lean_int_dec_lt(v___x_448_, v___x_450_);
lean_dec(v___x_450_);
lean_dec(v___x_448_);
return v___x_451_;
}
else
{
lean_dec(v_den_441_);
lean_dec(v_num_440_);
lean_dec_ref(v_b_439_);
return v___y_443_;
}
}
v___jp_453_:
{
if (v___y_454_ == 0)
{
uint8_t v___x_455_; 
v___x_455_ = lean_int_dec_eq(v_num_440_, v___x_452_);
if (v___x_455_ == 0)
{
uint8_t v___x_456_; 
v___x_456_ = lean_int_dec_lt(v___x_452_, v_num_440_);
if (v___x_456_ == 0)
{
v___y_443_ = v___y_454_;
v___y_444_ = v___x_456_;
goto v___jp_442_;
}
else
{
lean_object* v_num_457_; uint8_t v___x_458_; 
v_num_457_ = lean_ctor_get(v_b_439_, 0);
v___x_458_ = lean_int_dec_le(v_num_457_, v___x_452_);
v___y_443_ = v___y_454_;
v___y_444_ = v___x_458_;
goto v___jp_442_;
}
}
else
{
lean_object* v_num_459_; uint8_t v___x_460_; 
lean_dec(v_den_441_);
lean_dec(v_num_440_);
v_num_459_ = lean_ctor_get(v_b_439_, 0);
lean_inc(v_num_459_);
lean_dec_ref(v_b_439_);
v___x_460_ = lean_int_dec_lt(v___x_452_, v_num_459_);
lean_dec(v_num_459_);
return v___x_460_;
}
}
else
{
lean_dec(v_den_441_);
lean_dec(v_num_440_);
lean_dec_ref(v_b_439_);
return v___y_454_;
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_blt___boxed(lean_object* v_a_464_, lean_object* v_b_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Rat_blt(v_a_464_, v_b_465_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
static lean_object* _init_l_Rat_instLT(void){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = lean_box(0);
return v___x_468_;
}
}
LEAN_EXPORT uint8_t l_Rat_instDecidableLt(lean_object* v_a_469_, lean_object* v_b_470_){
_start:
{
uint8_t v___x_471_; 
v___x_471_ = l_Rat_blt(v_a_469_, v_b_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Rat_instDecidableLt___boxed(lean_object* v_a_472_, lean_object* v_b_473_){
_start:
{
uint8_t v_res_474_; lean_object* v_r_475_; 
v_res_474_ = l_Rat_instDecidableLt(v_a_472_, v_b_473_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
static lean_object* _init_l_Rat_instLE(void){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = lean_box(0);
return v___x_476_;
}
}
LEAN_EXPORT uint8_t l_Rat_instDecidableLe(lean_object* v_a_477_, lean_object* v_b_478_){
_start:
{
uint8_t v___x_479_; 
v___x_479_ = l_Rat_blt(v_b_478_, v_a_477_);
if (v___x_479_ == 0)
{
uint8_t v___x_480_; 
v___x_480_ = 1;
return v___x_480_;
}
else
{
uint8_t v___x_481_; 
v___x_481_ = 0;
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_instDecidableLe___boxed(lean_object* v_a_482_, lean_object* v_b_483_){
_start:
{
uint8_t v_res_484_; lean_object* v_r_485_; 
v_res_484_ = l_Rat_instDecidableLe(v_a_482_, v_b_483_);
v_r_485_ = lean_box(v_res_484_);
return v_r_485_;
}
}
LEAN_EXPORT lean_object* l_Rat_instMin___lam__0(lean_object* v_x_486_, lean_object* v_y_487_){
_start:
{
uint8_t v___x_488_; 
lean_inc_ref(v_y_487_);
lean_inc_ref(v_x_486_);
v___x_488_ = l_Rat_instDecidableLe(v_x_486_, v_y_487_);
if (v___x_488_ == 0)
{
lean_dec_ref(v_x_486_);
return v_y_487_;
}
else
{
lean_dec_ref(v_y_487_);
return v_x_486_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_instMax___lam__0(lean_object* v_x_491_, lean_object* v_y_492_){
_start:
{
uint8_t v___x_493_; 
lean_inc_ref(v_y_492_);
lean_inc_ref(v_x_491_);
v___x_493_ = l_Rat_instDecidableLe(v_x_491_, v_y_492_);
if (v___x_493_ == 0)
{
lean_dec_ref(v_y_492_);
return v_x_491_;
}
else
{
lean_dec_ref(v_x_491_);
return v_y_492_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_mul(lean_object* v_a_496_, lean_object* v_b_497_){
_start:
{
lean_object* v_num_498_; lean_object* v_den_499_; lean_object* v_num_500_; lean_object* v_den_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_520_; 
v_num_498_ = lean_ctor_get(v_a_496_, 0);
v_den_499_ = lean_ctor_get(v_a_496_, 1);
v_num_500_ = lean_ctor_get(v_b_497_, 0);
v_den_501_ = lean_ctor_get(v_b_497_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_b_497_);
if (v_isSharedCheck_520_ == 0)
{
v___x_503_ = v_b_497_;
v_isShared_504_ = v_isSharedCheck_520_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_den_501_);
lean_inc(v_num_500_);
lean_dec(v_b_497_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_520_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v_g1_506_; lean_object* v___x_507_; lean_object* v_g2_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_505_ = lean_nat_abs(v_num_498_);
v_g1_506_ = lean_nat_gcd(v___x_505_, v_den_501_);
lean_dec(v___x_505_);
v___x_507_ = lean_nat_abs(v_num_500_);
v_g2_508_ = lean_nat_gcd(v___x_507_, v_den_499_);
lean_dec(v___x_507_);
lean_inc(v_g1_506_);
v___x_509_ = lean_nat_to_int(v_g1_506_);
v___x_510_ = lean_int_div_exact(v_num_498_, v___x_509_);
lean_dec(v___x_509_);
lean_inc(v_g2_508_);
v___x_511_ = lean_nat_to_int(v_g2_508_);
v___x_512_ = lean_int_div_exact(v_num_500_, v___x_511_);
lean_dec(v___x_511_);
lean_dec(v_num_500_);
v___x_513_ = lean_int_mul(v___x_510_, v___x_512_);
lean_dec(v___x_512_);
lean_dec(v___x_510_);
v___x_514_ = lean_nat_div_exact(v_den_499_, v_g2_508_);
lean_dec(v_g2_508_);
v___x_515_ = lean_nat_div_exact(v_den_501_, v_g1_506_);
lean_dec(v_g1_506_);
lean_dec(v_den_501_);
v___x_516_ = lean_nat_mul(v___x_514_, v___x_515_);
lean_dec(v___x_515_);
lean_dec(v___x_514_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_516_);
lean_ctor_set(v___x_503_, 0, v___x_513_);
v___x_518_ = v___x_503_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_mul___boxed(lean_object* v_a_521_, lean_object* v_b_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Rat_mul(v_a_521_, v_b_522_);
lean_dec_ref(v_a_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Rat_inv(lean_object* v_a_526_){
_start:
{
lean_object* v_num_527_; lean_object* v_den_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v_num_527_ = lean_ctor_get(v_a_526_, 0);
v_den_528_ = lean_ctor_get(v_a_526_, 1);
v___x_529_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v___x_530_ = lean_int_dec_lt(v_num_527_, v___x_529_);
if (v___x_530_ == 0)
{
uint8_t v___x_531_; 
v___x_531_ = lean_int_dec_lt(v___x_529_, v_num_527_);
if (v___x_531_ == 0)
{
return v_a_526_;
}
else
{
lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_540_; 
lean_inc(v_den_528_);
lean_inc(v_num_527_);
v_isSharedCheck_540_ = !lean_is_exclusive(v_a_526_);
if (v_isSharedCheck_540_ == 0)
{
lean_object* v_unused_541_; lean_object* v_unused_542_; 
v_unused_541_ = lean_ctor_get(v_a_526_, 1);
lean_dec(v_unused_541_);
v_unused_542_ = lean_ctor_get(v_a_526_, 0);
lean_dec(v_unused_542_);
v___x_533_ = v_a_526_;
v_isShared_534_ = v_isSharedCheck_540_;
goto v_resetjp_532_;
}
else
{
lean_dec(v_a_526_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_540_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_535_ = lean_nat_to_int(v_den_528_);
v___x_536_ = lean_nat_abs(v_num_527_);
lean_dec(v_num_527_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 1, v___x_536_);
lean_ctor_set(v___x_533_, 0, v___x_535_);
v___x_538_ = v___x_533_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_552_; 
lean_inc(v_den_528_);
lean_inc(v_num_527_);
v_isSharedCheck_552_ = !lean_is_exclusive(v_a_526_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; lean_object* v_unused_554_; 
v_unused_553_ = lean_ctor_get(v_a_526_, 1);
lean_dec(v_unused_553_);
v_unused_554_ = lean_ctor_get(v_a_526_, 0);
lean_dec(v_unused_554_);
v___x_544_ = v_a_526_;
v_isShared_545_ = v_isSharedCheck_552_;
goto v_resetjp_543_;
}
else
{
lean_dec(v_a_526_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_552_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_546_ = lean_nat_to_int(v_den_528_);
v___x_547_ = lean_int_neg(v___x_546_);
lean_dec(v___x_546_);
v___x_548_ = lean_nat_abs(v_num_527_);
lean_dec(v_num_527_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 1, v___x_548_);
lean_ctor_set(v___x_544_, 0, v___x_547_);
v___x_550_ = v___x_544_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_pow(lean_object* v_q_557_, lean_object* v_n_558_){
_start:
{
lean_object* v_num_559_; lean_object* v_den_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_569_; 
v_num_559_ = lean_ctor_get(v_q_557_, 0);
v_den_560_ = lean_ctor_get(v_q_557_, 1);
v_isSharedCheck_569_ = !lean_is_exclusive(v_q_557_);
if (v_isSharedCheck_569_ == 0)
{
v___x_562_ = v_q_557_;
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_den_560_);
lean_inc(v_num_559_);
lean_dec(v_q_557_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_569_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_564_ = l_Int_pow(v_num_559_, v_n_558_);
lean_dec(v_num_559_);
v___x_565_ = lean_nat_pow(v_den_560_, v_n_558_);
lean_dec(v_den_560_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___x_565_);
lean_ctor_set(v___x_562_, 0, v___x_564_);
v___x_567_ = v___x_562_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_pow___boxed(lean_object* v_q_570_, lean_object* v_n_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Rat_pow(v_q_570_, v_n_571_);
lean_dec(v_n_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Rat_zpow(lean_object* v_q_575_, lean_object* v_i_576_){
_start:
{
lean_object* v_intZero_577_; uint8_t v_isNeg_578_; 
v_intZero_577_ = lean_obj_once(&l_instHashableRat_hash___closed__0, &l_instHashableRat_hash___closed__0_once, _init_l_instHashableRat_hash___closed__0);
v_isNeg_578_ = lean_int_dec_lt(v_i_576_, v_intZero_577_);
if (v_isNeg_578_ == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; 
v_a_579_ = lean_nat_abs(v_i_576_);
v___x_580_ = l_Rat_pow(v_q_575_, v_a_579_);
lean_dec(v_a_579_);
return v___x_580_;
}
else
{
lean_object* v_abs_581_; lean_object* v_one_582_; lean_object* v_a_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_abs_581_ = lean_nat_abs(v_i_576_);
v_one_582_ = lean_unsigned_to_nat(1u);
v_a_583_ = lean_nat_sub(v_abs_581_, v_one_582_);
lean_dec(v_abs_581_);
v___x_584_ = lean_nat_add(v_a_583_, v_one_582_);
lean_dec(v_a_583_);
v___x_585_ = l_Rat_pow(v_q_575_, v___x_584_);
lean_dec(v___x_584_);
v___x_586_ = l_Rat_inv(v___x_585_);
return v___x_586_;
}
}
}
LEAN_EXPORT lean_object* l_Rat_zpow___boxed(lean_object* v_q_587_, lean_object* v_i_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Rat_zpow(v_q_587_, v_i_588_);
lean_dec(v_i_588_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Rat_div(lean_object* v_x1_592_, lean_object* v_x2_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = l_Rat_inv(v_x2_593_);
v___x_595_ = l_Rat_mul(v_x1_592_, v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Rat_div___boxed(lean_object* v_x1_596_, lean_object* v_x2_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Rat_div(v_x1_596_, v_x2_597_);
lean_dec_ref(v_x1_596_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Rat_add(lean_object* v_a_601_, lean_object* v_b_602_){
_start:
{
lean_object* v_num_603_; lean_object* v_den_604_; lean_object* v_num_605_; lean_object* v_den_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_642_; 
v_num_603_ = lean_ctor_get(v_a_601_, 0);
lean_inc(v_num_603_);
v_den_604_ = lean_ctor_get(v_a_601_, 1);
lean_inc(v_den_604_);
lean_dec_ref(v_a_601_);
v_num_605_ = lean_ctor_get(v_b_602_, 0);
v_den_606_ = lean_ctor_get(v_b_602_, 1);
v_isSharedCheck_642_ = !lean_is_exclusive(v_b_602_);
if (v_isSharedCheck_642_ == 0)
{
v___x_608_ = v_b_602_;
v_isShared_609_ = v_isSharedCheck_642_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_den_606_);
lean_inc(v_num_605_);
lean_dec(v_b_602_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_642_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_610_ = lean_nat_gcd(v_den_604_, v_den_606_);
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_nat_dec_eq(v___x_610_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v_den_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v_num_620_; lean_object* v___x_621_; lean_object* v_g1_622_; uint8_t v___x_623_; 
v___x_613_ = lean_nat_div(v_den_604_, v___x_610_);
lean_dec(v_den_604_);
v_den_614_ = lean_nat_mul(v___x_613_, v_den_606_);
v___x_615_ = lean_nat_div(v_den_606_, v___x_610_);
lean_dec(v_den_606_);
v___x_616_ = lean_nat_to_int(v___x_615_);
v___x_617_ = lean_int_mul(v_num_603_, v___x_616_);
lean_dec(v___x_616_);
lean_dec(v_num_603_);
v___x_618_ = lean_nat_to_int(v___x_613_);
v___x_619_ = lean_int_mul(v_num_605_, v___x_618_);
lean_dec(v___x_618_);
lean_dec(v_num_605_);
v_num_620_ = lean_int_add(v___x_617_, v___x_619_);
lean_dec(v___x_619_);
lean_dec(v___x_617_);
v___x_621_ = lean_nat_abs(v_num_620_);
v_g1_622_ = lean_nat_gcd(v___x_621_, v___x_610_);
lean_dec(v___x_610_);
lean_dec(v___x_621_);
v___x_623_ = lean_nat_dec_eq(v_g1_622_, v___x_611_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
lean_inc(v_g1_622_);
v___x_624_ = lean_nat_to_int(v_g1_622_);
v___x_625_ = lean_int_div_exact(v_num_620_, v___x_624_);
lean_dec(v___x_624_);
lean_dec(v_num_620_);
v___x_626_ = lean_nat_div_exact(v_den_614_, v_g1_622_);
lean_dec(v_g1_622_);
lean_dec(v_den_614_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v___x_626_);
lean_ctor_set(v___x_608_, 0, v___x_625_);
v___x_628_ = v___x_608_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
else
{
lean_object* v___x_631_; 
lean_dec(v_g1_622_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v_den_614_);
lean_ctor_set(v___x_608_, 0, v_num_620_);
v___x_631_ = v___x_608_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_num_620_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_den_614_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
lean_dec(v___x_610_);
lean_inc(v_den_606_);
v___x_633_ = lean_nat_to_int(v_den_606_);
v___x_634_ = lean_int_mul(v_num_603_, v___x_633_);
lean_dec(v___x_633_);
lean_dec(v_num_603_);
lean_inc(v_den_604_);
v___x_635_ = lean_nat_to_int(v_den_604_);
v___x_636_ = lean_int_mul(v_num_605_, v___x_635_);
lean_dec(v___x_635_);
lean_dec(v_num_605_);
v___x_637_ = lean_int_add(v___x_634_, v___x_636_);
lean_dec(v___x_636_);
lean_dec(v___x_634_);
v___x_638_ = lean_nat_mul(v_den_604_, v_den_606_);
lean_dec(v_den_606_);
lean_dec(v_den_604_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v___x_638_);
lean_ctor_set(v___x_608_, 0, v___x_637_);
v___x_640_ = v___x_608_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_neg(lean_object* v_a_645_){
_start:
{
lean_object* v_num_646_; lean_object* v_den_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_655_; 
v_num_646_ = lean_ctor_get(v_a_645_, 0);
v_den_647_ = lean_ctor_get(v_a_645_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_a_645_);
if (v_isSharedCheck_655_ == 0)
{
v___x_649_ = v_a_645_;
v_isShared_650_ = v_isSharedCheck_655_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_den_647_);
lean_inc(v_num_646_);
lean_dec(v_a_645_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_655_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_651_ = lean_int_neg(v_num_646_);
lean_dec(v_num_646_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_651_);
v___x_653_ = v___x_649_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_den_647_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Rat_sub(lean_object* v_a_658_, lean_object* v_b_659_){
_start:
{
lean_object* v_num_660_; lean_object* v_den_661_; lean_object* v_num_662_; lean_object* v_den_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_699_; 
v_num_660_ = lean_ctor_get(v_a_658_, 0);
lean_inc(v_num_660_);
v_den_661_ = lean_ctor_get(v_a_658_, 1);
lean_inc(v_den_661_);
lean_dec_ref(v_a_658_);
v_num_662_ = lean_ctor_get(v_b_659_, 0);
v_den_663_ = lean_ctor_get(v_b_659_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v_b_659_);
if (v_isSharedCheck_699_ == 0)
{
v___x_665_ = v_b_659_;
v_isShared_666_ = v_isSharedCheck_699_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_den_663_);
lean_inc(v_num_662_);
lean_dec(v_b_659_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_699_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_667_ = lean_nat_gcd(v_den_661_, v_den_663_);
v___x_668_ = lean_unsigned_to_nat(1u);
v___x_669_ = lean_nat_dec_eq(v___x_667_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v_den_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v_num_677_; lean_object* v___x_678_; lean_object* v_g1_679_; uint8_t v___x_680_; 
v___x_670_ = lean_nat_div(v_den_661_, v___x_667_);
lean_dec(v_den_661_);
v_den_671_ = lean_nat_mul(v___x_670_, v_den_663_);
v___x_672_ = lean_nat_div(v_den_663_, v___x_667_);
lean_dec(v_den_663_);
v___x_673_ = lean_nat_to_int(v___x_672_);
v___x_674_ = lean_int_mul(v_num_660_, v___x_673_);
lean_dec(v___x_673_);
lean_dec(v_num_660_);
v___x_675_ = lean_nat_to_int(v___x_670_);
v___x_676_ = lean_int_mul(v_num_662_, v___x_675_);
lean_dec(v___x_675_);
lean_dec(v_num_662_);
v_num_677_ = lean_int_sub(v___x_674_, v___x_676_);
lean_dec(v___x_676_);
lean_dec(v___x_674_);
v___x_678_ = lean_nat_abs(v_num_677_);
v_g1_679_ = lean_nat_gcd(v___x_678_, v___x_667_);
lean_dec(v___x_667_);
lean_dec(v___x_678_);
v___x_680_ = lean_nat_dec_eq(v_g1_679_, v___x_668_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
lean_inc(v_g1_679_);
v___x_681_ = lean_nat_to_int(v_g1_679_);
v___x_682_ = lean_int_div_exact(v_num_677_, v___x_681_);
lean_dec(v___x_681_);
lean_dec(v_num_677_);
v___x_683_ = lean_nat_div_exact(v_den_671_, v_g1_679_);
lean_dec(v_g1_679_);
lean_dec(v_den_671_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_683_);
lean_ctor_set(v___x_665_, 0, v___x_682_);
v___x_685_ = v___x_665_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_683_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
else
{
lean_object* v___x_688_; 
lean_dec(v_g1_679_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v_den_671_);
lean_ctor_set(v___x_665_, 0, v_num_677_);
v___x_688_ = v___x_665_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_num_677_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_den_671_);
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
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
lean_dec(v___x_667_);
lean_inc(v_den_663_);
v___x_690_ = lean_nat_to_int(v_den_663_);
v___x_691_ = lean_int_mul(v_num_660_, v___x_690_);
lean_dec(v___x_690_);
lean_dec(v_num_660_);
lean_inc(v_den_661_);
v___x_692_ = lean_nat_to_int(v_den_661_);
v___x_693_ = lean_int_mul(v_num_662_, v___x_692_);
lean_dec(v___x_692_);
lean_dec(v_num_662_);
v___x_694_ = lean_int_sub(v___x_691_, v___x_693_);
lean_dec(v___x_693_);
lean_dec(v___x_691_);
v___x_695_ = lean_nat_mul(v_den_661_, v_den_663_);
lean_dec(v_den_663_);
lean_dec(v_den_661_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_695_);
lean_ctor_set(v___x_665_, 0, v___x_694_);
v___x_697_ = v___x_665_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_695_);
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
LEAN_EXPORT lean_object* l_Rat_floor(lean_object* v_a_702_){
_start:
{
lean_object* v_num_703_; lean_object* v_den_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_num_703_ = lean_ctor_get(v_a_702_, 0);
lean_inc(v_num_703_);
v_den_704_ = lean_ctor_get(v_a_702_, 1);
lean_inc(v_den_704_);
lean_dec_ref(v_a_702_);
v___x_705_ = lean_unsigned_to_nat(1u);
v___x_706_ = lean_nat_dec_eq(v_den_704_, v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_nat_to_int(v_den_704_);
v___x_708_ = lean_int_ediv(v_num_703_, v___x_707_);
lean_dec(v___x_707_);
lean_dec(v_num_703_);
return v___x_708_;
}
else
{
lean_dec(v_den_704_);
return v_num_703_;
}
}
}
static lean_object* _init_l_Rat_ceil___closed__0(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = lean_unsigned_to_nat(1u);
v___x_710_ = lean_nat_to_int(v___x_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Rat_ceil(lean_object* v_a_711_){
_start:
{
lean_object* v_num_712_; lean_object* v_den_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v_num_712_ = lean_ctor_get(v_a_711_, 0);
lean_inc(v_num_712_);
v_den_713_ = lean_ctor_get(v_a_711_, 1);
lean_inc(v_den_713_);
lean_dec_ref(v_a_711_);
v___x_714_ = lean_unsigned_to_nat(1u);
v___x_715_ = lean_nat_dec_eq(v_den_713_, v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_716_ = lean_nat_to_int(v_den_713_);
v___x_717_ = lean_int_ediv(v_num_712_, v___x_716_);
lean_dec(v___x_716_);
lean_dec(v_num_712_);
v___x_718_ = lean_obj_once(&l_Rat_ceil___closed__0, &l_Rat_ceil___closed__0_once, _init_l_Rat_ceil___closed__0);
v___x_719_ = lean_int_add(v___x_717_, v___x_718_);
lean_dec(v___x_717_);
return v___x_719_;
}
else
{
lean_dec(v_den_713_);
return v_num_712_;
}
}
}
static lean_object* _init_l_Rat_abs___closed__0(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = l_Nat_cast___at___00Rat_ofScientific_spec__0(v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Rat_abs(lean_object* v_a_722_){
_start:
{
lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = lean_obj_once(&l_Rat_abs___closed__0, &l_Rat_abs___closed__0_once, _init_l_Rat_abs___closed__0);
lean_inc_ref(v_a_722_);
v___x_724_ = l_Rat_instDecidableLe(v___x_723_, v_a_722_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
v___x_725_ = l_Rat_neg(v_a_722_);
return v___x_725_;
}
else
{
return v_a_722_;
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
