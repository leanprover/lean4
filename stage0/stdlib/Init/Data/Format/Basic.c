// Lean compiler output
// Module: Init.Data.Format.Basic
// Imports: public import Init.Data.Int.Basic public import Init.Data.String.Bootstrap import Init.Control.State import Init.Data.Nat.Bitwise.Basic
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
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Format_instInhabitedFlattenBehavior_default;
LEAN_EXPORT uint8_t l_Std_Format_instInhabitedFlattenBehavior;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Format_instBEqFlattenBehavior_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Format_instBEqFlattenBehavior_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Format_instBEqFlattenBehavior___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Format_instBEqFlattenBehavior_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Format_instBEqFlattenBehavior___closed__0 = (const lean_object*)&l_Std_Format_instBEqFlattenBehavior___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Format_instBEqFlattenBehavior = (const lean_object*)&l_Std_Format_instBEqFlattenBehavior___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Format_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_nil_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_nil_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_line_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_line_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_align_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_align_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_text_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_text_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_nest_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_nest_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_append_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_append_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_group_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_group_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_tag_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_tag_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instInhabitedFormat_default;
LEAN_EXPORT lean_object* l_Std_instInhabitedFormat;
static const lean_string_object l_Std_Format_isEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Format_isEmpty___closed__0 = (const lean_object*)&l_Std_Format_isEmpty___closed__0_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Format_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_fill(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_instAppend___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Format_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Format_instAppend___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Format_instAppend___closed__0 = (const lean_object*)&l_Std_Format_instAppend___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Format_instAppend = (const lean_object*)&l_Std_Format_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Format_instCoeString___lam__0(lean_object*);
static const lean_closure_object l_Std_Format_instCoeString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Format_instCoeString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Format_instCoeString___closed__0 = (const lean_object*)&l_Std_Format_instCoeString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Format_instCoeString = (const lean_object*)&l_Std_Format_instCoeString___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_join_spec__0(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Format_join___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Format_isEmpty___closed__0_value)}};
static const lean_object* l_Std_Format_join___closed__0 = (const lean_object*)&l_Std_Format_join___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Format_join(lean_object*);
LEAN_EXPORT uint8_t l_Std_Format_isNil(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_isNil___boxed(lean_object*);
static const lean_ctor_object l___private_Init_Data_Format_Basic_0__Std_Format_instInhabitedSpaceResult_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instInhabitedSpaceResult_default___closed__0 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instInhabitedSpaceResult_default___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instInhabitedSpaceResult_default = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instInhabitedSpaceResult_default___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instInhabitedSpaceResult = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instInhabitedSpaceResult_default___closed__0_value;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_merge(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_merge___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_spec__0(lean_object*);
static const lean_ctor_object l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0_value;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_string_posof(lean_object*, uint32_t);
lean_object* lean_string_offsetofpos(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Format_instBEqFlattenAllowability_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_instBEqFlattenAllowability_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Format_instBEqFlattenAllowability___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Format_instBEqFlattenAllowability_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Format_instBEqFlattenAllowability___closed__0 = (const lean_object*)&l_Std_Format_instBEqFlattenAllowability___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Format_instBEqFlattenAllowability = (const lean_object*)&l_Std_Format_instBEqFlattenAllowability___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Format_FlattenAllowability_shouldFlatten(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_shouldFlatten___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_pushn(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unreachable"};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
static lean_once_cell_t l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_prettyM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_prettyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_bracket(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Format_paren___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_Format_paren___closed__0 = (const lean_object*)&l_Std_Format_paren___closed__0_value;
static const lean_string_object l_Std_Format_paren___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_Format_paren___closed__1 = (const lean_object*)&l_Std_Format_paren___closed__1_value;
static lean_once_cell_t l_Std_Format_paren___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Format_paren___closed__2;
static lean_once_cell_t l_Std_Format_paren___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Format_paren___closed__3;
static const lean_ctor_object l_Std_Format_paren___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Format_paren___closed__0_value)}};
static const lean_object* l_Std_Format_paren___closed__4 = (const lean_object*)&l_Std_Format_paren___closed__4_value;
static const lean_ctor_object l_Std_Format_paren___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Format_paren___closed__1_value)}};
static const lean_object* l_Std_Format_paren___closed__5 = (const lean_object*)&l_Std_Format_paren___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Format_paren(lean_object*);
static const lean_string_object l_Std_Format_sbracket___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Format_sbracket___closed__0 = (const lean_object*)&l_Std_Format_sbracket___closed__0_value;
static const lean_string_object l_Std_Format_sbracket___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Format_sbracket___closed__1 = (const lean_object*)&l_Std_Format_sbracket___closed__1_value;
static lean_once_cell_t l_Std_Format_sbracket___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Format_sbracket___closed__2;
static lean_once_cell_t l_Std_Format_sbracket___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Format_sbracket___closed__3;
static const lean_ctor_object l_Std_Format_sbracket___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Format_sbracket___closed__0_value)}};
static const lean_object* l_Std_Format_sbracket___closed__4 = (const lean_object*)&l_Std_Format_sbracket___closed__4_value;
static const lean_ctor_object l_Std_Format_sbracket___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Format_sbracket___closed__1_value)}};
static const lean_object* l_Std_Format_sbracket___closed__5 = (const lean_object*)&l_Std_Format_sbracket___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Format_sbracket(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_bracketFill(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_defIndent;
LEAN_EXPORT uint8_t l_Std_Format_defUnicode;
LEAN_EXPORT lean_object* l_Std_Format_defWidth;
static lean_once_cell_t l_Std_Format_nestD___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Format_nestD___closed__0;
LEAN_EXPORT lean_object* l_Std_Format_nestD(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_indentD(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__0 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__0_value;
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__1 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__1_value;
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__2 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__2_value;
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__3 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__3_value;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__4 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__4_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__5 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__5_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__6 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__6_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__7 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__7_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__8 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__8_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__9 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__9_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__10 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__4_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__5_value)}};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__11 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__11_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__6_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__7_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__8_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__9_value)}};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__12 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__12_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__10_value)}};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value;
lean_object* l_StateT_get(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_get, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value)} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__14 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__14_value;
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 7, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__14_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__2_value)} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__15 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__15_value;
static lean_once_cell_t l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16;
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState;
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value)} };
static const lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0 = (const lean_object*)&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0_value;
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__4, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value)} };
static const lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1 = (const lean_object*)&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1_value;
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__7, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value)} };
static const lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2 = (const lean_object*)&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2_value;
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__9, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value)} };
static const lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3 = (const lean_object*)&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3_value;
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_map, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value)} };
static const lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4 = (const lean_object*)&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4_value;
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_pure, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value)} };
static const lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5 = (const lean_object*)&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value)} };
static const lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6 = (const lean_object*)&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6_value;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_pretty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instToFormatFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToFormatFormat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instToFormatFormat___closed__0 = (const lean_object*)&l_Std_instToFormatFormat___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instToFormatFormat = (const lean_object*)&l_Std_instToFormatFormat___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instToFormatString___lam__0(lean_object*);
static const lean_closure_object l_Std_instToFormatString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToFormatString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instToFormatString___closed__0 = (const lean_object*)&l_Std_instToFormatString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instToFormatString = (const lean_object*)&l_Std_instToFormatString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Format_FlattenBehavior_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Format_FlattenBehavior_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Std_Format_FlattenBehavior_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Format_FlattenBehavior_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Std_Format_FlattenBehavior_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Format_FlattenBehavior_allOrNone_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Format_FlattenBehavior_allOrNone_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Format_FlattenBehavior_fill_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Format_FlattenBehavior_fill_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static uint8_t _init_l_Std_Format_instInhabitedFlattenBehavior_default(void) {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Std_Format_instInhabitedFlattenBehavior(void) {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_Format_instBEqFlattenBehavior_beq(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Std_Format_FlattenBehavior_ctorIdx(x_1);
x_4 = l_Std_Format_FlattenBehavior_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Format_instBEqFlattenBehavior_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Std_Format_instBEqFlattenBehavior_beq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorIdx(lean_object* x_1) {
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
case 6:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
default: 
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(7u);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Format_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get_uint8(x_1, 0);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
case 3:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 4:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_2(x_2, x_8, x_9);
return x_10;
}
case 5:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = lean_apply_2(x_2, x_11, x_12);
return x_13;
}
case 6:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec_ref(x_1);
x_16 = lean_box(x_15);
x_17 = lean_apply_2(x_2, x_14, x_16);
return x_17;
}
case 7:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec_ref(x_1);
x_20 = lean_apply_2(x_2, x_18, x_19);
return x_20;
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Format_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Format_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nil_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Format_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nil_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Format_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Format_line_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Format_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_line_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Format_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Format_align_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Format_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_align_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Format_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Format_text_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Format_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_text_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Format_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nest_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Format_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nest_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Format_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Format_append_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Format_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_append_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Format_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Format_group_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Format_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_group_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Format_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Format_tag_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Format_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_tag_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Format_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Std_instInhabitedFormat_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Std_instInhabitedFormat(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_Format_isEmpty(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 3:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
x_5 = lean_string_dec_eq(x_3, x_4);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
x_1 = x_6;
goto _start;
}
case 5:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_Std_Format_isEmpty(x_8);
if (x_10 == 0)
{
return x_10;
}
else
{
x_1 = x_9;
goto _start;
}
}
case 6:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 0);
x_1 = x_12;
goto _start;
}
case 7:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 1);
x_1 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Format_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_fill(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 1;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_instAppend___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_instCoeString___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_join_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
x_5 = x_2;
x_6 = x_12;
goto block_11;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_7; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 5);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_1);
x_7 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_3);
x_7 = x_10;
goto block_9;
}
block_9:
{
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_join(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Std_Format_join___closed__0));
x_3 = l_List_foldl___at___00Std_Format_join_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Format_isNil(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
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
LEAN_EXPORT lean_object* l_Std_Format_isNil___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Format_isNil(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_merge(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_21; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_5 = lean_ctor_get(x_2, 0);
x_21 = lean_nat_dec_lt(x_1, x_5);
if (x_21 == 0)
{
x_6 = x_4;
goto block_20;
}
else
{
x_6 = x_21;
goto block_20;
}
block_20:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_7 = lean_nat_sub(x_1, x_5);
x_8 = lean_apply_1(x_3, x_7);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_10 = lean_ctor_get_uint8(x_8, sizeof(void*)*1 + 1);
x_11 = lean_ctor_get(x_8, 0);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
x_12 = x_8;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_nat_add(x_5, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_9);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 1, x_10);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
else
{
lean_dec_ref(x_3);
lean_inc_ref(x_2);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_merge___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Format_Basic_0__Std_Format_merge(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instInhabitedSpaceResult_default___closed__0));
return x_15;
}
case 1:
{
lean_dec(x_4);
lean_dec(x_3);
if (x_2 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = 1;
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 1, x_2);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0));
return x_19;
}
}
case 2:
{
if (x_2 == 0)
{
lean_dec_ref(x_1);
x_5 = x_2;
goto block_14;
}
else
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_1, 0);
lean_dec_ref(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1 + 1, x_20);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = 0;
x_5 = x_23;
goto block_14;
}
}
}
case 3:
{
lean_object* x_24; uint32_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_32; uint8_t x_33; 
lean_dec(x_4);
lean_dec(x_3);
x_24 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_24);
lean_dec_ref(x_1);
x_25 = 10;
lean_inc_ref(x_24);
x_26 = lean_string_posof(x_24, x_25);
lean_inc(x_26);
lean_inc_ref(x_24);
x_27 = lean_string_offsetofpos(x_24, x_26);
x_32 = lean_string_utf8_byte_size(x_24);
lean_dec_ref(x_24);
x_33 = lean_nat_dec_eq(x_26, x_32);
lean_dec(x_26);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = 1;
x_28 = x_34;
goto block_31;
}
else
{
uint8_t x_35; 
x_35 = 0;
x_28 = x_35;
goto block_31;
}
block_31:
{
if (x_2 == 0)
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1 + 1, x_2);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1 + 1, x_28);
return x_30;
}
}
}
case 4:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec_ref(x_1);
x_38 = lean_int_sub(x_3, x_36);
lean_dec(x_36);
lean_dec(x_3);
x_1 = x_37;
x_3 = x_38;
goto _start;
}
case 5:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; uint8_t x_45; uint8_t x_60; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
lean_dec_ref(x_1);
lean_inc(x_4);
lean_inc(x_3);
x_42 = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(x_40, x_2, x_3, x_4);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*1);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_60 = lean_nat_dec_lt(x_4, x_44);
if (x_60 == 0)
{
x_45 = x_43;
goto block_59;
}
else
{
x_45 = x_60;
goto block_59;
}
block_59:
{
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_58; 
lean_dec_ref(x_42);
x_46 = lean_nat_sub(x_4, x_44);
lean_dec(x_4);
x_47 = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(x_41, x_2, x_3, x_46);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
x_49 = lean_ctor_get_uint8(x_47, sizeof(void*)*1 + 1);
x_50 = lean_ctor_get(x_47, 0);
x_58 = !lean_is_exclusive(x_47);
if (x_58 == 0)
{
x_51 = x_47;
x_52 = x_58;
goto block_57;
}
else
{
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_box(0);
x_52 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_nat_add(x_44, x_50);
lean_dec(x_50);
lean_dec(x_44);
if (x_52 == 0)
{
lean_ctor_set(x_51, 0, x_53);
x_54 = x_51;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_48);
lean_ctor_set_uint8(x_56, sizeof(void*)*1 + 1, x_49);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
else
{
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_4);
lean_dec(x_3);
return x_42;
}
}
}
case 6:
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
lean_dec_ref(x_1);
x_62 = 1;
x_1 = x_61;
x_2 = x_62;
goto _start;
}
default: 
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
lean_dec_ref(x_1);
x_1 = x_64;
goto _start;
}
}
block_14:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_nat_to_int(x_4);
x_7 = lean_int_dec_lt(x_6, x_3);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_3);
x_8 = 1;
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*1 + 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_int_sub(x_3, x_6);
lean_dec(x_6);
lean_dec(x_3);
x_12 = l_Int_toNat(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_5);
lean_ctor_set_uint8(x_13, sizeof(void*)*1 + 1, x_5);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Format_FlattenAllowability_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get_uint8(x_1, 0);
x_4 = lean_box(x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Format_FlattenAllowability_ctorElim___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Format_FlattenAllowability_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Format_FlattenAllowability_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Format_FlattenAllowability_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Format_FlattenAllowability_allow_elim___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Format_FlattenAllowability_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Format_FlattenAllowability_allow_elim(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Format_FlattenAllowability_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Format_FlattenAllowability_disallow_elim___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Format_FlattenAllowability_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Format_FlattenAllowability_disallow_elim(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Format_instBEqFlattenAllowability_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, 0);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_2, 0);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
return x_3;
}
}
else
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_2, 0);
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
else
{
if (lean_obj_tag(x_2) == 1)
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
}
}
LEAN_EXPORT lean_object* l_Std_Format_instBEqFlattenAllowability_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Format_instBEqFlattenAllowability_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Format_FlattenAllowability_shouldFlatten(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, 0);
if (x_2 == 1)
{
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_shouldFlatten___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Format_FlattenAllowability_shouldFlatten(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
lean_dec(x_2);
x_4 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instInhabitedSpaceResult_default___closed__0));
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_1 = x_7;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; uint8_t x_54; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
x_54 = !lean_is_exclusive(x_5);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_5, 1);
lean_dec(x_55);
x_13 = x_5;
x_14 = x_54;
goto block_53;
}
else
{
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_51; 
x_15 = lean_ctor_get(x_6, 1);
x_51 = !lean_is_exclusive(x_6);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_6, 0);
lean_dec(x_52);
x_16 = x_6;
x_17 = x_51;
goto block_50;
}
else
{
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l_Std_Format_FlattenAllowability_shouldFlatten(x_11);
lean_inc(x_3);
x_21 = lean_nat_to_int(x_3);
lean_inc(x_2);
x_22 = lean_nat_to_int(x_2);
x_23 = lean_int_add(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
x_24 = lean_int_sub(x_23, x_19);
lean_dec(x_19);
lean_dec(x_23);
lean_inc(x_3);
x_25 = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(x_18, x_20, x_24, x_3);
x_26 = lean_ctor_get_uint8(x_25, sizeof(void*)*1);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_15);
x_28 = x_13;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_49, 0, x_11);
lean_ctor_set(x_49, 1, x_15);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_12);
x_28 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_29; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 0, x_28);
x_29 = x_16;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_28);
lean_ctor_set(x_47, 1, x_10);
x_29 = x_47;
goto block_46;
}
block_46:
{
uint8_t x_30; uint8_t x_45; 
x_45 = lean_nat_dec_lt(x_3, x_27);
if (x_45 == 0)
{
x_30 = x_26;
goto block_44;
}
else
{
x_30 = x_45;
goto block_44;
}
block_44:
{
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_43; 
lean_dec_ref(x_25);
x_31 = lean_nat_sub(x_3, x_27);
lean_dec(x_3);
x_32 = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(x_29, x_2, x_31);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*1);
x_34 = lean_ctor_get_uint8(x_32, sizeof(void*)*1 + 1);
x_35 = lean_ctor_get(x_32, 0);
x_43 = !lean_is_exclusive(x_32);
if (x_43 == 0)
{
x_36 = x_32;
x_37 = x_43;
goto block_42;
}
else
{
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_box(0);
x_37 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_nat_add(x_27, x_35);
lean_dec(x_35);
lean_dec(x_27);
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_38);
x_39 = x_36;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_33);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 1, x_34);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
else
{
lean_dec_ref(x_29);
lean_dec(x_27);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_27; lean_object* x_28; uint8_t x_29; uint8_t x_44; 
x_13 = 0;
x_14 = l_Std_Format_instBEqFlattenBehavior_beq(x_1, x_13);
x_15 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_15, 0, x_14);
lean_inc(x_2);
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_nat_sub(x_3, x_6);
lean_inc(x_19);
lean_inc(x_6);
x_20 = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(x_18, x_6, x_19);
x_27 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
x_44 = lean_nat_dec_lt(x_19, x_28);
if (x_44 == 0)
{
x_29 = x_27;
goto block_43;
}
else
{
x_29 = x_44;
goto block_43;
}
block_12:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_1);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_apply_2(x_5, lean_box(0), x_10);
return x_11;
}
block_26:
{
uint8_t x_22; 
x_22 = lean_ctor_get_uint8(x_20, sizeof(void*)*1 + 1);
lean_dec_ref(x_20);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_nat_dec_le(x_23, x_19);
lean_dec(x_19);
lean_dec(x_23);
x_7 = x_24;
goto block_12;
}
else
{
uint8_t x_25; 
lean_dec_ref(x_21);
lean_dec(x_19);
x_25 = 0;
x_7 = x_25;
goto block_12;
}
}
block_43:
{
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_42; 
x_30 = lean_nat_sub(x_19, x_28);
lean_inc(x_4);
x_31 = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(x_4, x_6, x_30);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*1);
x_33 = lean_ctor_get_uint8(x_31, sizeof(void*)*1 + 1);
x_34 = lean_ctor_get(x_31, 0);
x_42 = !lean_is_exclusive(x_31);
if (x_42 == 0)
{
x_35 = x_31;
x_36 = x_42;
goto block_41;
}
else
{
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_box(0);
x_36 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_nat_add(x_28, x_34);
lean_dec(x_34);
lean_dec(x_28);
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_37);
x_38 = x_35;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_32);
lean_ctor_set_uint8(x_40, sizeof(void*)*1 + 1, x_33);
x_38 = x_40;
goto block_39;
}
block_39:
{
x_21 = x_38;
goto block_26;
}
}
}
else
{
lean_dec(x_28);
lean_dec(x_6);
lean_inc_ref(x_20);
x_21 = x_20;
goto block_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_box(x_1);
x_12 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed), 6, 5);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_10);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_2);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_1(x_1, x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Int_toNat(x_1);
x_7 = lean_apply_1(x_2, x_6);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_nat_to_int(x_6);
x_8 = lean_int_dec_lt(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_5);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = l_Int_toNat(x_1);
x_11 = lean_apply_1(x_9, x_10);
x_12 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_11, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint32_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
x_15 = 32;
x_16 = lean_int_sub(x_1, x_7);
lean_dec(x_7);
x_17 = l_Int_toNat(x_16);
lean_dec(x_16);
x_18 = lean_string_pushn(x_14, x_15, x_17);
x_19 = lean_apply_1(x_13, x_18);
x_20 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_19, x_5);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_6, x_2);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_1(x_1, x_2);
x_8 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_9 = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
x_10 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_6);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_11, 0);
x_13 = l_Std_Format_FlattenAllowability_shouldFlatten(x_12);
if (x_13 == 0)
{
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4), 5, 4);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_10);
lean_inc(x_7);
x_15 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_6);
lean_closure_set(x_15, 2, x_7);
lean_closure_set(x_15, 3, x_14);
x_16 = lean_apply_1(x_8, x_9);
x_17 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_16, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_18 = lean_box(0);
x_19 = l_instInhabitedOfMonad___redArg(x_3, x_18);
x_20 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0));
x_21 = l_panic___redArg(x_19, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
x_2 = lean_string_length(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_string_utf8_next(x_1, x_2);
x_17 = lean_string_utf8_extract(x_1, x_16, x_3);
lean_dec(x_16);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
lean_ctor_set(x_19, 2, x_5);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
x_21 = lean_box(1);
x_22 = l_Std_Format_instBEqFlattenAllowability_beq(x_7, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_14);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
x_23 = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(x_8, x_20, x_9, x_10, x_11, x_12);
x_24 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(x_24, 0, x_10);
lean_closure_set(x_24, 1, x_11);
lean_closure_set(x_24, 2, x_12);
x_25 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_23, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_13);
lean_dec(x_9);
x_26 = lean_apply_1(x_14, x_20);
x_27 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(x_10, x_11, x_12, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_8);
x_17 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_3);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
x_14 = lean_apply_1(x_5, x_13);
x_15 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(x_6, x_7, x_8, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_box(0);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec_ref(x_4);
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_158; 
lean_inc(x_9);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_4, 1);
x_158 = !lean_is_exclusive(x_4);
if (x_158 == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_4, 0);
lean_dec(x_159);
x_16 = x_4;
x_17 = x_158;
goto block_157;
}
else
{
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = x_158;
goto block_157;
}
block_157:
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_155; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
lean_dec(x_9);
x_20 = lean_ctor_get(x_10, 1);
x_155 = !lean_is_exclusive(x_10);
if (x_155 == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_10, 0);
lean_dec(x_156);
x_21 = x_10;
x_22 = x_155;
goto block_154;
}
else
{
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_box(0);
x_22 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_153; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
x_25 = lean_ctor_get(x_13, 2);
x_153 = !lean_is_exclusive(x_13);
if (x_153 == 0)
{
x_26 = x_13;
x_27 = x_153;
goto block_152;
}
else
{
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_26 = lean_box(0);
x_27 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(x_19);
lean_inc(x_15);
lean_inc(x_18);
x_29 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_29, 0, x_18);
lean_closure_set(x_29, 1, x_28);
lean_closure_set(x_29, 2, x_15);
switch (lean_obj_tag(x_23)) {
case 0:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc(x_14);
lean_del_object(x_26);
lean_dec(x_24);
lean_del_object(x_21);
lean_dec(x_18);
lean_del_object(x_16);
lean_dec(x_15);
x_30 = lean_ctor_get(x_3, 4);
lean_inc(x_30);
x_31 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(x_31, 0, x_29);
lean_closure_set(x_31, 1, x_20);
lean_closure_set(x_31, 2, x_1);
lean_closure_set(x_31, 3, x_2);
lean_closure_set(x_31, 4, x_3);
x_32 = lean_apply_1(x_30, x_25);
x_33 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_32, x_31);
return x_33;
}
case 1:
{
lean_inc(x_14);
lean_del_object(x_26);
lean_del_object(x_21);
lean_del_object(x_16);
if (x_19 == 0)
{
uint8_t x_34; 
lean_dec(x_15);
x_34 = l_Std_Format_FlattenAllowability_shouldFlatten(x_18);
lean_dec(x_18);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 4);
lean_inc(x_36);
x_37 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(x_37, 0, x_29);
lean_closure_set(x_37, 1, x_20);
lean_closure_set(x_37, 2, x_1);
lean_closure_set(x_37, 3, x_2);
lean_closure_set(x_37, 4, x_3);
lean_inc(x_14);
x_38 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(x_38, 0, x_36);
lean_closure_set(x_38, 1, x_25);
lean_closure_set(x_38, 2, x_14);
lean_closure_set(x_38, 3, x_37);
x_39 = l_Int_toNat(x_24);
lean_dec(x_24);
x_40 = lean_apply_1(x_35, x_39);
x_41 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_40, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_24);
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 4);
lean_inc(x_43);
x_44 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(x_44, 0, x_29);
lean_closure_set(x_44, 1, x_20);
lean_closure_set(x_44, 2, x_1);
lean_closure_set(x_44, 3, x_2);
lean_closure_set(x_44, 4, x_3);
lean_inc(x_14);
x_45 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(x_45, 0, x_43);
lean_closure_set(x_45, 1, x_25);
lean_closure_set(x_45, 2, x_14);
lean_closure_set(x_45, 3, x_44);
x_46 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
x_47 = lean_apply_1(x_42, x_46);
x_48 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_47, x_45);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec_ref(x_29);
x_49 = lean_ctor_get(x_3, 0);
x_50 = lean_ctor_get(x_3, 1);
x_51 = lean_ctor_get(x_3, 4);
x_52 = lean_box(x_19);
lean_inc(x_14);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
lean_inc(x_15);
lean_inc(x_20);
x_53 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed), 8, 7);
lean_closure_set(x_53, 0, x_52);
lean_closure_set(x_53, 1, x_20);
lean_closure_set(x_53, 2, x_15);
lean_closure_set(x_53, 3, x_1);
lean_closure_set(x_53, 4, x_2);
lean_closure_set(x_53, 5, x_3);
lean_closure_set(x_53, 6, x_14);
lean_inc(x_14);
lean_inc(x_25);
lean_inc(x_51);
x_54 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(x_54, 0, x_51);
lean_closure_set(x_54, 1, x_25);
lean_closure_set(x_54, 2, x_14);
lean_closure_set(x_54, 3, x_53);
x_55 = l_Int_toNat(x_24);
lean_dec(x_24);
lean_inc(x_50);
x_56 = lean_apply_1(x_50, x_55);
lean_inc(x_14);
x_57 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_56, x_54);
x_58 = l_Std_Format_FlattenAllowability_shouldFlatten(x_18);
lean_dec(x_18);
if (x_58 == 0)
{
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
lean_inc(x_49);
lean_inc(x_14);
lean_inc(x_51);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_60 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed), 10, 9);
lean_closure_set(x_60, 0, x_57);
lean_closure_set(x_60, 1, x_1);
lean_closure_set(x_60, 2, x_2);
lean_closure_set(x_60, 3, x_3);
lean_closure_set(x_60, 4, x_51);
lean_closure_set(x_60, 5, x_25);
lean_closure_set(x_60, 6, x_14);
lean_closure_set(x_60, 7, x_49);
lean_closure_set(x_60, 8, x_59);
x_61 = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
x_62 = lean_nat_sub(x_1, x_61);
lean_dec(x_1);
x_63 = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(x_19, x_20, x_15, x_62, x_2, x_3);
x_64 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_63, x_60);
return x_64;
}
}
}
case 2:
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_72; uint8_t x_77; 
lean_inc(x_14);
lean_del_object(x_26);
lean_del_object(x_21);
lean_del_object(x_16);
lean_dec(x_15);
x_65 = lean_ctor_get_uint8(x_23, 0);
lean_dec_ref(x_23);
lean_inc_ref(x_3);
x_66 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(x_66, 0, x_29);
lean_closure_set(x_66, 1, x_20);
lean_closure_set(x_66, 2, x_1);
lean_closure_set(x_66, 3, x_2);
lean_closure_set(x_66, 4, x_3);
lean_inc_ref(x_66);
lean_inc(x_14);
lean_inc(x_25);
lean_inc_ref(x_3);
x_67 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9), 5, 4);
lean_closure_set(x_67, 0, x_3);
lean_closure_set(x_67, 1, x_25);
lean_closure_set(x_67, 2, x_14);
lean_closure_set(x_67, 3, x_66);
lean_inc_ref(x_67);
lean_inc(x_14);
lean_inc_ref(x_3);
x_68 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed), 6, 5);
lean_closure_set(x_68, 0, x_24);
lean_closure_set(x_68, 1, x_3);
lean_closure_set(x_68, 2, x_14);
lean_closure_set(x_68, 3, x_67);
lean_closure_set(x_68, 4, x_67);
x_77 = l_Std_Format_FlattenAllowability_shouldFlatten(x_18);
lean_dec(x_18);
if (x_77 == 0)
{
x_72 = x_77;
goto block_76;
}
else
{
if (x_65 == 0)
{
x_72 = x_77;
goto block_76;
}
else
{
lean_dec_ref(x_66);
lean_dec(x_25);
goto block_71;
}
}
block_71:
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_3, 2);
lean_inc(x_69);
lean_dec_ref(x_3);
x_70 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_69, x_68);
return x_70;
}
block_76:
{
if (x_72 == 0)
{
lean_dec_ref(x_66);
lean_dec(x_25);
goto block_71;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_68);
x_73 = lean_ctor_get(x_3, 4);
lean_inc(x_73);
lean_dec_ref(x_3);
x_74 = lean_apply_1(x_73, x_25);
x_75 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_74, x_66);
return x_75;
}
}
}
case 3:
{
lean_object* x_78; uint32_t x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_inc(x_14);
lean_del_object(x_26);
lean_del_object(x_21);
lean_del_object(x_16);
x_78 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_78);
lean_dec_ref(x_23);
x_79 = 10;
lean_inc_ref(x_78);
x_80 = lean_string_posof(x_78, x_79);
x_81 = lean_string_utf8_byte_size(x_78);
x_82 = lean_nat_dec_eq(x_80, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_83 = lean_ctor_get(x_3, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_3, 1);
lean_inc(x_84);
x_85 = lean_box(x_19);
lean_inc(x_14);
lean_inc(x_24);
lean_inc(x_80);
lean_inc_ref(x_78);
x_86 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed), 15, 14);
lean_closure_set(x_86, 0, x_78);
lean_closure_set(x_86, 1, x_80);
lean_closure_set(x_86, 2, x_81);
lean_closure_set(x_86, 3, x_24);
lean_closure_set(x_86, 4, x_25);
lean_closure_set(x_86, 5, x_20);
lean_closure_set(x_86, 6, x_18);
lean_closure_set(x_86, 7, x_85);
lean_closure_set(x_86, 8, x_15);
lean_closure_set(x_86, 9, x_1);
lean_closure_set(x_86, 10, x_2);
lean_closure_set(x_86, 11, x_3);
lean_closure_set(x_86, 12, x_14);
lean_closure_set(x_86, 13, x_29);
lean_inc(x_14);
x_87 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed), 5, 4);
lean_closure_set(x_87, 0, x_24);
lean_closure_set(x_87, 1, x_84);
lean_closure_set(x_87, 2, x_14);
lean_closure_set(x_87, 3, x_86);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_string_utf8_extract(x_78, x_88, x_80);
lean_dec(x_80);
lean_dec_ref(x_78);
x_90 = lean_apply_1(x_83, x_89);
x_91 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_90, x_87);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_80);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_15);
x_92 = lean_ctor_get(x_3, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_3, 4);
lean_inc(x_93);
x_94 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(x_94, 0, x_29);
lean_closure_set(x_94, 1, x_20);
lean_closure_set(x_94, 2, x_1);
lean_closure_set(x_94, 3, x_2);
lean_closure_set(x_94, 4, x_3);
lean_inc(x_14);
x_95 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(x_95, 0, x_93);
lean_closure_set(x_95, 1, x_25);
lean_closure_set(x_95, 2, x_14);
lean_closure_set(x_95, 3, x_94);
x_96 = lean_apply_1(x_92, x_78);
x_97 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_96, x_95);
return x_97;
}
}
case 4:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec_ref(x_29);
lean_del_object(x_16);
x_98 = lean_ctor_get(x_23, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_23, 1);
lean_inc(x_99);
lean_dec_ref(x_23);
x_100 = lean_int_add(x_24, x_98);
lean_dec(x_98);
lean_dec(x_24);
if (x_27 == 0)
{
lean_ctor_set(x_26, 1, x_100);
lean_ctor_set(x_26, 0, x_99);
x_101 = x_26;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_108, 0, x_99);
lean_ctor_set(x_108, 1, x_100);
lean_ctor_set(x_108, 2, x_25);
x_101 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_102; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_101);
x_102 = x_21;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_101);
lean_ctor_set(x_106, 1, x_20);
x_102 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_103; 
x_103 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_18, x_19, x_15, x_102);
x_4 = x_103;
goto _start;
}
}
}
case 5:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec_ref(x_29);
x_109 = lean_ctor_get(x_23, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_23, 1);
lean_inc(x_110);
lean_dec_ref(x_23);
x_111 = lean_unsigned_to_nat(0u);
lean_inc(x_24);
if (x_27 == 0)
{
lean_ctor_set(x_26, 2, x_111);
lean_ctor_set(x_26, 0, x_109);
x_112 = x_26;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_123, 0, x_109);
lean_ctor_set(x_123, 1, x_24);
lean_ctor_set(x_123, 2, x_111);
x_112 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_24);
lean_ctor_set(x_113, 2, x_25);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_113);
x_114 = x_21;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_113);
lean_ctor_set(x_121, 1, x_20);
x_114 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_115; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_114);
lean_ctor_set(x_16, 0, x_112);
x_115 = x_16;
goto block_118;
}
else
{
lean_object* x_119; 
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_112);
lean_ctor_set(x_119, 1, x_114);
x_115 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_116; 
x_116 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_18, x_19, x_15, x_115);
x_4 = x_116;
goto _start;
}
}
}
}
case 6:
{
lean_object* x_124; uint8_t x_125; uint8_t x_126; 
lean_dec_ref(x_29);
lean_del_object(x_16);
x_124 = lean_ctor_get(x_23, 0);
lean_inc(x_124);
x_125 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
lean_dec_ref(x_23);
x_126 = l_Std_Format_FlattenAllowability_shouldFlatten(x_18);
if (x_126 == 0)
{
lean_object* x_127; 
lean_inc(x_14);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_124);
x_127 = x_26;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_137, 0, x_124);
lean_ctor_set(x_137, 1, x_24);
lean_ctor_set(x_137, 2, x_25);
x_127 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_box(0);
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_128);
lean_ctor_set(x_21, 0, x_127);
x_129 = x_21;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_127);
lean_ctor_set(x_135, 1, x_128);
x_129 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_18, x_19, x_15, x_20);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_131 = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(x_125, x_129, x_130, x_1, x_2, x_3);
x_132 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(x_132, 0, x_1);
lean_closure_set(x_132, 1, x_2);
lean_closure_set(x_132, 2, x_3);
x_133 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_131, x_132);
return x_133;
}
}
}
else
{
lean_object* x_138; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_124);
x_138 = x_26;
goto block_144;
}
else
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_145, 0, x_124);
lean_ctor_set(x_145, 1, x_24);
lean_ctor_set(x_145, 2, x_25);
x_138 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_139; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_138);
x_139 = x_21;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_138);
lean_ctor_set(x_143, 1, x_20);
x_139 = x_143;
goto block_142;
}
block_142:
{
lean_object* x_140; 
x_140 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_18, x_19, x_15, x_139);
x_4 = x_140;
goto _start;
}
}
}
}
default: 
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_inc(x_14);
lean_del_object(x_26);
lean_del_object(x_21);
lean_dec(x_18);
lean_del_object(x_16);
lean_dec(x_15);
x_146 = lean_ctor_get(x_23, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_23, 1);
lean_inc(x_147);
lean_dec_ref(x_23);
x_148 = lean_ctor_get(x_3, 3);
lean_inc(x_148);
x_149 = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed), 9, 8);
lean_closure_set(x_149, 0, x_25);
lean_closure_set(x_149, 1, x_147);
lean_closure_set(x_149, 2, x_24);
lean_closure_set(x_149, 3, x_20);
lean_closure_set(x_149, 4, x_29);
lean_closure_set(x_149, 5, x_1);
lean_closure_set(x_149, 6, x_2);
lean_closure_set(x_149, 7, x_3);
x_150 = lean_apply_1(x_148, x_146);
x_151 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_150, x_149);
return x_151;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_box(1);
x_7 = 0;
x_8 = lean_nat_to_int(x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(x_2, x_4, x_5, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Format_prettyM___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Format_bracket(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_4 = lean_string_length(x_1);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
static lean_object* _init_l_Std_Format_paren___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Std_Format_paren___closed__0));
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Format_paren___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Std_Format_paren___closed__2, &l_Std_Format_paren___closed__2_once, _init_l_Std_Format_paren___closed__2);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Format_paren(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_obj_once(&l_Std_Format_paren___closed__3, &l_Std_Format_paren___closed__3_once, _init_l_Std_Format_paren___closed__3);
x_3 = ((lean_object*)(l_Std_Format_paren___closed__4));
x_4 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = ((lean_object*)(l_Std_Format_paren___closed__5));
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
x_8 = 0;
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
return x_9;
}
}
static lean_object* _init_l_Std_Format_sbracket___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Std_Format_sbracket___closed__0));
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Format_sbracket___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Std_Format_sbracket___closed__2, &l_Std_Format_sbracket___closed__2_once, _init_l_Std_Format_sbracket___closed__2);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Format_sbracket(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = lean_obj_once(&l_Std_Format_sbracket___closed__3, &l_Std_Format_sbracket___closed__3_once, _init_l_Std_Format_sbracket___closed__3);
x_3 = ((lean_object*)(l_Std_Format_sbracket___closed__4));
x_4 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = ((lean_object*)(l_Std_Format_sbracket___closed__5));
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
x_8 = 0;
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Format_bracketFill(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_string_length(x_1);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Std_Format_fill(x_10);
return x_11;
}
}
static lean_object* _init_l_Std_Format_defIndent(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
static uint8_t _init_l_Std_Format_defUnicode(void) {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static lean_object* _init_l_Std_Format_defWidth(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(120u);
return x_1;
}
}
static lean_object* _init_l_Std_Format_nestD___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nestD(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Format_nestD___closed__0, &l_Std_Format_nestD___closed__0_once, _init_l_Std_Format_nestD___closed__0);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_indentD(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = l_Std_Format_nestD(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_16; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
x_5 = x_2;
x_6 = x_16;
goto block_15;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_box(0);
x_8 = lean_string_append(x_3, x_1);
x_9 = lean_string_length(x_1);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_9);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_10);
lean_ctor_set(x_5, 0, x_8);
x_11 = x_5;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_10);
x_11 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_16; 
x_3 = lean_ctor_get(x_2, 0);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_2, 1);
lean_dec(x_17);
x_4 = x_2;
x_5 = x_16;
goto block_15;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_box(0);
x_7 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
x_8 = 32;
lean_inc(x_1);
x_9 = lean_string_pushn(x_7, x_8, x_1);
x_10 = lean_string_append(x_3, x_9);
lean_dec_ref(x_9);
if (x_5 == 0)
{
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 0, x_10);
x_11 = x_4;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_1);
x_11 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 1);
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_4 = x_1;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_3);
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_2);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__3));
x_2 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__15));
x_3 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__1));
x_4 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__0));
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16, &l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_27; lean_object* x_28; uint8_t x_29; uint8_t x_44; 
x_12 = lean_ctor_get(x_5, 1);
x_13 = 0;
x_14 = l_Std_Format_instBEqFlattenBehavior_beq(x_1, x_13);
x_15 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_15, 0, x_14);
lean_inc(x_2);
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_nat_sub(x_4, x_12);
lean_inc(x_19);
lean_inc(x_12);
x_20 = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(x_18, x_12, x_19);
x_27 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
x_44 = lean_nat_dec_lt(x_19, x_28);
if (x_44 == 0)
{
x_29 = x_27;
goto block_43;
}
else
{
x_29 = x_44;
goto block_43;
}
block_11:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
block_26:
{
uint8_t x_22; 
x_22 = lean_ctor_get_uint8(x_20, sizeof(void*)*1 + 1);
lean_dec_ref(x_20);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_nat_dec_le(x_23, x_19);
lean_dec(x_19);
lean_dec(x_23);
x_6 = x_24;
goto block_11;
}
else
{
uint8_t x_25; 
lean_dec_ref(x_21);
lean_dec(x_19);
x_25 = 0;
x_6 = x_25;
goto block_11;
}
}
block_43:
{
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_42; 
x_30 = lean_nat_sub(x_19, x_28);
lean_inc(x_12);
lean_inc(x_3);
x_31 = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(x_3, x_12, x_30);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*1);
x_33 = lean_ctor_get_uint8(x_31, sizeof(void*)*1 + 1);
x_34 = lean_ctor_get(x_31, 0);
x_42 = !lean_is_exclusive(x_31);
if (x_42 == 0)
{
x_35 = x_31;
x_36 = x_42;
goto block_41;
}
else
{
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_box(0);
x_36 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_nat_add(x_28, x_34);
lean_dec(x_34);
lean_dec(x_28);
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_37);
x_38 = x_35;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_32);
lean_ctor_set_uint8(x_40, sizeof(void*)*1 + 1, x_33);
x_38 = x_40;
goto block_39;
}
block_39:
{
x_21 = x_38;
goto block_26;
}
}
}
else
{
lean_dec(x_28);
lean_inc_ref(x_20);
x_21 = x_20;
goto block_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_3 = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0));
x_4 = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1));
x_5 = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2));
x_6 = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3));
x_7 = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4));
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
x_9 = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5));
x_10 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_4);
lean_ctor_set(x_10, 3, x_5);
lean_ctor_set(x_10, 4, x_6);
x_11 = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6));
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(0);
x_14 = l_instInhabitedOfMonad___redArg(x_12, x_13);
x_15 = lean_panic_fn(x_14, x_1);
x_16 = lean_apply_1(x_15, x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec_ref(x_2);
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_281; 
lean_inc(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
x_281 = !lean_is_exclusive(x_2);
if (x_281 == 0)
{
lean_object* x_282; 
x_282 = lean_ctor_get(x_2, 0);
lean_dec(x_282);
x_12 = x_2;
x_13 = x_281;
goto block_280;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_281;
goto block_280;
}
block_280:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_278; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
lean_dec(x_6);
x_16 = lean_ctor_get(x_7, 1);
x_278 = !lean_is_exclusive(x_7);
if (x_278 == 0)
{
lean_object* x_279; 
x_279 = lean_ctor_get(x_7, 0);
lean_dec(x_279);
x_17 = x_7;
x_18 = x_278;
goto block_277;
}
else
{
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = x_278;
goto block_277;
}
block_277:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_276; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
x_21 = lean_ctor_get(x_10, 2);
x_276 = !lean_is_exclusive(x_10);
if (x_276 == 0)
{
x_22 = x_10;
x_23 = x_276;
goto block_275;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_22 = lean_box(0);
x_23 = x_276;
goto block_275;
}
block_275:
{
uint8_t x_56; 
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_60; 
lean_del_object(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_del_object(x_17);
lean_del_object(x_12);
x_60 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_14, x_15, x_11, x_16);
x_2 = x_60;
goto _start;
}
case 1:
{
lean_del_object(x_22);
lean_dec(x_21);
lean_del_object(x_17);
lean_del_object(x_12);
if (x_15 == 0)
{
uint8_t x_62; 
x_62 = l_Std_Format_FlattenAllowability_shouldFlatten(x_14);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_77; 
x_63 = lean_ctor_get(x_3, 0);
x_77 = !lean_is_exclusive(x_3);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_3, 1);
lean_dec(x_78);
x_64 = x_3;
x_65 = x_77;
goto block_76;
}
else
{
lean_inc(x_63);
lean_dec(x_3);
x_64 = lean_box(0);
x_65 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_66; lean_object* x_67; uint32_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = l_Int_toNat(x_20);
lean_dec(x_20);
x_67 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
x_68 = 32;
lean_inc(x_66);
x_69 = lean_string_pushn(x_67, x_68, x_66);
x_70 = lean_string_append(x_63, x_69);
lean_dec_ref(x_69);
if (x_65 == 0)
{
lean_ctor_set(x_64, 1, x_66);
lean_ctor_set(x_64, 0, x_70);
x_71 = x_64;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_66);
x_71 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_72; 
x_72 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_14, x_15, x_11, x_16);
x_2 = x_72;
x_3 = x_71;
goto _start;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_93; 
lean_dec(x_20);
x_79 = lean_ctor_get(x_3, 0);
x_80 = lean_ctor_get(x_3, 1);
x_93 = !lean_is_exclusive(x_3);
if (x_93 == 0)
{
x_81 = x_3;
x_82 = x_93;
goto block_92;
}
else
{
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_3);
x_81 = lean_box(0);
x_82 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
x_84 = lean_string_append(x_79, x_83);
x_85 = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
x_86 = lean_nat_add(x_80, x_85);
lean_dec(x_80);
if (x_82 == 0)
{
lean_ctor_set(x_81, 1, x_86);
lean_ctor_set(x_81, 0, x_84);
x_87 = x_81;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_84);
lean_ctor_set(x_91, 1, x_86);
x_87 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_88; 
x_88 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_14, x_15, x_11, x_16);
x_2 = x_88;
x_3 = x_87;
goto _start;
}
}
}
}
else
{
lean_object* x_94; uint8_t x_95; 
x_94 = l_Int_toNat(x_20);
lean_dec(x_20);
x_95 = l_Std_Format_FlattenAllowability_shouldFlatten(x_14);
lean_dec(x_14);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_111; 
x_96 = lean_ctor_get(x_3, 0);
x_111 = !lean_is_exclusive(x_3);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_3, 1);
lean_dec(x_112);
x_97 = x_3;
x_98 = x_111;
goto block_110;
}
else
{
lean_inc(x_96);
lean_dec(x_3);
x_97 = lean_box(0);
x_98 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_99; uint32_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
x_100 = 32;
lean_inc(x_94);
x_101 = lean_string_pushn(x_99, x_100, x_94);
x_102 = lean_string_append(x_96, x_101);
lean_dec_ref(x_101);
if (x_98 == 0)
{
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 0, x_102);
x_103 = x_97;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_102);
lean_ctor_set(x_109, 1, x_94);
x_103 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(x_15, x_16, x_11, x_1, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec_ref(x_104);
x_2 = x_105;
x_3 = x_106;
goto _start;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
x_114 = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
x_115 = lean_nat_sub(x_1, x_114);
lean_inc(x_11);
lean_inc(x_16);
x_116 = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(x_15, x_16, x_11, x_115, x_3);
lean_dec(x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 1)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_118 = lean_ctor_get(x_117, 0);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_dec_ref(x_116);
x_120 = lean_ctor_get(x_118, 0);
x_121 = l_Std_Format_FlattenAllowability_shouldFlatten(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_137; 
lean_dec_ref(x_117);
x_122 = lean_ctor_get(x_119, 0);
x_137 = !lean_is_exclusive(x_119);
if (x_137 == 0)
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_119, 1);
lean_dec(x_138);
x_123 = x_119;
x_124 = x_137;
goto block_136;
}
else
{
lean_inc(x_122);
lean_dec(x_119);
x_123 = lean_box(0);
x_124 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_125; uint32_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
x_126 = 32;
lean_inc(x_94);
x_127 = lean_string_pushn(x_125, x_126, x_94);
x_128 = lean_string_append(x_122, x_127);
lean_dec_ref(x_127);
if (x_124 == 0)
{
lean_ctor_set(x_123, 1, x_94);
lean_ctor_set(x_123, 0, x_128);
x_129 = x_123;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_128);
lean_ctor_set(x_135, 1, x_94);
x_129 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(x_15, x_16, x_11, x_1, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec_ref(x_130);
x_2 = x_131;
x_3 = x_132;
goto _start;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_150; 
lean_dec(x_94);
lean_dec(x_16);
lean_dec(x_11);
x_139 = lean_ctor_get(x_119, 0);
x_140 = lean_ctor_get(x_119, 1);
x_150 = !lean_is_exclusive(x_119);
if (x_150 == 0)
{
x_141 = x_119;
x_142 = x_150;
goto block_149;
}
else
{
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_119);
x_141 = lean_box(0);
x_142 = x_150;
goto block_149;
}
block_149:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_string_append(x_139, x_113);
x_144 = lean_nat_add(x_140, x_114);
lean_dec(x_140);
if (x_142 == 0)
{
lean_ctor_set(x_141, 1, x_144);
lean_ctor_set(x_141, 0, x_143);
x_145 = x_141;
goto block_147;
}
else
{
lean_object* x_148; 
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_144);
x_145 = x_148;
goto block_147;
}
block_147:
{
x_2 = x_117;
x_3 = x_145;
goto _start;
}
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_117);
lean_dec(x_94);
lean_dec(x_16);
lean_dec(x_11);
x_151 = lean_ctor_get(x_116, 1);
lean_inc(x_151);
lean_dec_ref(x_116);
x_152 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0));
x_153 = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(x_152, x_151);
return x_153;
}
}
}
}
case 2:
{
uint8_t x_154; uint8_t x_155; 
lean_del_object(x_22);
lean_dec(x_21);
lean_del_object(x_17);
lean_del_object(x_12);
x_154 = lean_ctor_get_uint8(x_19, 0);
lean_dec_ref(x_19);
x_155 = l_Std_Format_FlattenAllowability_shouldFlatten(x_14);
if (x_155 == 0)
{
x_56 = x_155;
goto block_59;
}
else
{
if (x_154 == 0)
{
x_56 = x_155;
goto block_59;
}
else
{
goto block_55;
}
}
}
case 3:
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_214; 
lean_del_object(x_12);
x_156 = lean_ctor_get(x_19, 0);
x_214 = !lean_is_exclusive(x_19);
if (x_214 == 0)
{
x_157 = x_19;
x_158 = x_214;
goto block_213;
}
else
{
lean_inc(x_156);
lean_dec(x_19);
x_157 = lean_box(0);
x_158 = x_214;
goto block_213;
}
block_213:
{
uint32_t x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_159 = 10;
lean_inc_ref(x_156);
x_160 = lean_string_posof(x_156, x_159);
x_161 = lean_string_utf8_byte_size(x_156);
x_162 = lean_nat_dec_eq(x_160, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_197; 
x_163 = lean_ctor_get(x_3, 0);
x_197 = !lean_is_exclusive(x_3);
if (x_197 == 0)
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_3, 1);
lean_dec(x_198);
x_164 = x_3;
x_165 = x_197;
goto block_196;
}
else
{
lean_inc(x_163);
lean_dec(x_3);
x_164 = lean_box(0);
x_165 = x_197;
goto block_196;
}
block_196:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint32_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_166 = lean_unsigned_to_nat(0u);
x_167 = lean_string_utf8_extract(x_156, x_166, x_160);
x_168 = lean_string_append(x_163, x_167);
lean_dec_ref(x_167);
x_169 = l_Int_toNat(x_20);
x_170 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
x_171 = 32;
lean_inc(x_169);
x_172 = lean_string_pushn(x_170, x_171, x_169);
x_173 = lean_string_append(x_168, x_172);
lean_dec_ref(x_172);
if (x_165 == 0)
{
lean_ctor_set(x_164, 1, x_169);
lean_ctor_set(x_164, 0, x_173);
x_174 = x_164;
goto block_194;
}
else
{
lean_object* x_195; 
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_173);
lean_ctor_set(x_195, 1, x_169);
x_174 = x_195;
goto block_194;
}
block_194:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_string_utf8_next(x_156, x_160);
lean_dec(x_160);
x_176 = lean_string_utf8_extract(x_156, x_175, x_161);
lean_dec(x_175);
lean_dec_ref(x_156);
if (x_158 == 0)
{
lean_ctor_set(x_157, 0, x_176);
x_177 = x_157;
goto block_192;
}
else
{
lean_object* x_193; 
x_193 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_193, 0, x_176);
x_177 = x_193;
goto block_192;
}
block_192:
{
lean_object* x_178; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_177);
x_178 = x_22;
goto block_190;
}
else
{
lean_object* x_191; 
x_191 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_191, 0, x_177);
lean_ctor_set(x_191, 1, x_20);
lean_ctor_set(x_191, 2, x_21);
x_178 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_179; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_178);
x_179 = x_17;
goto block_188;
}
else
{
lean_object* x_189; 
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_178);
lean_ctor_set(x_189, 1, x_16);
x_179 = x_189;
goto block_188;
}
block_188:
{
lean_object* x_180; uint8_t x_181; 
x_180 = lean_box(1);
x_181 = l_Std_Format_instBEqFlattenAllowability_beq(x_14, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_14);
x_182 = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(x_15, x_179, x_11, x_1, x_174);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec_ref(x_182);
x_2 = x_183;
x_3 = x_184;
goto _start;
}
else
{
lean_object* x_186; 
x_186 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_14, x_15, x_11, x_179);
x_2 = x_186;
x_3 = x_174;
goto _start;
}
}
}
}
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; uint8_t x_212; 
lean_dec(x_160);
lean_del_object(x_157);
lean_del_object(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_del_object(x_17);
x_199 = lean_ctor_get(x_3, 0);
x_200 = lean_ctor_get(x_3, 1);
x_212 = !lean_is_exclusive(x_3);
if (x_212 == 0)
{
x_201 = x_3;
x_202 = x_212;
goto block_211;
}
else
{
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_3);
x_201 = lean_box(0);
x_202 = x_212;
goto block_211;
}
block_211:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_203 = lean_string_append(x_199, x_156);
x_204 = lean_string_length(x_156);
lean_dec_ref(x_156);
x_205 = lean_nat_add(x_200, x_204);
lean_dec(x_204);
lean_dec(x_200);
if (x_202 == 0)
{
lean_ctor_set(x_201, 1, x_205);
lean_ctor_set(x_201, 0, x_203);
x_206 = x_201;
goto block_209;
}
else
{
lean_object* x_210; 
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_203);
lean_ctor_set(x_210, 1, x_205);
x_206 = x_210;
goto block_209;
}
block_209:
{
lean_object* x_207; 
x_207 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_14, x_15, x_11, x_16);
x_2 = x_207;
x_3 = x_206;
goto _start;
}
}
}
}
}
case 4:
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_del_object(x_12);
x_215 = lean_ctor_get(x_19, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_19, 1);
lean_inc(x_216);
lean_dec_ref(x_19);
x_217 = lean_int_add(x_20, x_215);
lean_dec(x_215);
lean_dec(x_20);
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_217);
lean_ctor_set(x_22, 0, x_216);
x_218 = x_22;
goto block_224;
}
else
{
lean_object* x_225; 
x_225 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_225, 0, x_216);
lean_ctor_set(x_225, 1, x_217);
lean_ctor_set(x_225, 2, x_21);
x_218 = x_225;
goto block_224;
}
block_224:
{
lean_object* x_219; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_218);
x_219 = x_17;
goto block_222;
}
else
{
lean_object* x_223; 
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_218);
lean_ctor_set(x_223, 1, x_16);
x_219 = x_223;
goto block_222;
}
block_222:
{
lean_object* x_220; 
x_220 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_14, x_15, x_11, x_219);
x_2 = x_220;
goto _start;
}
}
}
case 5:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_226 = lean_ctor_get(x_19, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_19, 1);
lean_inc(x_227);
lean_dec_ref(x_19);
x_228 = lean_unsigned_to_nat(0u);
lean_inc(x_20);
if (x_23 == 0)
{
lean_ctor_set(x_22, 2, x_228);
lean_ctor_set(x_22, 0, x_226);
x_229 = x_22;
goto block_239;
}
else
{
lean_object* x_240; 
x_240 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_240, 0, x_226);
lean_ctor_set(x_240, 1, x_20);
lean_ctor_set(x_240, 2, x_228);
x_229 = x_240;
goto block_239;
}
block_239:
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_20);
lean_ctor_set(x_230, 2, x_21);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_230);
x_231 = x_17;
goto block_237;
}
else
{
lean_object* x_238; 
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_230);
lean_ctor_set(x_238, 1, x_16);
x_231 = x_238;
goto block_237;
}
block_237:
{
lean_object* x_232; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_231);
lean_ctor_set(x_12, 0, x_229);
x_232 = x_12;
goto block_235;
}
else
{
lean_object* x_236; 
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_229);
lean_ctor_set(x_236, 1, x_231);
x_232 = x_236;
goto block_235;
}
block_235:
{
lean_object* x_233; 
x_233 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_14, x_15, x_11, x_232);
x_2 = x_233;
goto _start;
}
}
}
}
case 6:
{
lean_object* x_241; uint8_t x_242; uint8_t x_243; 
lean_del_object(x_12);
x_241 = lean_ctor_get(x_19, 0);
lean_inc(x_241);
x_242 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
lean_dec_ref(x_19);
x_243 = l_Std_Format_FlattenAllowability_shouldFlatten(x_14);
if (x_243 == 0)
{
lean_object* x_244; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_241);
x_244 = x_22;
goto block_254;
}
else
{
lean_object* x_255; 
x_255 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_255, 0, x_241);
lean_ctor_set(x_255, 1, x_20);
lean_ctor_set(x_255, 2, x_21);
x_244 = x_255;
goto block_254;
}
block_254:
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_box(0);
if (x_18 == 0)
{
lean_ctor_set(x_17, 1, x_245);
lean_ctor_set(x_17, 0, x_244);
x_246 = x_17;
goto block_252;
}
else
{
lean_object* x_253; 
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_244);
lean_ctor_set(x_253, 1, x_245);
x_246 = x_253;
goto block_252;
}
block_252:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_247 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_14, x_15, x_11, x_16);
x_248 = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(x_242, x_246, x_247, x_1, x_3);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec_ref(x_248);
x_2 = x_249;
x_3 = x_250;
goto _start;
}
}
}
else
{
lean_object* x_256; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_241);
x_256 = x_22;
goto block_262;
}
else
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_263, 0, x_241);
lean_ctor_set(x_263, 1, x_20);
lean_ctor_set(x_263, 2, x_21);
x_256 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_257; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_256);
x_257 = x_17;
goto block_260;
}
else
{
lean_object* x_261; 
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_256);
lean_ctor_set(x_261, 1, x_16);
x_257 = x_261;
goto block_260;
}
block_260:
{
lean_object* x_258; 
x_258 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_14, x_15, x_11, x_257);
x_2 = x_258;
goto _start;
}
}
}
}
default: 
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_del_object(x_12);
x_264 = lean_ctor_get(x_19, 1);
lean_inc(x_264);
lean_dec_ref(x_19);
x_265 = lean_unsigned_to_nat(1u);
x_266 = lean_nat_add(x_21, x_265);
lean_dec(x_21);
if (x_23 == 0)
{
lean_ctor_set(x_22, 2, x_266);
lean_ctor_set(x_22, 0, x_264);
x_267 = x_22;
goto block_273;
}
else
{
lean_object* x_274; 
x_274 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_274, 0, x_264);
lean_ctor_set(x_274, 1, x_20);
lean_ctor_set(x_274, 2, x_266);
x_267 = x_274;
goto block_273;
}
block_273:
{
lean_object* x_268; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_267);
x_268 = x_17;
goto block_271;
}
else
{
lean_object* x_272; 
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_267);
lean_ctor_set(x_272, 1, x_16);
x_268 = x_272;
goto block_271;
}
block_271:
{
lean_object* x_269; 
x_269 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_14, x_15, x_11, x_268);
x_2 = x_269;
goto _start;
}
}
}
}
block_55:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_54; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_54 = !lean_is_exclusive(x_3);
if (x_54 == 0)
{
x_26 = x_3;
x_27 = x_54;
goto block_53;
}
else
{
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_26 = lean_box(0);
x_27 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_28; uint8_t x_29; 
lean_inc(x_25);
x_28 = lean_nat_to_int(x_25);
x_29 = lean_int_dec_lt(x_28, x_20);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint32_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_28);
lean_dec(x_25);
x_30 = l_Int_toNat(x_20);
lean_dec(x_20);
x_31 = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
x_32 = 32;
lean_inc(x_30);
x_33 = lean_string_pushn(x_31, x_32, x_30);
x_34 = lean_string_append(x_24, x_33);
lean_dec_ref(x_33);
if (x_27 == 0)
{
lean_ctor_set(x_26, 1, x_30);
lean_ctor_set(x_26, 0, x_34);
x_35 = x_26;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_30);
x_35 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_36; 
x_36 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_14, x_15, x_11, x_16);
x_2 = x_36;
x_3 = x_35;
goto _start;
}
}
else
{
lean_object* x_40; uint32_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
x_41 = 32;
x_42 = lean_int_sub(x_20, x_28);
lean_dec(x_28);
lean_dec(x_20);
x_43 = l_Int_toNat(x_42);
lean_dec(x_42);
x_44 = lean_string_pushn(x_40, x_41, x_43);
x_45 = lean_string_append(x_24, x_44);
x_46 = lean_string_length(x_44);
lean_dec_ref(x_44);
x_47 = lean_nat_add(x_25, x_46);
lean_dec(x_46);
lean_dec(x_25);
if (x_27 == 0)
{
lean_ctor_set(x_26, 1, x_47);
lean_ctor_set(x_26, 0, x_45);
x_48 = x_26;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_47);
x_48 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_49; 
x_49 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_14, x_15, x_11, x_16);
x_2 = x_49;
x_3 = x_48;
goto _start;
}
}
}
}
block_59:
{
if (x_56 == 0)
{
goto block_55;
}
else
{
lean_object* x_57; 
lean_dec(x_20);
x_57 = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(x_14, x_15, x_11, x_16);
x_2 = x_57;
goto _start;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_box(1);
x_6 = 0;
x_7 = lean_nat_to_int(x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(x_2, x_13, x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(x_1, x_2, x_3, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Format_pretty(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_instToFormatFormat___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatString___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_apply_1(x_1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_5);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_9 = lean_alloc_closure((void*)(l_Std_Format_joinSep___redArg___lam__0), 4, 2);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_1);
x_10 = lean_apply_1(x_1, x_8);
x_11 = l_List_foldl___redArg(x_9, x_10, x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Format_joinSep___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_16; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
x_7 = x_3;
x_8 = x_16;
goto block_15;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_1);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Std_Format_prefixJoin___redArg___lam__0), 4, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_1);
x_10 = lean_apply_1(x_1, x_5);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 5);
lean_ctor_set(x_7, 1, x_10);
lean_ctor_set(x_7, 0, x_2);
x_11 = x_7;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_10);
x_11 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_12; 
x_12 = l_List_foldl___redArg(x_9, x_11, x_6);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Format_prefixJoin___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_16; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
x_7 = x_2;
x_8 = x_16;
goto block_15;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_3);
lean_inc_ref(x_1);
x_9 = lean_alloc_closure((void*)(l_Std_Format_joinSuffix___redArg___lam__0), 4, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
x_10 = lean_apply_1(x_1, x_5);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 5);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 0, x_10);
x_11 = x_7;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_3);
x_11 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_12; 
x_12 = l_List_foldl___redArg(x_9, x_11, x_6);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Format_joinSuffix___redArg(x_2, x_3, x_4);
return x_5;
}
}
lean_object* runtime_initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_State(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Format_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Int_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Bootstrap(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_State(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Format_instInhabitedFlattenBehavior_default = _init_l_Std_Format_instInhabitedFlattenBehavior_default();
l_Std_Format_instInhabitedFlattenBehavior = _init_l_Std_Format_instInhabitedFlattenBehavior();
l_Std_instInhabitedFormat_default = _init_l_Std_instInhabitedFormat_default();
lean_mark_persistent(l_Std_instInhabitedFormat_default);
l_Std_instInhabitedFormat = _init_l_Std_instInhabitedFormat();
lean_mark_persistent(l_Std_instInhabitedFormat);
l_Std_Format_defIndent = _init_l_Std_Format_defIndent();
lean_mark_persistent(l_Std_Format_defIndent);
l_Std_Format_defUnicode = _init_l_Std_Format_defUnicode();
l_Std_Format_defWidth = _init_l_Std_Format_defWidth();
lean_mark_persistent(l_Std_Format_defWidth);
l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState = _init_l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState();
lean_mark_persistent(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Format_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Control_State(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Format_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Bootstrap(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_State(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Format_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Format_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
