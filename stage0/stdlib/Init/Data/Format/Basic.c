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
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_string_posof(lean_object*, uint32_t);
lean_object* lean_string_offsetofpos(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_get(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_string_pushn(lean_object*, uint32_t, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_merge(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_merge___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_spec__0(lean_object*);
static const lean_ctor_object l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unreachable"};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___closed__0 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__4 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__4_value;
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__5 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__5_value;
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__6 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__6_value;
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__7 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__7_value;
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__8 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__8_value;
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__9 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__9_value;
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__10 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__4_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__5_value)}};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__11 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__11_value;
static const lean_ctor_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__11_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__6_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__7_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__8_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__9_value)}};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__12 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__12_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__10_value)}};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value;
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_get, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value)} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__14 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__14_value;
static const lean_closure_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 7, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__14_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__2_value)} };
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__15 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__15_value;
static lean_once_cell_t l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16;
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState;
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value)} };
static const lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0 = (const lean_object*)&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__4, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value)} };
static const lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1 = (const lean_object*)&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__7, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value)} };
static const lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2 = (const lean_object*)&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__9, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value)} };
static const lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3 = (const lean_object*)&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_map, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value)} };
static const lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4 = (const lean_object*)&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_pure, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value)} };
static const lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5 = (const lean_object*)&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__13_value)} };
static const lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6 = (const lean_object*)&l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6_value;
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
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorIdx(uint8_t v_x_1_){
_start:
{
if (v_x_1_ == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_Format_FlattenBehavior_ctorIdx(v_x_boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_toCtorIdx(uint8_t v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Std_Format_FlattenBehavior_ctorIdx(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_toCtorIdx___boxed(lean_object* v_x_9_){
_start:
{
uint8_t v_x_4__boxed_10_; lean_object* v_res_11_; 
v_x_4__boxed_10_ = lean_unbox(v_x_9_);
v_res_11_ = l_Std_Format_FlattenBehavior_toCtorIdx(v_x_4__boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim___redArg(lean_object* v_k_12_){
_start:
{
lean_inc(v_k_12_);
return v_k_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim___redArg___boxed(lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Format_FlattenBehavior_ctorElim___redArg(v_k_13_);
lean_dec(v_k_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, uint8_t v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_inc(v_k_19_);
return v_k_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
uint8_t v_t_boxed_25_; lean_object* v_res_26_; 
v_t_boxed_25_ = lean_unbox(v_t_22_);
v_res_26_ = l_Std_Format_FlattenBehavior_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_boxed_25_, v_h_23_, v_k_24_);
lean_dec(v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim___redArg(lean_object* v_allOrNone_27_){
_start:
{
lean_inc(v_allOrNone_27_);
return v_allOrNone_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim___redArg___boxed(lean_object* v_allOrNone_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_Format_FlattenBehavior_allOrNone_elim___redArg(v_allOrNone_28_);
lean_dec(v_allOrNone_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim(lean_object* v_motive_30_, uint8_t v_t_31_, lean_object* v_h_32_, lean_object* v_allOrNone_33_){
_start:
{
lean_inc(v_allOrNone_33_);
return v_allOrNone_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim___boxed(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_allOrNone_37_){
_start:
{
uint8_t v_t_boxed_38_; lean_object* v_res_39_; 
v_t_boxed_38_ = lean_unbox(v_t_35_);
v_res_39_ = l_Std_Format_FlattenBehavior_allOrNone_elim(v_motive_34_, v_t_boxed_38_, v_h_36_, v_allOrNone_37_);
lean_dec(v_allOrNone_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim___redArg(lean_object* v_fill_40_){
_start:
{
lean_inc(v_fill_40_);
return v_fill_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim___redArg___boxed(lean_object* v_fill_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Std_Format_FlattenBehavior_fill_elim___redArg(v_fill_41_);
lean_dec(v_fill_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim(lean_object* v_motive_43_, uint8_t v_t_44_, lean_object* v_h_45_, lean_object* v_fill_46_){
_start:
{
lean_inc(v_fill_46_);
return v_fill_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim___boxed(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_fill_50_){
_start:
{
uint8_t v_t_boxed_51_; lean_object* v_res_52_; 
v_t_boxed_51_ = lean_unbox(v_t_48_);
v_res_52_ = l_Std_Format_FlattenBehavior_fill_elim(v_motive_47_, v_t_boxed_51_, v_h_49_, v_fill_50_);
lean_dec(v_fill_50_);
return v_res_52_;
}
}
static uint8_t _init_l_Std_Format_instInhabitedFlattenBehavior_default(void){
_start:
{
uint8_t v___x_53_; 
v___x_53_ = 0;
return v___x_53_;
}
}
static uint8_t _init_l_Std_Format_instInhabitedFlattenBehavior(void){
_start:
{
uint8_t v___x_54_; 
v___x_54_ = 0;
return v___x_54_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_instBEqFlattenBehavior_beq(uint8_t v_x_55_, uint8_t v_y_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_57_ = l_Std_Format_FlattenBehavior_ctorIdx(v_x_55_);
v___x_58_ = l_Std_Format_FlattenBehavior_ctorIdx(v_y_56_);
v___x_59_ = lean_nat_dec_eq(v___x_57_, v___x_58_);
lean_dec(v___x_58_);
lean_dec(v___x_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_instBEqFlattenBehavior_beq___boxed(lean_object* v_x_60_, lean_object* v_y_61_){
_start:
{
uint8_t v_x_17__boxed_62_; uint8_t v_y_18__boxed_63_; uint8_t v_res_64_; lean_object* v_r_65_; 
v_x_17__boxed_62_ = lean_unbox(v_x_60_);
v_y_18__boxed_63_ = lean_unbox(v_y_61_);
v_res_64_ = l_Std_Format_instBEqFlattenBehavior_beq(v_x_17__boxed_62_, v_y_18__boxed_63_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorIdx(lean_object* v_x_68_){
_start:
{
switch(lean_obj_tag(v_x_68_))
{
case 0:
{
lean_object* v___x_69_; 
v___x_69_ = lean_unsigned_to_nat(0u);
return v___x_69_;
}
case 1:
{
lean_object* v___x_70_; 
v___x_70_ = lean_unsigned_to_nat(1u);
return v___x_70_;
}
case 2:
{
lean_object* v___x_71_; 
v___x_71_ = lean_unsigned_to_nat(2u);
return v___x_71_;
}
case 3:
{
lean_object* v___x_72_; 
v___x_72_ = lean_unsigned_to_nat(3u);
return v___x_72_;
}
case 4:
{
lean_object* v___x_73_; 
v___x_73_ = lean_unsigned_to_nat(4u);
return v___x_73_;
}
case 5:
{
lean_object* v___x_74_; 
v___x_74_ = lean_unsigned_to_nat(5u);
return v___x_74_;
}
case 6:
{
lean_object* v___x_75_; 
v___x_75_ = lean_unsigned_to_nat(6u);
return v___x_75_;
}
default: 
{
lean_object* v___x_76_; 
v___x_76_ = lean_unsigned_to_nat(7u);
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorIdx___boxed(lean_object* v_x_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Std_Format_ctorIdx(v_x_77_);
lean_dec(v_x_77_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorElim___redArg(lean_object* v_t_79_, lean_object* v_k_80_){
_start:
{
switch(lean_obj_tag(v_t_79_))
{
case 2:
{
uint8_t v_force_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_force_81_ = lean_ctor_get_uint8(v_t_79_, 0);
lean_dec_ref(v_t_79_);
v___x_82_ = lean_box(v_force_81_);
v___x_83_ = lean_apply_1(v_k_80_, v___x_82_);
return v___x_83_;
}
case 3:
{
lean_object* v_a_84_; lean_object* v___x_85_; 
v_a_84_ = lean_ctor_get(v_t_79_, 0);
lean_inc_ref(v_a_84_);
lean_dec_ref(v_t_79_);
v___x_85_ = lean_apply_1(v_k_80_, v_a_84_);
return v___x_85_;
}
case 4:
{
lean_object* v_indent_86_; lean_object* v_f_87_; lean_object* v___x_88_; 
v_indent_86_ = lean_ctor_get(v_t_79_, 0);
lean_inc(v_indent_86_);
v_f_87_ = lean_ctor_get(v_t_79_, 1);
lean_inc(v_f_87_);
lean_dec_ref(v_t_79_);
v___x_88_ = lean_apply_2(v_k_80_, v_indent_86_, v_f_87_);
return v___x_88_;
}
case 5:
{
lean_object* v_a_89_; lean_object* v_a_90_; lean_object* v___x_91_; 
v_a_89_ = lean_ctor_get(v_t_79_, 0);
lean_inc(v_a_89_);
v_a_90_ = lean_ctor_get(v_t_79_, 1);
lean_inc(v_a_90_);
lean_dec_ref(v_t_79_);
v___x_91_ = lean_apply_2(v_k_80_, v_a_89_, v_a_90_);
return v___x_91_;
}
case 6:
{
lean_object* v_a_92_; uint8_t v_behavior_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_a_92_ = lean_ctor_get(v_t_79_, 0);
lean_inc(v_a_92_);
v_behavior_93_ = lean_ctor_get_uint8(v_t_79_, sizeof(void*)*1);
lean_dec_ref(v_t_79_);
v___x_94_ = lean_box(v_behavior_93_);
v___x_95_ = lean_apply_2(v_k_80_, v_a_92_, v___x_94_);
return v___x_95_;
}
case 7:
{
lean_object* v_a_96_; lean_object* v_a_97_; lean_object* v___x_98_; 
v_a_96_ = lean_ctor_get(v_t_79_, 0);
lean_inc(v_a_96_);
v_a_97_ = lean_ctor_get(v_t_79_, 1);
lean_inc(v_a_97_);
lean_dec_ref(v_t_79_);
v___x_98_ = lean_apply_2(v_k_80_, v_a_96_, v_a_97_);
return v___x_98_;
}
default: 
{
lean_dec(v_t_79_);
return v_k_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorElim(lean_object* v_motive_99_, lean_object* v_ctorIdx_100_, lean_object* v_t_101_, lean_object* v_h_102_, lean_object* v_k_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Std_Format_ctorElim___redArg(v_t_101_, v_k_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorElim___boxed(lean_object* v_motive_105_, lean_object* v_ctorIdx_106_, lean_object* v_t_107_, lean_object* v_h_108_, lean_object* v_k_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_Format_ctorElim(v_motive_105_, v_ctorIdx_106_, v_t_107_, v_h_108_, v_k_109_);
lean_dec(v_ctorIdx_106_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nil_elim___redArg(lean_object* v_t_111_, lean_object* v_nil_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Std_Format_ctorElim___redArg(v_t_111_, v_nil_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nil_elim(lean_object* v_motive_114_, lean_object* v_t_115_, lean_object* v_h_116_, lean_object* v_nil_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Std_Format_ctorElim___redArg(v_t_115_, v_nil_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_line_elim___redArg(lean_object* v_t_119_, lean_object* v_line_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Std_Format_ctorElim___redArg(v_t_119_, v_line_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_line_elim(lean_object* v_motive_122_, lean_object* v_t_123_, lean_object* v_h_124_, lean_object* v_line_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Std_Format_ctorElim___redArg(v_t_123_, v_line_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_align_elim___redArg(lean_object* v_t_127_, lean_object* v_align_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Std_Format_ctorElim___redArg(v_t_127_, v_align_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_align_elim(lean_object* v_motive_130_, lean_object* v_t_131_, lean_object* v_h_132_, lean_object* v_align_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Std_Format_ctorElim___redArg(v_t_131_, v_align_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_text_elim___redArg(lean_object* v_t_135_, lean_object* v_text_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Std_Format_ctorElim___redArg(v_t_135_, v_text_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_text_elim(lean_object* v_motive_138_, lean_object* v_t_139_, lean_object* v_h_140_, lean_object* v_text_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Std_Format_ctorElim___redArg(v_t_139_, v_text_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nest_elim___redArg(lean_object* v_t_143_, lean_object* v_nest_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Std_Format_ctorElim___redArg(v_t_143_, v_nest_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nest_elim(lean_object* v_motive_146_, lean_object* v_t_147_, lean_object* v_h_148_, lean_object* v_nest_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Std_Format_ctorElim___redArg(v_t_147_, v_nest_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_append_elim___redArg(lean_object* v_t_151_, lean_object* v_append_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Std_Format_ctorElim___redArg(v_t_151_, v_append_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_append_elim(lean_object* v_motive_154_, lean_object* v_t_155_, lean_object* v_h_156_, lean_object* v_append_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Std_Format_ctorElim___redArg(v_t_155_, v_append_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_group_elim___redArg(lean_object* v_t_159_, lean_object* v_group_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Std_Format_ctorElim___redArg(v_t_159_, v_group_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_group_elim(lean_object* v_motive_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_group_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Std_Format_ctorElim___redArg(v_t_163_, v_group_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_tag_elim___redArg(lean_object* v_t_167_, lean_object* v_tag_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Std_Format_ctorElim___redArg(v_t_167_, v_tag_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_tag_elim(lean_object* v_motive_170_, lean_object* v_t_171_, lean_object* v_h_172_, lean_object* v_tag_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Std_Format_ctorElim___redArg(v_t_171_, v_tag_173_);
return v___x_174_;
}
}
static lean_object* _init_l_Std_instInhabitedFormat_default(void){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_box(0);
return v___x_175_;
}
}
static lean_object* _init_l_Std_instInhabitedFormat(void){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_box(0);
return v___x_176_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_isEmpty(lean_object* v_x_178_){
_start:
{
switch(lean_obj_tag(v_x_178_))
{
case 1:
{
uint8_t v___x_179_; 
v___x_179_ = 0;
return v___x_179_;
}
case 3:
{
lean_object* v_a_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_a_180_ = lean_ctor_get(v_x_178_, 0);
v___x_181_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_182_ = lean_string_dec_eq(v_a_180_, v___x_181_);
return v___x_182_;
}
case 4:
{
lean_object* v_f_183_; 
v_f_183_ = lean_ctor_get(v_x_178_, 1);
v_x_178_ = v_f_183_;
goto _start;
}
case 5:
{
lean_object* v_a_185_; lean_object* v_a_186_; uint8_t v___x_187_; 
v_a_185_ = lean_ctor_get(v_x_178_, 0);
v_a_186_ = lean_ctor_get(v_x_178_, 1);
v___x_187_ = l_Std_Format_isEmpty(v_a_185_);
if (v___x_187_ == 0)
{
return v___x_187_;
}
else
{
v_x_178_ = v_a_186_;
goto _start;
}
}
case 6:
{
lean_object* v_a_189_; 
v_a_189_ = lean_ctor_get(v_x_178_, 0);
v_x_178_ = v_a_189_;
goto _start;
}
case 7:
{
lean_object* v_a_191_; 
v_a_191_ = lean_ctor_get(v_x_178_, 1);
v_x_178_ = v_a_191_;
goto _start;
}
default: 
{
uint8_t v___x_193_; 
v___x_193_ = 1;
return v___x_193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_isEmpty___boxed(lean_object* v_x_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Std_Format_isEmpty(v_x_194_);
lean_dec(v_x_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_fill(lean_object* v_f_197_){
_start:
{
uint8_t v___x_198_; lean_object* v___x_199_; 
v___x_198_ = 1;
v___x_199_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_199_, 0, v_f_197_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*1, v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_instAppend___lam__0(lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_202_, 0, v_a_200_);
lean_ctor_set(v___x_202_, 1, v_a_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_instCoeString___lam__0(lean_object* v_a_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_206_, 0, v_a_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_join_spec__0(lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
if (lean_obj_tag(v_x_210_) == 0)
{
return v_x_209_;
}
else
{
lean_object* v_head_211_; lean_object* v_tail_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_220_; 
v_head_211_ = lean_ctor_get(v_x_210_, 0);
v_tail_212_ = lean_ctor_get(v_x_210_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_220_ == 0)
{
v___x_214_ = v_x_210_;
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_tail_212_);
lean_inc(v_head_211_);
lean_dec(v_x_210_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 5);
lean_ctor_set(v___x_214_, 1, v_head_211_);
lean_ctor_set(v___x_214_, 0, v_x_209_);
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_x_209_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_head_211_);
v___x_217_ = v_reuseFailAlloc_219_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
v_x_209_ = v___x_217_;
v_x_210_ = v_tail_212_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_join(lean_object* v_xs_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l_Std_Format_join___closed__0));
v___x_225_ = l_List_foldl___at___00Std_Format_join_spec__0(v___x_224_, v_xs_223_);
return v___x_225_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_isNil(lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
uint8_t v___x_227_; 
v___x_227_ = 1;
return v___x_227_;
}
else
{
uint8_t v___x_228_; 
v___x_228_ = 0;
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_isNil___boxed(lean_object* v_x_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l_Std_Format_isNil(v_x_229_);
lean_dec(v_x_229_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_merge(lean_object* v_w_237_, lean_object* v_r_u2081_238_, lean_object* v_r_u2082_239_){
_start:
{
uint8_t v_foundLine_240_; lean_object* v_space_241_; uint8_t v___y_243_; uint8_t v___x_257_; 
v_foundLine_240_ = lean_ctor_get_uint8(v_r_u2081_238_, sizeof(void*)*1);
v_space_241_ = lean_ctor_get(v_r_u2081_238_, 0);
v___x_257_ = lean_nat_dec_lt(v_w_237_, v_space_241_);
if (v___x_257_ == 0)
{
v___y_243_ = v_foundLine_240_;
goto v___jp_242_;
}
else
{
v___y_243_ = v___x_257_;
goto v___jp_242_;
}
v___jp_242_:
{
if (v___y_243_ == 0)
{
lean_object* v___x_244_; lean_object* v_r_u2082_245_; uint8_t v_foundLine_246_; uint8_t v_foundFlattenedHardLine_247_; lean_object* v_space_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_256_; 
v___x_244_ = lean_nat_sub(v_w_237_, v_space_241_);
v_r_u2082_245_ = lean_apply_1(v_r_u2082_239_, v___x_244_);
v_foundLine_246_ = lean_ctor_get_uint8(v_r_u2082_245_, sizeof(void*)*1);
v_foundFlattenedHardLine_247_ = lean_ctor_get_uint8(v_r_u2082_245_, sizeof(void*)*1 + 1);
v_space_248_ = lean_ctor_get(v_r_u2082_245_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v_r_u2082_245_);
if (v_isSharedCheck_256_ == 0)
{
v___x_250_ = v_r_u2082_245_;
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_space_248_);
lean_dec(v_r_u2082_245_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_252_ = lean_nat_add(v_space_241_, v_space_248_);
lean_dec(v_space_248_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v___x_252_);
v___x_254_ = v___x_250_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
lean_ctor_set_uint8(v_reuseFailAlloc_255_, sizeof(void*)*1, v_foundLine_246_);
lean_ctor_set_uint8(v_reuseFailAlloc_255_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_247_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
else
{
lean_dec_ref(v_r_u2082_239_);
lean_inc_ref(v_r_u2081_238_);
return v_r_u2081_238_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_merge___boxed(lean_object* v_w_258_, lean_object* v_r_u2081_259_, lean_object* v_r_u2082_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Init_Data_Format_Basic_0__Std_Format_merge(v_w_258_, v_r_u2081_259_, v_r_u2082_260_);
lean_dec_ref(v_r_u2081_259_);
lean_dec(v_w_258_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_spec__0(lean_object* v_a_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lean_nat_to_int(v_a_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(lean_object* v_x_267_, uint8_t v_x_268_, lean_object* v_x_269_, lean_object* v_x_270_){
_start:
{
uint8_t v___y_272_; 
switch(lean_obj_tag(v_x_267_))
{
case 0:
{
lean_object* v___x_281_; 
lean_dec(v_x_270_);
lean_dec(v_x_269_);
v___x_281_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instInhabitedSpaceResult_default___closed__0));
return v___x_281_;
}
case 1:
{
lean_dec(v_x_270_);
lean_dec(v_x_269_);
if (v_x_268_ == 0)
{
uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = 1;
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*1, v___x_282_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*1 + 1, v_x_268_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; 
v___x_285_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0));
return v___x_285_;
}
}
case 2:
{
if (v_x_268_ == 0)
{
lean_dec_ref(v_x_267_);
v___y_272_ = v_x_268_;
goto v___jp_271_;
}
else
{
uint8_t v_force_286_; 
v_force_286_ = lean_ctor_get_uint8(v_x_267_, 0);
lean_dec_ref(v_x_267_);
if (v_force_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec(v_x_270_);
lean_dec(v_x_269_);
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*1, v_force_286_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*1 + 1, v_force_286_);
return v___x_288_;
}
else
{
uint8_t v___x_289_; 
v___x_289_ = 0;
v___y_272_ = v___x_289_;
goto v___jp_271_;
}
}
}
case 3:
{
lean_object* v_a_290_; uint32_t v___x_291_; lean_object* v_p_292_; lean_object* v_off_293_; uint8_t v___y_295_; lean_object* v___x_298_; uint8_t v___x_299_; 
lean_dec(v_x_270_);
lean_dec(v_x_269_);
v_a_290_ = lean_ctor_get(v_x_267_, 0);
lean_inc_ref(v_a_290_);
lean_dec_ref(v_x_267_);
v___x_291_ = 10;
lean_inc_ref(v_a_290_);
v_p_292_ = lean_string_posof(v_a_290_, v___x_291_);
lean_inc(v_p_292_);
lean_inc_ref(v_a_290_);
v_off_293_ = lean_string_offsetofpos(v_a_290_, v_p_292_);
v___x_298_ = lean_string_utf8_byte_size(v_a_290_);
lean_dec_ref(v_a_290_);
v___x_299_ = lean_nat_dec_eq(v_p_292_, v___x_298_);
lean_dec(v_p_292_);
if (v___x_299_ == 0)
{
uint8_t v___x_300_; 
v___x_300_ = 1;
v___y_295_ = v___x_300_;
goto v___jp_294_;
}
else
{
uint8_t v___x_301_; 
v___x_301_ = 0;
v___y_295_ = v___x_301_;
goto v___jp_294_;
}
v___jp_294_:
{
if (v_x_268_ == 0)
{
lean_object* v___x_296_; 
v___x_296_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_296_, 0, v_off_293_);
lean_ctor_set_uint8(v___x_296_, sizeof(void*)*1, v___y_295_);
lean_ctor_set_uint8(v___x_296_, sizeof(void*)*1 + 1, v_x_268_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; 
v___x_297_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_297_, 0, v_off_293_);
lean_ctor_set_uint8(v___x_297_, sizeof(void*)*1, v___y_295_);
lean_ctor_set_uint8(v___x_297_, sizeof(void*)*1 + 1, v___y_295_);
return v___x_297_;
}
}
}
case 4:
{
lean_object* v_indent_302_; lean_object* v_f_303_; lean_object* v___x_304_; 
v_indent_302_ = lean_ctor_get(v_x_267_, 0);
lean_inc(v_indent_302_);
v_f_303_ = lean_ctor_get(v_x_267_, 1);
lean_inc(v_f_303_);
lean_dec_ref(v_x_267_);
v___x_304_ = lean_int_sub(v_x_269_, v_indent_302_);
lean_dec(v_indent_302_);
lean_dec(v_x_269_);
v_x_267_ = v_f_303_;
v_x_269_ = v___x_304_;
goto _start;
}
case 5:
{
lean_object* v_a_306_; lean_object* v_a_307_; lean_object* v___x_308_; uint8_t v_foundLine_309_; lean_object* v_space_310_; uint8_t v___y_312_; uint8_t v___x_326_; 
v_a_306_ = lean_ctor_get(v_x_267_, 0);
lean_inc(v_a_306_);
v_a_307_ = lean_ctor_get(v_x_267_, 1);
lean_inc(v_a_307_);
lean_dec_ref(v_x_267_);
lean_inc(v_x_270_);
lean_inc(v_x_269_);
v___x_308_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_a_306_, v_x_268_, v_x_269_, v_x_270_);
v_foundLine_309_ = lean_ctor_get_uint8(v___x_308_, sizeof(void*)*1);
v_space_310_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_space_310_);
v___x_326_ = lean_nat_dec_lt(v_x_270_, v_space_310_);
if (v___x_326_ == 0)
{
v___y_312_ = v_foundLine_309_;
goto v___jp_311_;
}
else
{
v___y_312_ = v___x_326_;
goto v___jp_311_;
}
v___jp_311_:
{
if (v___y_312_ == 0)
{
lean_object* v___x_313_; lean_object* v_r_u2082_314_; uint8_t v_foundLine_315_; uint8_t v_foundFlattenedHardLine_316_; lean_object* v_space_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_325_; 
lean_dec_ref(v___x_308_);
v___x_313_ = lean_nat_sub(v_x_270_, v_space_310_);
lean_dec(v_x_270_);
v_r_u2082_314_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_a_307_, v_x_268_, v_x_269_, v___x_313_);
v_foundLine_315_ = lean_ctor_get_uint8(v_r_u2082_314_, sizeof(void*)*1);
v_foundFlattenedHardLine_316_ = lean_ctor_get_uint8(v_r_u2082_314_, sizeof(void*)*1 + 1);
v_space_317_ = lean_ctor_get(v_r_u2082_314_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v_r_u2082_314_);
if (v_isSharedCheck_325_ == 0)
{
v___x_319_ = v_r_u2082_314_;
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_space_317_);
lean_dec(v_r_u2082_314_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_321_ = lean_nat_add(v_space_310_, v_space_317_);
lean_dec(v_space_317_);
lean_dec(v_space_310_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_321_);
v___x_323_ = v___x_319_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
lean_ctor_set_uint8(v_reuseFailAlloc_324_, sizeof(void*)*1, v_foundLine_315_);
lean_ctor_set_uint8(v_reuseFailAlloc_324_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_316_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
else
{
lean_dec(v_space_310_);
lean_dec(v_a_307_);
lean_dec(v_x_270_);
lean_dec(v_x_269_);
return v___x_308_;
}
}
}
case 6:
{
lean_object* v_a_327_; uint8_t v___x_328_; 
v_a_327_ = lean_ctor_get(v_x_267_, 0);
lean_inc(v_a_327_);
lean_dec_ref(v_x_267_);
v___x_328_ = 1;
v_x_267_ = v_a_327_;
v_x_268_ = v___x_328_;
goto _start;
}
default: 
{
lean_object* v_a_330_; 
v_a_330_ = lean_ctor_get(v_x_267_, 1);
lean_inc(v_a_330_);
lean_dec_ref(v_x_267_);
v_x_267_ = v_a_330_;
goto _start;
}
}
v___jp_271_:
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = lean_nat_to_int(v_x_270_);
v___x_274_ = lean_int_dec_lt(v___x_273_, v_x_269_);
if (v___x_274_ == 0)
{
uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec(v___x_273_);
lean_dec(v_x_269_);
v___x_275_ = 1;
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*1, v___x_275_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*1 + 1, v___y_272_);
return v___x_277_;
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = lean_int_sub(v_x_269_, v___x_273_);
lean_dec(v___x_273_);
lean_dec(v_x_269_);
v___x_279_ = l_Int_toNat(v___x_278_);
lean_dec(v___x_278_);
v___x_280_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set_uint8(v___x_280_, sizeof(void*)*1, v___y_272_);
lean_ctor_set_uint8(v___x_280_, sizeof(void*)*1 + 1, v___y_272_);
return v___x_280_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___boxed(lean_object* v_x_332_, lean_object* v_x_333_, lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
uint8_t v_x_414__boxed_336_; lean_object* v_res_337_; 
v_x_414__boxed_336_ = lean_unbox(v_x_333_);
v_res_337_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_x_332_, v_x_414__boxed_336_, v_x_334_, v_x_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx(lean_object* v_x_338_){
_start:
{
if (lean_obj_tag(v_x_338_) == 0)
{
lean_object* v___x_339_; 
v___x_339_ = lean_unsigned_to_nat(0u);
return v___x_339_;
}
else
{
lean_object* v___x_340_; 
v___x_340_ = lean_unsigned_to_nat(1u);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx___boxed(lean_object* v_x_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_Format_FlattenAllowability_ctorIdx(v_x_341_);
lean_dec(v_x_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___redArg(lean_object* v_t_343_, lean_object* v_k_344_){
_start:
{
if (lean_obj_tag(v_t_343_) == 0)
{
uint8_t v_fits_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_fits_345_ = lean_ctor_get_uint8(v_t_343_, 0);
v___x_346_ = lean_box(v_fits_345_);
v___x_347_ = lean_apply_1(v_k_344_, v___x_346_);
return v___x_347_;
}
else
{
return v_k_344_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___redArg___boxed(lean_object* v_t_348_, lean_object* v_k_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_348_, v_k_349_);
lean_dec(v_t_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim(lean_object* v_motive_351_, lean_object* v_ctorIdx_352_, lean_object* v_t_353_, lean_object* v_h_354_, lean_object* v_k_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_353_, v_k_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___boxed(lean_object* v_motive_357_, lean_object* v_ctorIdx_358_, lean_object* v_t_359_, lean_object* v_h_360_, lean_object* v_k_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Std_Format_FlattenAllowability_ctorElim(v_motive_357_, v_ctorIdx_358_, v_t_359_, v_h_360_, v_k_361_);
lean_dec(v_t_359_);
lean_dec(v_ctorIdx_358_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___redArg(lean_object* v_t_363_, lean_object* v_allow_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_363_, v_allow_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___redArg___boxed(lean_object* v_t_366_, lean_object* v_allow_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Std_Format_FlattenAllowability_allow_elim___redArg(v_t_366_, v_allow_367_);
lean_dec(v_t_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim(lean_object* v_motive_369_, lean_object* v_t_370_, lean_object* v_h_371_, lean_object* v_allow_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_370_, v_allow_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___boxed(lean_object* v_motive_374_, lean_object* v_t_375_, lean_object* v_h_376_, lean_object* v_allow_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Std_Format_FlattenAllowability_allow_elim(v_motive_374_, v_t_375_, v_h_376_, v_allow_377_);
lean_dec(v_t_375_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___redArg(lean_object* v_t_379_, lean_object* v_disallow_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_379_, v_disallow_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___redArg___boxed(lean_object* v_t_382_, lean_object* v_disallow_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Std_Format_FlattenAllowability_disallow_elim___redArg(v_t_382_, v_disallow_383_);
lean_dec(v_t_382_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim(lean_object* v_motive_385_, lean_object* v_t_386_, lean_object* v_h_387_, lean_object* v_disallow_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_386_, v_disallow_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___boxed(lean_object* v_motive_390_, lean_object* v_t_391_, lean_object* v_h_392_, lean_object* v_disallow_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_Format_FlattenAllowability_disallow_elim(v_motive_390_, v_t_391_, v_h_392_, v_disallow_393_);
lean_dec(v_t_391_);
return v_res_394_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_instBEqFlattenAllowability_beq(lean_object* v_x_395_, lean_object* v_x_396_){
_start:
{
if (lean_obj_tag(v_x_395_) == 0)
{
if (lean_obj_tag(v_x_396_) == 0)
{
uint8_t v_fits_397_; 
v_fits_397_ = lean_ctor_get_uint8(v_x_395_, 0);
if (v_fits_397_ == 0)
{
uint8_t v_fits_398_; 
v_fits_398_ = lean_ctor_get_uint8(v_x_396_, 0);
if (v_fits_398_ == 0)
{
uint8_t v___x_399_; 
v___x_399_ = 1;
return v___x_399_;
}
else
{
return v_fits_397_;
}
}
else
{
uint8_t v_fits_400_; 
v_fits_400_ = lean_ctor_get_uint8(v_x_396_, 0);
return v_fits_400_;
}
}
else
{
uint8_t v___x_401_; 
v___x_401_ = 0;
return v___x_401_;
}
}
else
{
if (lean_obj_tag(v_x_396_) == 1)
{
uint8_t v___x_402_; 
v___x_402_ = 1;
return v___x_402_;
}
else
{
uint8_t v___x_403_; 
v___x_403_ = 0;
return v___x_403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_instBEqFlattenAllowability_beq___boxed(lean_object* v_x_404_, lean_object* v_x_405_){
_start:
{
uint8_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l_Std_Format_instBEqFlattenAllowability_beq(v_x_404_, v_x_405_);
lean_dec(v_x_405_);
lean_dec(v_x_404_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_FlattenAllowability_shouldFlatten(lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
uint8_t v_fits_411_; 
v_fits_411_ = lean_ctor_get_uint8(v_x_410_, 0);
if (v_fits_411_ == 1)
{
return v_fits_411_;
}
else
{
uint8_t v___x_412_; 
v___x_412_ = 0;
return v___x_412_;
}
}
else
{
uint8_t v___x_413_; 
v___x_413_ = 0;
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_shouldFlatten___boxed(lean_object* v_x_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_x_414_);
lean_dec(v_x_414_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
if (lean_obj_tag(v_x_417_) == 0)
{
lean_object* v___x_420_; 
lean_dec(v_x_419_);
lean_dec(v_x_418_);
v___x_420_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instInhabitedSpaceResult_default___closed__0));
return v___x_420_;
}
else
{
lean_object* v_head_421_; lean_object* v_items_422_; 
v_head_421_ = lean_ctor_get(v_x_417_, 0);
lean_inc(v_head_421_);
v_items_422_ = lean_ctor_get(v_head_421_, 1);
lean_inc(v_items_422_);
if (lean_obj_tag(v_items_422_) == 0)
{
lean_object* v_tail_423_; 
lean_dec(v_head_421_);
v_tail_423_ = lean_ctor_get(v_x_417_, 1);
lean_inc(v_tail_423_);
lean_dec_ref(v_x_417_);
v_x_417_ = v_tail_423_;
goto _start;
}
else
{
lean_object* v_head_425_; lean_object* v_tail_426_; lean_object* v_fla_427_; uint8_t v_flb_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_470_; 
v_head_425_ = lean_ctor_get(v_items_422_, 0);
lean_inc(v_head_425_);
v_tail_426_ = lean_ctor_get(v_x_417_, 1);
lean_inc(v_tail_426_);
lean_dec_ref(v_x_417_);
v_fla_427_ = lean_ctor_get(v_head_421_, 0);
v_flb_428_ = lean_ctor_get_uint8(v_head_421_, sizeof(void*)*2);
v_isSharedCheck_470_ = !lean_is_exclusive(v_head_421_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v_head_421_, 1);
lean_dec(v_unused_471_);
v___x_430_ = v_head_421_;
v_isShared_431_ = v_isSharedCheck_470_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_fla_427_);
lean_dec(v_head_421_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_470_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v_tail_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_468_; 
v_tail_432_ = lean_ctor_get(v_items_422_, 1);
v_isSharedCheck_468_ = !lean_is_exclusive(v_items_422_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; 
v_unused_469_ = lean_ctor_get(v_items_422_, 0);
lean_dec(v_unused_469_);
v___x_434_ = v_items_422_;
v_isShared_435_ = v_isSharedCheck_468_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_tail_432_);
lean_dec(v_items_422_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_468_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_f_436_; lean_object* v_indent_437_; uint8_t v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v_foundLine_444_; lean_object* v_space_445_; lean_object* v___x_447_; 
v_f_436_ = lean_ctor_get(v_head_425_, 0);
lean_inc(v_f_436_);
v_indent_437_ = lean_ctor_get(v_head_425_, 1);
lean_inc(v_indent_437_);
lean_dec(v_head_425_);
v___x_438_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_427_);
lean_inc(v_x_419_);
v___x_439_ = lean_nat_to_int(v_x_419_);
lean_inc(v_x_418_);
v___x_440_ = lean_nat_to_int(v_x_418_);
v___x_441_ = lean_int_add(v___x_439_, v___x_440_);
lean_dec(v___x_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_int_sub(v___x_441_, v_indent_437_);
lean_dec(v_indent_437_);
lean_dec(v___x_441_);
lean_inc(v_x_419_);
v___x_443_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_f_436_, v___x_438_, v___x_442_, v_x_419_);
v_foundLine_444_ = lean_ctor_get_uint8(v___x_443_, sizeof(void*)*1);
v_space_445_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_space_445_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v_tail_432_);
v___x_447_ = v___x_430_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_fla_427_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_tail_432_);
lean_ctor_set_uint8(v_reuseFailAlloc_467_, sizeof(void*)*2, v_flb_428_);
v___x_447_ = v_reuseFailAlloc_467_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_449_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v_tail_426_);
lean_ctor_set(v___x_434_, 0, v___x_447_);
v___x_449_ = v___x_434_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_447_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_tail_426_);
v___x_449_ = v_reuseFailAlloc_466_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
uint8_t v___y_451_; uint8_t v___x_465_; 
v___x_465_ = lean_nat_dec_lt(v_x_419_, v_space_445_);
if (v___x_465_ == 0)
{
v___y_451_ = v_foundLine_444_;
goto v___jp_450_;
}
else
{
v___y_451_ = v___x_465_;
goto v___jp_450_;
}
v___jp_450_:
{
if (v___y_451_ == 0)
{
lean_object* v___x_452_; lean_object* v_r_u2082_453_; uint8_t v_foundLine_454_; uint8_t v_foundFlattenedHardLine_455_; lean_object* v_space_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_464_; 
lean_dec_ref(v___x_443_);
v___x_452_ = lean_nat_sub(v_x_419_, v_space_445_);
lean_dec(v_x_419_);
v_r_u2082_453_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_449_, v_x_418_, v___x_452_);
v_foundLine_454_ = lean_ctor_get_uint8(v_r_u2082_453_, sizeof(void*)*1);
v_foundFlattenedHardLine_455_ = lean_ctor_get_uint8(v_r_u2082_453_, sizeof(void*)*1 + 1);
v_space_456_ = lean_ctor_get(v_r_u2082_453_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v_r_u2082_453_);
if (v_isSharedCheck_464_ == 0)
{
v___x_458_ = v_r_u2082_453_;
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_space_456_);
lean_dec(v_r_u2082_453_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = lean_nat_add(v_space_445_, v_space_456_);
lean_dec(v_space_456_);
lean_dec(v_space_445_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_460_);
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
lean_ctor_set_uint8(v_reuseFailAlloc_463_, sizeof(void*)*1, v_foundLine_454_);
lean_ctor_set_uint8(v_reuseFailAlloc_463_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_455_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_dec_ref(v___x_449_);
lean_dec(v_space_445_);
lean_dec(v_x_419_);
lean_dec(v_x_418_);
return v___x_443_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(uint8_t v_flb_472_, lean_object* v_items_473_, lean_object* v_w_474_, lean_object* v_gs_475_, lean_object* v_toPure_476_, lean_object* v_k_477_){
_start:
{
uint8_t v___y_479_; uint8_t v___x_484_; uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v_g_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_r_491_; lean_object* v___y_493_; uint8_t v_foundLine_498_; lean_object* v_space_499_; uint8_t v___y_501_; uint8_t v___x_515_; 
v___x_484_ = 0;
v___x_485_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_472_, v___x_484_);
v___x_486_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_486_, 0, v___x_485_);
lean_inc(v_items_473_);
v_g_487_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_487_, 0, v___x_486_);
lean_ctor_set(v_g_487_, 1, v_items_473_);
lean_ctor_set_uint8(v_g_487_, sizeof(void*)*2, v_flb_472_);
v___x_488_ = lean_box(0);
v___x_489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_489_, 0, v_g_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = lean_nat_sub(v_w_474_, v_k_477_);
lean_inc(v___x_490_);
lean_inc(v_k_477_);
v_r_491_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_489_, v_k_477_, v___x_490_);
v_foundLine_498_ = lean_ctor_get_uint8(v_r_491_, sizeof(void*)*1);
v_space_499_ = lean_ctor_get(v_r_491_, 0);
lean_inc(v_space_499_);
v___x_515_ = lean_nat_dec_lt(v___x_490_, v_space_499_);
if (v___x_515_ == 0)
{
v___y_501_ = v_foundLine_498_;
goto v___jp_500_;
}
else
{
v___y_501_ = v___x_515_;
goto v___jp_500_;
}
v___jp_478_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_480_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_480_, 0, v___y_479_);
v___x_481_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v_items_473_);
lean_ctor_set_uint8(v___x_481_, sizeof(void*)*2, v_flb_472_);
v___x_482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v_gs_475_);
v___x_483_ = lean_apply_2(v_toPure_476_, lean_box(0), v___x_482_);
return v___x_483_;
}
v___jp_492_:
{
uint8_t v_foundFlattenedHardLine_494_; 
v_foundFlattenedHardLine_494_ = lean_ctor_get_uint8(v_r_491_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_491_);
if (v_foundFlattenedHardLine_494_ == 0)
{
lean_object* v_space_495_; uint8_t v___x_496_; 
v_space_495_ = lean_ctor_get(v___y_493_, 0);
lean_inc(v_space_495_);
lean_dec_ref(v___y_493_);
v___x_496_ = lean_nat_dec_le(v_space_495_, v___x_490_);
lean_dec(v___x_490_);
lean_dec(v_space_495_);
v___y_479_ = v___x_496_;
goto v___jp_478_;
}
else
{
uint8_t v___x_497_; 
lean_dec_ref(v___y_493_);
lean_dec(v___x_490_);
v___x_497_ = 0;
v___y_479_ = v___x_497_;
goto v___jp_478_;
}
}
v___jp_500_:
{
if (v___y_501_ == 0)
{
lean_object* v___x_502_; lean_object* v_r_u2082_503_; uint8_t v_foundLine_504_; uint8_t v_foundFlattenedHardLine_505_; lean_object* v_space_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_514_; 
v___x_502_ = lean_nat_sub(v___x_490_, v_space_499_);
lean_inc(v_gs_475_);
v_r_u2082_503_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_475_, v_k_477_, v___x_502_);
v_foundLine_504_ = lean_ctor_get_uint8(v_r_u2082_503_, sizeof(void*)*1);
v_foundFlattenedHardLine_505_ = lean_ctor_get_uint8(v_r_u2082_503_, sizeof(void*)*1 + 1);
v_space_506_ = lean_ctor_get(v_r_u2082_503_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v_r_u2082_503_);
if (v_isSharedCheck_514_ == 0)
{
v___x_508_ = v_r_u2082_503_;
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_space_506_);
lean_dec(v_r_u2082_503_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_514_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_510_ = lean_nat_add(v_space_499_, v_space_506_);
lean_dec(v_space_506_);
lean_dec(v_space_499_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_510_);
v___x_512_ = v___x_508_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
lean_ctor_set_uint8(v_reuseFailAlloc_513_, sizeof(void*)*1, v_foundLine_504_);
lean_ctor_set_uint8(v_reuseFailAlloc_513_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_505_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
v___y_493_ = v___x_512_;
goto v___jp_492_;
}
}
}
else
{
lean_dec(v_space_499_);
lean_dec(v_k_477_);
lean_inc_ref(v_r_491_);
v___y_493_ = v_r_491_;
goto v___jp_492_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed(lean_object* v_flb_516_, lean_object* v_items_517_, lean_object* v_w_518_, lean_object* v_gs_519_, lean_object* v_toPure_520_, lean_object* v_k_521_){
_start:
{
uint8_t v_flb_boxed_522_; lean_object* v_res_523_; 
v_flb_boxed_522_ = lean_unbox(v_flb_516_);
v_res_523_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(v_flb_boxed_522_, v_items_517_, v_w_518_, v_gs_519_, v_toPure_520_, v_k_521_);
lean_dec(v_w_518_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(uint8_t v_flb_524_, lean_object* v_items_525_, lean_object* v_gs_526_, lean_object* v_w_527_, lean_object* v_inst_528_, lean_object* v_inst_529_){
_start:
{
lean_object* v_toApplicative_530_; lean_object* v_toBind_531_; lean_object* v_currColumn_532_; lean_object* v_toPure_533_; lean_object* v___x_534_; lean_object* v___f_535_; lean_object* v___x_536_; 
v_toApplicative_530_ = lean_ctor_get(v_inst_528_, 0);
lean_inc_ref(v_toApplicative_530_);
v_toBind_531_ = lean_ctor_get(v_inst_528_, 1);
lean_inc(v_toBind_531_);
lean_dec_ref(v_inst_528_);
v_currColumn_532_ = lean_ctor_get(v_inst_529_, 2);
lean_inc(v_currColumn_532_);
lean_dec_ref(v_inst_529_);
v_toPure_533_ = lean_ctor_get(v_toApplicative_530_, 1);
lean_inc(v_toPure_533_);
lean_dec_ref(v_toApplicative_530_);
v___x_534_ = lean_box(v_flb_524_);
v___f_535_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_535_, 0, v___x_534_);
lean_closure_set(v___f_535_, 1, v_items_525_);
lean_closure_set(v___f_535_, 2, v_w_527_);
lean_closure_set(v___f_535_, 3, v_gs_526_);
lean_closure_set(v___f_535_, 4, v_toPure_533_);
v___x_536_ = lean_apply_4(v_toBind_531_, lean_box(0), lean_box(0), v_currColumn_532_, v___f_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___boxed(lean_object* v_flb_537_, lean_object* v_items_538_, lean_object* v_gs_539_, lean_object* v_w_540_, lean_object* v_inst_541_, lean_object* v_inst_542_){
_start:
{
uint8_t v_flb_boxed_543_; lean_object* v_res_544_; 
v_flb_boxed_543_ = lean_unbox(v_flb_537_);
v_res_544_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_boxed_543_, v_items_538_, v_gs_539_, v_w_540_, v_inst_541_, v_inst_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(lean_object* v_m_545_, uint8_t v_flb_546_, lean_object* v_items_547_, lean_object* v_gs_548_, lean_object* v_w_549_, lean_object* v_inst_550_, lean_object* v_inst_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_546_, v_items_547_, v_gs_548_, v_w_549_, v_inst_550_, v_inst_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___boxed(lean_object* v_m_553_, lean_object* v_flb_554_, lean_object* v_items_555_, lean_object* v_gs_556_, lean_object* v_w_557_, lean_object* v_inst_558_, lean_object* v_inst_559_){
_start:
{
uint8_t v_flb_boxed_560_; lean_object* v_res_561_; 
v_flb_boxed_560_ = lean_unbox(v_flb_554_);
v_res_561_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(v_m_553_, v_flb_boxed_560_, v_items_555_, v_gs_556_, v_w_557_, v_inst_558_, v_inst_559_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(lean_object* v_fla_562_, uint8_t v_flb_563_, lean_object* v_tail_564_, lean_object* v_is_x27_565_){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_566_, 0, v_fla_562_);
lean_ctor_set(v___x_566_, 1, v_is_x27_565_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*2, v_flb_563_);
v___x_567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v_tail_564_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed(lean_object* v_fla_568_, lean_object* v_flb_569_, lean_object* v_tail_570_, lean_object* v_is_x27_571_){
_start:
{
uint8_t v_flb_1651__boxed_572_; lean_object* v_res_573_; 
v_flb_1651__boxed_572_ = lean_unbox(v_flb_569_);
v_res_573_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_568_, v_flb_1651__boxed_572_, v_tail_570_, v_is_x27_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3(lean_object* v_endTags_574_, lean_object* v_activeTags_575_, lean_object* v_toBind_576_, lean_object* v___f_577_, lean_object* v_____r_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_apply_1(v_endTags_574_, v_activeTags_575_);
v___x_580_ = lean_apply_4(v_toBind_576_, lean_box(0), lean_box(0), v___x_579_, v___f_577_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(lean_object* v_inst_581_, lean_object* v_activeTags_582_, lean_object* v_toBind_583_, lean_object* v___f_584_, lean_object* v_00___585_){
_start:
{
lean_object* v_endTags_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_endTags_586_ = lean_ctor_get(v_inst_581_, 4);
lean_inc(v_endTags_586_);
lean_dec_ref(v_inst_581_);
v___x_587_ = lean_apply_1(v_endTags_586_, v_activeTags_582_);
v___x_588_ = lean_apply_4(v_toBind_583_, lean_box(0), lean_box(0), v___x_587_, v___f_584_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(lean_object* v_indent_589_, lean_object* v_inst_590_, lean_object* v_toBind_591_, lean_object* v___f_592_, lean_object* v_k_593_){
_start:
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_nat_to_int(v_k_593_);
v___x_595_ = lean_int_dec_lt(v___x_594_, v_indent_589_);
if (v___x_595_ == 0)
{
lean_object* v_pushNewline_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v___x_594_);
v_pushNewline_596_ = lean_ctor_get(v_inst_590_, 1);
lean_inc(v_pushNewline_596_);
lean_dec_ref(v_inst_590_);
v___x_597_ = l_Int_toNat(v_indent_589_);
v___x_598_ = lean_apply_1(v_pushNewline_596_, v___x_597_);
v___x_599_ = lean_apply_4(v_toBind_591_, lean_box(0), lean_box(0), v___x_598_, v___f_592_);
return v___x_599_;
}
else
{
lean_object* v_pushOutput_600_; lean_object* v___x_601_; uint32_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_pushOutput_600_ = lean_ctor_get(v_inst_590_, 0);
lean_inc(v_pushOutput_600_);
lean_dec_ref(v_inst_590_);
v___x_601_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_602_ = 32;
v___x_603_ = lean_int_sub(v_indent_589_, v___x_594_);
lean_dec(v___x_594_);
v___x_604_ = l_Int_toNat(v___x_603_);
lean_dec(v___x_603_);
v___x_605_ = lean_string_pushn(v___x_601_, v___x_602_, v___x_604_);
v___x_606_ = lean_apply_1(v_pushOutput_600_, v___x_605_);
v___x_607_ = lean_apply_4(v_toBind_591_, lean_box(0), lean_box(0), v___x_606_, v___f_592_);
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed(lean_object* v_indent_608_, lean_object* v_inst_609_, lean_object* v_toBind_610_, lean_object* v___f_611_, lean_object* v_k_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(v_indent_608_, v_inst_609_, v_toBind_610_, v___f_611_, v_k_612_);
lean_dec(v_indent_608_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9(lean_object* v_indent_614_, lean_object* v_pushNewline_615_, lean_object* v_toBind_616_, lean_object* v___f_617_, lean_object* v_____r_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = l_Int_toNat(v_indent_614_);
v___x_620_ = lean_apply_1(v_pushNewline_615_, v___x_619_);
v___x_621_ = lean_apply_4(v_toBind_616_, lean_box(0), lean_box(0), v___x_620_, v___f_617_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9___boxed(lean_object* v_indent_622_, lean_object* v_pushNewline_623_, lean_object* v_toBind_624_, lean_object* v___f_625_, lean_object* v_____r_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9(v_indent_622_, v_pushNewline_623_, v_toBind_624_, v___f_625_, v_____r_626_);
lean_dec(v_indent_622_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1(lean_object* v_gs_x27_628_, lean_object* v_tail_629_, lean_object* v_w_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_____r_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_apply_1(v_gs_x27_628_, v_tail_629_);
v___x_635_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_630_, v_inst_631_, v_inst_632_, v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4(uint8_t v_flb_637_, lean_object* v_tail_638_, lean_object* v_tail_639_, lean_object* v_w_640_, lean_object* v_inst_641_, lean_object* v_inst_642_, lean_object* v_toBind_643_, lean_object* v_____r_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
lean_inc_ref(v_inst_642_);
lean_inc_ref(v_inst_641_);
lean_inc(v_w_640_);
v___x_645_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_637_, v_tail_638_, v_tail_639_, v_w_640_, v_inst_641_, v_inst_642_);
v___x_646_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_646_, 0, v_w_640_);
lean_closure_set(v___x_646_, 1, v_inst_641_);
lean_closure_set(v___x_646_, 2, v_inst_642_);
v___x_647_ = lean_apply_4(v_toBind_643_, lean_box(0), lean_box(0), v___x_645_, v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4___boxed(lean_object* v_flb_648_, lean_object* v_tail_649_, lean_object* v_tail_650_, lean_object* v_w_651_, lean_object* v_inst_652_, lean_object* v_inst_653_, lean_object* v_toBind_654_, lean_object* v_____r_655_){
_start:
{
uint8_t v_flb_1738__boxed_656_; lean_object* v_res_657_; 
v_flb_1738__boxed_656_ = lean_unbox(v_flb_648_);
v_res_657_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4(v_flb_1738__boxed_656_, v_tail_649_, v_tail_650_, v_w_651_, v_inst_652_, v_inst_653_, v_toBind_654_, v_____r_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(lean_object* v_breakHere_659_, lean_object* v_w_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_endTags_663_, lean_object* v_activeTags_664_, lean_object* v_toBind_665_, lean_object* v_pushOutput_666_, lean_object* v___x_667_, lean_object* v_____x_668_){
_start:
{
if (lean_obj_tag(v_____x_668_) == 1)
{
lean_object* v_head_669_; lean_object* v_fla_670_; uint8_t v___x_671_; 
v_head_669_ = lean_ctor_get(v_____x_668_, 0);
v_fla_670_ = lean_ctor_get(v_head_669_, 0);
v___x_671_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_670_);
if (v___x_671_ == 0)
{
lean_dec_ref(v_____x_668_);
lean_dec_ref(v___x_667_);
lean_dec(v_pushOutput_666_);
lean_dec(v_toBind_665_);
lean_dec(v_activeTags_664_);
lean_dec(v_endTags_663_);
lean_dec_ref(v_inst_662_);
lean_dec_ref(v_inst_661_);
lean_dec(v_w_660_);
lean_inc(v_breakHere_659_);
return v_breakHere_659_;
}
else
{
lean_object* v___f_672_; lean_object* v___f_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___f_672_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5), 5, 4);
lean_closure_set(v___f_672_, 0, v_w_660_);
lean_closure_set(v___f_672_, 1, v_inst_661_);
lean_closure_set(v___f_672_, 2, v_inst_662_);
lean_closure_set(v___f_672_, 3, v_____x_668_);
lean_inc(v_toBind_665_);
v___f_673_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_673_, 0, v_endTags_663_);
lean_closure_set(v___f_673_, 1, v_activeTags_664_);
lean_closure_set(v___f_673_, 2, v_toBind_665_);
lean_closure_set(v___f_673_, 3, v___f_672_);
v___x_674_ = lean_apply_1(v_pushOutput_666_, v___x_667_);
v___x_675_ = lean_apply_4(v_toBind_665_, lean_box(0), lean_box(0), v___x_674_, v___f_673_);
return v___x_675_;
}
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec(v_____x_668_);
lean_dec_ref(v___x_667_);
lean_dec(v_pushOutput_666_);
lean_dec(v_toBind_665_);
lean_dec(v_activeTags_664_);
lean_dec(v_endTags_663_);
lean_dec_ref(v_inst_662_);
lean_dec(v_w_660_);
v___x_676_ = lean_box(0);
v___x_677_ = l_instInhabitedOfMonad___redArg(v_inst_661_, v___x_676_);
v___x_678_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___closed__0));
v___x_679_ = l_panic___redArg(v___x_677_, v___x_678_);
return v___x_679_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed(lean_object* v_breakHere_680_, lean_object* v_w_681_, lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_endTags_684_, lean_object* v_activeTags_685_, lean_object* v_toBind_686_, lean_object* v_pushOutput_687_, lean_object* v___x_688_, lean_object* v_____x_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(v_breakHere_680_, v_w_681_, v_inst_682_, v_inst_683_, v_endTags_684_, v_activeTags_685_, v_toBind_686_, v_pushOutput_687_, v___x_688_, v_____x_689_);
lean_dec(v_breakHere_680_);
return v_res_690_;
}
}
static lean_object* _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_692_ = lean_string_length(v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(lean_object* v_a_693_, lean_object* v_p_694_, lean_object* v___x_695_, lean_object* v_indent_696_, lean_object* v_activeTags_697_, lean_object* v_tail_698_, lean_object* v_fla_699_, uint8_t v_flb_700_, lean_object* v_tail_701_, lean_object* v_w_702_, lean_object* v_inst_703_, lean_object* v_inst_704_, lean_object* v_toBind_705_, lean_object* v_gs_x27_706_, lean_object* v_____r_707_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_is_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_708_ = lean_string_utf8_next(v_a_693_, v_p_694_);
v___x_709_ = lean_string_utf8_extract(v_a_693_, v___x_708_, v___x_695_);
lean_dec(v___x_708_);
v___x_710_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
v___x_711_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v_indent_696_);
lean_ctor_set(v___x_711_, 2, v_activeTags_697_);
v_is_712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_is_712_, 0, v___x_711_);
lean_ctor_set(v_is_712_, 1, v_tail_698_);
v___x_713_ = lean_box(1);
v___x_714_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_699_, v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec_ref(v_gs_x27_706_);
lean_inc_ref(v_inst_704_);
lean_inc_ref(v_inst_703_);
lean_inc(v_w_702_);
v___x_715_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_700_, v_is_712_, v_tail_701_, v_w_702_, v_inst_703_, v_inst_704_);
v___x_716_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_716_, 0, v_w_702_);
lean_closure_set(v___x_716_, 1, v_inst_703_);
lean_closure_set(v___x_716_, 2, v_inst_704_);
v___x_717_ = lean_apply_4(v_toBind_705_, lean_box(0), lean_box(0), v___x_715_, v___x_716_);
return v___x_717_;
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec(v_toBind_705_);
lean_dec(v_tail_701_);
v___x_718_ = lean_apply_1(v_gs_x27_706_, v_is_712_);
v___x_719_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_702_, v_inst_703_, v_inst_704_, v___x_718_);
return v___x_719_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed(lean_object* v_a_720_, lean_object* v_p_721_, lean_object* v___x_722_, lean_object* v_indent_723_, lean_object* v_activeTags_724_, lean_object* v_tail_725_, lean_object* v_fla_726_, lean_object* v_flb_727_, lean_object* v_tail_728_, lean_object* v_w_729_, lean_object* v_inst_730_, lean_object* v_inst_731_, lean_object* v_toBind_732_, lean_object* v_gs_x27_733_, lean_object* v_____r_734_){
_start:
{
uint8_t v_flb_1762__boxed_735_; lean_object* v_res_736_; 
v_flb_1762__boxed_735_ = lean_unbox(v_flb_727_);
v_res_736_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(v_a_720_, v_p_721_, v___x_722_, v_indent_723_, v_activeTags_724_, v_tail_725_, v_fla_726_, v_flb_1762__boxed_735_, v_tail_728_, v_w_729_, v_inst_730_, v_inst_731_, v_toBind_732_, v_gs_x27_733_, v_____r_734_);
lean_dec(v_fla_726_);
lean_dec(v___x_722_);
lean_dec(v_p_721_);
lean_dec_ref(v_a_720_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__10(lean_object* v_activeTags_737_, lean_object* v_a_738_, lean_object* v_indent_739_, lean_object* v_tail_740_, lean_object* v_gs_x27_741_, lean_object* v_w_742_, lean_object* v_inst_743_, lean_object* v_inst_744_, lean_object* v_____r_745_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = lean_nat_add(v_activeTags_737_, v___x_746_);
v___x_748_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_748_, 0, v_a_738_);
lean_ctor_set(v___x_748_, 1, v_indent_739_);
lean_ctor_set(v___x_748_, 2, v___x_747_);
v___x_749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v_tail_740_);
v___x_750_ = lean_apply_1(v_gs_x27_741_, v___x_749_);
v___x_751_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_742_, v_inst_743_, v_inst_744_, v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__10___boxed(lean_object* v_activeTags_752_, lean_object* v_a_753_, lean_object* v_indent_754_, lean_object* v_tail_755_, lean_object* v_gs_x27_756_, lean_object* v_w_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_____r_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__10(v_activeTags_752_, v_a_753_, v_indent_754_, v_tail_755_, v_gs_x27_756_, v_w_757_, v_inst_758_, v_inst_759_, v_____r_760_);
lean_dec(v_activeTags_752_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(lean_object* v_w_762_, lean_object* v_inst_763_, lean_object* v_inst_764_, lean_object* v_x_765_){
_start:
{
if (lean_obj_tag(v_x_765_) == 0)
{
lean_object* v_toApplicative_766_; lean_object* v_toPure_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_toApplicative_766_ = lean_ctor_get(v_inst_763_, 0);
lean_inc_ref(v_toApplicative_766_);
lean_dec_ref(v_inst_764_);
lean_dec_ref(v_inst_763_);
lean_dec(v_w_762_);
v_toPure_767_ = lean_ctor_get(v_toApplicative_766_, 1);
lean_inc(v_toPure_767_);
lean_dec_ref(v_toApplicative_766_);
v___x_768_ = lean_box(0);
v___x_769_ = lean_apply_2(v_toPure_767_, lean_box(0), v___x_768_);
return v___x_769_;
}
else
{
lean_object* v_head_770_; lean_object* v_items_771_; 
v_head_770_ = lean_ctor_get(v_x_765_, 0);
v_items_771_ = lean_ctor_get(v_head_770_, 1);
lean_inc(v_items_771_);
if (lean_obj_tag(v_items_771_) == 0)
{
lean_object* v_tail_772_; 
v_tail_772_ = lean_ctor_get(v_x_765_, 1);
lean_inc(v_tail_772_);
lean_dec_ref(v_x_765_);
v_x_765_ = v_tail_772_;
goto _start;
}
else
{
lean_object* v_head_774_; lean_object* v_toBind_775_; lean_object* v_tail_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_909_; 
lean_inc(v_head_770_);
v_head_774_ = lean_ctor_get(v_items_771_, 0);
lean_inc(v_head_774_);
v_toBind_775_ = lean_ctor_get(v_inst_763_, 1);
v_tail_776_ = lean_ctor_get(v_x_765_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v_x_765_);
if (v_isSharedCheck_909_ == 0)
{
lean_object* v_unused_910_; 
v_unused_910_ = lean_ctor_get(v_x_765_, 0);
lean_dec(v_unused_910_);
v___x_778_ = v_x_765_;
v_isShared_779_ = v_isSharedCheck_909_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_tail_776_);
lean_dec(v_x_765_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_909_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v_fla_780_; uint8_t v_flb_781_; lean_object* v_tail_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_907_; 
v_fla_780_ = lean_ctor_get(v_head_770_, 0);
lean_inc(v_fla_780_);
v_flb_781_ = lean_ctor_get_uint8(v_head_770_, sizeof(void*)*2);
lean_dec(v_head_770_);
v_tail_782_ = lean_ctor_get(v_items_771_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_items_771_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; 
v_unused_908_ = lean_ctor_get(v_items_771_, 0);
lean_dec(v_unused_908_);
v___x_784_ = v_items_771_;
v_isShared_785_ = v_isSharedCheck_907_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_tail_782_);
lean_dec(v_items_771_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_907_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_f_786_; lean_object* v_indent_787_; lean_object* v_activeTags_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_906_; 
v_f_786_ = lean_ctor_get(v_head_774_, 0);
v_indent_787_ = lean_ctor_get(v_head_774_, 1);
v_activeTags_788_ = lean_ctor_get(v_head_774_, 2);
v_isSharedCheck_906_ = !lean_is_exclusive(v_head_774_);
if (v_isSharedCheck_906_ == 0)
{
v___x_790_ = v_head_774_;
v_isShared_791_ = v_isSharedCheck_906_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_activeTags_788_);
lean_inc(v_indent_787_);
lean_inc(v_f_786_);
lean_dec(v_head_774_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_906_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v_gs_x27_793_; lean_object* v___f_794_; lean_object* v___f_795_; 
v___x_792_ = lean_box(v_flb_781_);
lean_inc(v_tail_776_);
lean_inc(v_fla_780_);
v_gs_x27_793_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v_gs_x27_793_, 0, v_fla_780_);
lean_closure_set(v_gs_x27_793_, 1, v___x_792_);
lean_closure_set(v_gs_x27_793_, 2, v_tail_776_);
lean_inc_ref(v_inst_764_);
lean_inc_ref(v_inst_763_);
lean_inc(v_w_762_);
lean_inc(v_tail_782_);
lean_inc_ref(v_gs_x27_793_);
v___f_794_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_794_, 0, v_gs_x27_793_);
lean_closure_set(v___f_794_, 1, v_tail_782_);
lean_closure_set(v___f_794_, 2, v_w_762_);
lean_closure_set(v___f_794_, 3, v_inst_763_);
lean_closure_set(v___f_794_, 4, v_inst_764_);
lean_inc_ref(v___f_794_);
lean_inc(v_toBind_775_);
lean_inc(v_activeTags_788_);
lean_inc_ref(v_inst_764_);
v___f_795_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2), 5, 4);
lean_closure_set(v___f_795_, 0, v_inst_764_);
lean_closure_set(v___f_795_, 1, v_activeTags_788_);
lean_closure_set(v___f_795_, 2, v_toBind_775_);
lean_closure_set(v___f_795_, 3, v___f_794_);
switch(lean_obj_tag(v_f_786_))
{
case 0:
{
lean_object* v_endTags_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_inc(v_toBind_775_);
lean_dec_ref(v___f_795_);
lean_dec_ref(v_gs_x27_793_);
lean_del_object(v___x_790_);
lean_dec(v_indent_787_);
lean_del_object(v___x_784_);
lean_dec(v_tail_782_);
lean_dec(v_fla_780_);
lean_del_object(v___x_778_);
lean_dec(v_tail_776_);
lean_dec_ref(v_inst_763_);
lean_dec(v_w_762_);
v_endTags_796_ = lean_ctor_get(v_inst_764_, 4);
lean_inc(v_endTags_796_);
lean_dec_ref(v_inst_764_);
v___x_797_ = lean_apply_1(v_endTags_796_, v_activeTags_788_);
v___x_798_ = lean_apply_4(v_toBind_775_, lean_box(0), lean_box(0), v___x_797_, v___f_794_);
return v___x_798_;
}
case 1:
{
lean_inc(v_toBind_775_);
lean_dec_ref(v___f_794_);
lean_dec_ref(v_gs_x27_793_);
lean_del_object(v___x_790_);
lean_del_object(v___x_784_);
lean_del_object(v___x_778_);
if (v_flb_781_ == 0)
{
uint8_t v___x_799_; 
lean_dec(v_activeTags_788_);
lean_dec(v_tail_782_);
lean_dec(v_tail_776_);
lean_dec_ref(v_inst_763_);
lean_dec(v_w_762_);
v___x_799_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_780_);
lean_dec(v_fla_780_);
if (v___x_799_ == 0)
{
lean_object* v_pushNewline_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_pushNewline_800_ = lean_ctor_get(v_inst_764_, 1);
lean_inc(v_pushNewline_800_);
lean_dec_ref(v_inst_764_);
v___x_801_ = l_Int_toNat(v_indent_787_);
lean_dec(v_indent_787_);
v___x_802_ = lean_apply_1(v_pushNewline_800_, v___x_801_);
v___x_803_ = lean_apply_4(v_toBind_775_, lean_box(0), lean_box(0), v___x_802_, v___f_795_);
return v___x_803_;
}
else
{
lean_object* v_pushOutput_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec(v_indent_787_);
v_pushOutput_804_ = lean_ctor_get(v_inst_764_, 0);
lean_inc(v_pushOutput_804_);
lean_dec_ref(v_inst_764_);
v___x_805_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_806_ = lean_apply_1(v_pushOutput_804_, v___x_805_);
v___x_807_ = lean_apply_4(v_toBind_775_, lean_box(0), lean_box(0), v___x_806_, v___f_795_);
return v___x_807_;
}
}
else
{
lean_object* v_pushOutput_808_; lean_object* v_pushNewline_809_; lean_object* v_endTags_810_; lean_object* v___x_811_; lean_object* v___f_812_; lean_object* v___f_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v_breakHere_816_; uint8_t v___x_817_; 
lean_dec_ref(v___f_795_);
v_pushOutput_808_ = lean_ctor_get(v_inst_764_, 0);
v_pushNewline_809_ = lean_ctor_get(v_inst_764_, 1);
v_endTags_810_ = lean_ctor_get(v_inst_764_, 4);
v___x_811_ = lean_box(v_flb_781_);
lean_inc(v_toBind_775_);
lean_inc_ref(v_inst_764_);
lean_inc_ref(v_inst_763_);
lean_inc(v_w_762_);
lean_inc(v_tail_776_);
lean_inc(v_tail_782_);
v___f_812_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_812_, 0, v___x_811_);
lean_closure_set(v___f_812_, 1, v_tail_782_);
lean_closure_set(v___f_812_, 2, v_tail_776_);
lean_closure_set(v___f_812_, 3, v_w_762_);
lean_closure_set(v___f_812_, 4, v_inst_763_);
lean_closure_set(v___f_812_, 5, v_inst_764_);
lean_closure_set(v___f_812_, 6, v_toBind_775_);
lean_inc(v_toBind_775_);
lean_inc(v_activeTags_788_);
lean_inc(v_endTags_810_);
v___f_813_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_813_, 0, v_endTags_810_);
lean_closure_set(v___f_813_, 1, v_activeTags_788_);
lean_closure_set(v___f_813_, 2, v_toBind_775_);
lean_closure_set(v___f_813_, 3, v___f_812_);
v___x_814_ = l_Int_toNat(v_indent_787_);
lean_dec(v_indent_787_);
lean_inc(v_pushNewline_809_);
v___x_815_ = lean_apply_1(v_pushNewline_809_, v___x_814_);
lean_inc(v_toBind_775_);
v_breakHere_816_ = lean_apply_4(v_toBind_775_, lean_box(0), lean_box(0), v___x_815_, v___f_813_);
v___x_817_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_780_);
lean_dec(v_fla_780_);
if (v___x_817_ == 0)
{
lean_dec(v_activeTags_788_);
lean_dec(v_tail_782_);
lean_dec(v_tail_776_);
lean_dec(v_toBind_775_);
lean_dec_ref(v_inst_764_);
lean_dec_ref(v_inst_763_);
lean_dec(v_w_762_);
return v_breakHere_816_;
}
else
{
lean_object* v___x_818_; lean_object* v___f_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_818_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
lean_inc(v_pushOutput_808_);
lean_inc(v_toBind_775_);
lean_inc(v_endTags_810_);
lean_inc_ref(v_inst_764_);
lean_inc_ref(v_inst_763_);
lean_inc(v_w_762_);
v___f_819_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed), 10, 9);
lean_closure_set(v___f_819_, 0, v_breakHere_816_);
lean_closure_set(v___f_819_, 1, v_w_762_);
lean_closure_set(v___f_819_, 2, v_inst_763_);
lean_closure_set(v___f_819_, 3, v_inst_764_);
lean_closure_set(v___f_819_, 4, v_endTags_810_);
lean_closure_set(v___f_819_, 5, v_activeTags_788_);
lean_closure_set(v___f_819_, 6, v_toBind_775_);
lean_closure_set(v___f_819_, 7, v_pushOutput_808_);
lean_closure_set(v___f_819_, 8, v___x_818_);
v___x_820_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_821_ = lean_nat_sub(v_w_762_, v___x_820_);
lean_dec(v_w_762_);
v___x_822_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_781_, v_tail_782_, v_tail_776_, v___x_821_, v_inst_763_, v_inst_764_);
v___x_823_ = lean_apply_4(v_toBind_775_, lean_box(0), lean_box(0), v___x_822_, v___f_819_);
return v___x_823_;
}
}
}
case 2:
{
uint8_t v_force_824_; lean_object* v___f_825_; uint8_t v___y_830_; uint8_t v___x_834_; 
lean_inc(v_toBind_775_);
lean_dec_ref(v_gs_x27_793_);
lean_del_object(v___x_790_);
lean_del_object(v___x_784_);
lean_dec(v_tail_782_);
lean_del_object(v___x_778_);
lean_dec(v_tail_776_);
lean_dec_ref(v_inst_763_);
lean_dec(v_w_762_);
v_force_824_ = lean_ctor_get_uint8(v_f_786_, 0);
lean_dec_ref(v_f_786_);
lean_inc(v_toBind_775_);
lean_inc_ref(v_inst_764_);
v___f_825_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_825_, 0, v_indent_787_);
lean_closure_set(v___f_825_, 1, v_inst_764_);
lean_closure_set(v___f_825_, 2, v_toBind_775_);
lean_closure_set(v___f_825_, 3, v___f_795_);
v___x_834_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_780_);
lean_dec(v_fla_780_);
if (v___x_834_ == 0)
{
v___y_830_ = v___x_834_;
goto v___jp_829_;
}
else
{
if (v_force_824_ == 0)
{
v___y_830_ = v___x_834_;
goto v___jp_829_;
}
else
{
lean_dec_ref(v___f_794_);
lean_dec(v_activeTags_788_);
goto v___jp_826_;
}
}
v___jp_826_:
{
lean_object* v_currColumn_827_; lean_object* v___x_828_; 
v_currColumn_827_ = lean_ctor_get(v_inst_764_, 2);
lean_inc(v_currColumn_827_);
lean_dec_ref(v_inst_764_);
v___x_828_ = lean_apply_4(v_toBind_775_, lean_box(0), lean_box(0), v_currColumn_827_, v___f_825_);
return v___x_828_;
}
v___jp_829_:
{
if (v___y_830_ == 0)
{
lean_dec_ref(v___f_794_);
lean_dec(v_activeTags_788_);
goto v___jp_826_;
}
else
{
lean_object* v_endTags_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec_ref(v___f_825_);
v_endTags_831_ = lean_ctor_get(v_inst_764_, 4);
lean_inc(v_endTags_831_);
lean_dec_ref(v_inst_764_);
v___x_832_ = lean_apply_1(v_endTags_831_, v_activeTags_788_);
v___x_833_ = lean_apply_4(v_toBind_775_, lean_box(0), lean_box(0), v___x_832_, v___f_794_);
return v___x_833_;
}
}
}
case 3:
{
lean_object* v_a_835_; uint32_t v___x_836_; lean_object* v_p_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
lean_inc(v_toBind_775_);
lean_dec_ref(v___f_794_);
lean_del_object(v___x_790_);
lean_del_object(v___x_784_);
lean_del_object(v___x_778_);
v_a_835_ = lean_ctor_get(v_f_786_, 0);
lean_inc_ref(v_a_835_);
lean_dec_ref(v_f_786_);
v___x_836_ = 10;
lean_inc_ref(v_a_835_);
v_p_837_ = lean_string_posof(v_a_835_, v___x_836_);
v___x_838_ = lean_string_utf8_byte_size(v_a_835_);
v___x_839_ = lean_nat_dec_eq(v_p_837_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v_pushOutput_840_; lean_object* v_pushNewline_841_; lean_object* v___x_842_; lean_object* v___f_843_; lean_object* v___f_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec_ref(v___f_795_);
v_pushOutput_840_ = lean_ctor_get(v_inst_764_, 0);
lean_inc(v_pushOutput_840_);
v_pushNewline_841_ = lean_ctor_get(v_inst_764_, 1);
lean_inc(v_pushNewline_841_);
v___x_842_ = lean_box(v_flb_781_);
lean_inc(v_toBind_775_);
lean_inc(v_indent_787_);
lean_inc(v_p_837_);
lean_inc_ref(v_a_835_);
v___f_843_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed), 15, 14);
lean_closure_set(v___f_843_, 0, v_a_835_);
lean_closure_set(v___f_843_, 1, v_p_837_);
lean_closure_set(v___f_843_, 2, v___x_838_);
lean_closure_set(v___f_843_, 3, v_indent_787_);
lean_closure_set(v___f_843_, 4, v_activeTags_788_);
lean_closure_set(v___f_843_, 5, v_tail_782_);
lean_closure_set(v___f_843_, 6, v_fla_780_);
lean_closure_set(v___f_843_, 7, v___x_842_);
lean_closure_set(v___f_843_, 8, v_tail_776_);
lean_closure_set(v___f_843_, 9, v_w_762_);
lean_closure_set(v___f_843_, 10, v_inst_763_);
lean_closure_set(v___f_843_, 11, v_inst_764_);
lean_closure_set(v___f_843_, 12, v_toBind_775_);
lean_closure_set(v___f_843_, 13, v_gs_x27_793_);
lean_inc(v_toBind_775_);
v___f_844_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9___boxed), 5, 4);
lean_closure_set(v___f_844_, 0, v_indent_787_);
lean_closure_set(v___f_844_, 1, v_pushNewline_841_);
lean_closure_set(v___f_844_, 2, v_toBind_775_);
lean_closure_set(v___f_844_, 3, v___f_843_);
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_string_utf8_extract(v_a_835_, v___x_845_, v_p_837_);
lean_dec(v_p_837_);
lean_dec_ref(v_a_835_);
v___x_847_ = lean_apply_1(v_pushOutput_840_, v___x_846_);
v___x_848_ = lean_apply_4(v_toBind_775_, lean_box(0), lean_box(0), v___x_847_, v___f_844_);
return v___x_848_;
}
else
{
lean_object* v_pushOutput_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec(v_p_837_);
lean_dec_ref(v_gs_x27_793_);
lean_dec(v_activeTags_788_);
lean_dec(v_indent_787_);
lean_dec(v_tail_782_);
lean_dec(v_fla_780_);
lean_dec(v_tail_776_);
lean_dec_ref(v_inst_763_);
lean_dec(v_w_762_);
v_pushOutput_849_ = lean_ctor_get(v_inst_764_, 0);
lean_inc(v_pushOutput_849_);
lean_dec_ref(v_inst_764_);
v___x_850_ = lean_apply_1(v_pushOutput_849_, v_a_835_);
v___x_851_ = lean_apply_4(v_toBind_775_, lean_box(0), lean_box(0), v___x_850_, v___f_795_);
return v___x_851_;
}
}
case 4:
{
lean_object* v_indent_852_; lean_object* v_f_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
lean_dec_ref(v___f_795_);
lean_dec_ref(v___f_794_);
lean_dec_ref(v_gs_x27_793_);
lean_del_object(v___x_778_);
v_indent_852_ = lean_ctor_get(v_f_786_, 0);
lean_inc(v_indent_852_);
v_f_853_ = lean_ctor_get(v_f_786_, 1);
lean_inc(v_f_853_);
lean_dec_ref(v_f_786_);
v___x_854_ = lean_int_add(v_indent_787_, v_indent_852_);
lean_dec(v_indent_852_);
lean_dec(v_indent_787_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 1, v___x_854_);
lean_ctor_set(v___x_790_, 0, v_f_853_);
v___x_856_ = v___x_790_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_f_853_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_862_, 2, v_activeTags_788_);
v___x_856_ = v_reuseFailAlloc_862_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_858_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_856_);
v___x_858_ = v___x_784_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_tail_782_);
v___x_858_ = v_reuseFailAlloc_861_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; 
v___x_859_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_780_, v_flb_781_, v_tail_776_, v___x_858_);
v_x_765_ = v___x_859_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_863_; lean_object* v_a_864_; lean_object* v___x_865_; lean_object* v___x_867_; 
lean_dec_ref(v___f_795_);
lean_dec_ref(v___f_794_);
lean_dec_ref(v_gs_x27_793_);
v_a_863_ = lean_ctor_get(v_f_786_, 0);
lean_inc(v_a_863_);
v_a_864_ = lean_ctor_get(v_f_786_, 1);
lean_inc(v_a_864_);
lean_dec_ref(v_f_786_);
v___x_865_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_787_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 2, v___x_865_);
lean_ctor_set(v___x_790_, 0, v_a_863_);
v___x_867_ = v___x_790_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_863_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_indent_787_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v___x_865_);
v___x_867_ = v_reuseFailAlloc_877_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_868_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_868_, 0, v_a_864_);
lean_ctor_set(v___x_868_, 1, v_indent_787_);
lean_ctor_set(v___x_868_, 2, v_activeTags_788_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_868_);
v___x_870_ = v___x_784_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_tail_782_);
v___x_870_ = v_reuseFailAlloc_876_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_872_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v___x_870_);
lean_ctor_set(v___x_778_, 0, v___x_867_);
v___x_872_ = v___x_778_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_870_);
v___x_872_ = v_reuseFailAlloc_875_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; 
v___x_873_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_780_, v_flb_781_, v_tail_776_, v___x_872_);
v_x_765_ = v___x_873_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_878_; uint8_t v_behavior_879_; uint8_t v___x_880_; 
lean_dec_ref(v___f_795_);
lean_dec_ref(v___f_794_);
lean_dec_ref(v_gs_x27_793_);
lean_del_object(v___x_778_);
v_a_878_ = lean_ctor_get(v_f_786_, 0);
lean_inc(v_a_878_);
v_behavior_879_ = lean_ctor_get_uint8(v_f_786_, sizeof(void*)*1);
lean_dec_ref(v_f_786_);
v___x_880_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_780_);
if (v___x_880_ == 0)
{
lean_object* v___x_882_; 
lean_inc(v_toBind_775_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v_a_878_);
v___x_882_ = v___x_790_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_878_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_indent_787_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v_activeTags_788_);
v___x_882_ = v_reuseFailAlloc_891_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_883_ = lean_box(0);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v___x_883_);
lean_ctor_set(v___x_784_, 0, v___x_882_);
v___x_885_ = v___x_784_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_883_);
v___x_885_ = v_reuseFailAlloc_890_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_886_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_780_, v_flb_781_, v_tail_776_, v_tail_782_);
lean_inc_ref(v_inst_764_);
lean_inc_ref(v_inst_763_);
lean_inc(v_w_762_);
v___x_887_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_behavior_879_, v___x_885_, v___x_886_, v_w_762_, v_inst_763_, v_inst_764_);
v___x_888_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_888_, 0, v_w_762_);
lean_closure_set(v___x_888_, 1, v_inst_763_);
lean_closure_set(v___x_888_, 2, v_inst_764_);
v___x_889_ = lean_apply_4(v_toBind_775_, lean_box(0), lean_box(0), v___x_887_, v___x_888_);
return v___x_889_;
}
}
}
else
{
lean_object* v___x_893_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v_a_878_);
v___x_893_ = v___x_790_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_878_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_indent_787_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_activeTags_788_);
v___x_893_ = v_reuseFailAlloc_899_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_895_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v___x_893_);
v___x_895_ = v___x_784_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_tail_782_);
v___x_895_ = v_reuseFailAlloc_898_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_896_; 
v___x_896_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_780_, v_flb_781_, v_tail_776_, v___x_895_);
v_x_765_ = v___x_896_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_900_; lean_object* v_a_901_; lean_object* v_startTag_902_; lean_object* v___f_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
lean_inc(v_toBind_775_);
lean_dec_ref(v___f_795_);
lean_dec_ref(v___f_794_);
lean_del_object(v___x_790_);
lean_del_object(v___x_784_);
lean_dec(v_fla_780_);
lean_del_object(v___x_778_);
lean_dec(v_tail_776_);
v_a_900_ = lean_ctor_get(v_f_786_, 0);
lean_inc(v_a_900_);
v_a_901_ = lean_ctor_get(v_f_786_, 1);
lean_inc(v_a_901_);
lean_dec_ref(v_f_786_);
v_startTag_902_ = lean_ctor_get(v_inst_764_, 3);
lean_inc(v_startTag_902_);
v___f_903_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__10___boxed), 9, 8);
lean_closure_set(v___f_903_, 0, v_activeTags_788_);
lean_closure_set(v___f_903_, 1, v_a_901_);
lean_closure_set(v___f_903_, 2, v_indent_787_);
lean_closure_set(v___f_903_, 3, v_tail_782_);
lean_closure_set(v___f_903_, 4, v_gs_x27_793_);
lean_closure_set(v___f_903_, 5, v_w_762_);
lean_closure_set(v___f_903_, 6, v_inst_763_);
lean_closure_set(v___f_903_, 7, v_inst_764_);
v___x_904_ = lean_apply_1(v_startTag_902_, v_a_900_);
v___x_905_ = lean_apply_4(v_toBind_775_, lean_box(0), lean_box(0), v___x_904_, v___f_903_);
return v___x_905_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(lean_object* v_w_911_, lean_object* v_inst_912_, lean_object* v_inst_913_, lean_object* v_____x_914_, lean_object* v_____r_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_911_, v_inst_912_, v_inst_913_, v_____x_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be(lean_object* v_m_917_, lean_object* v_w_918_, lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_x_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_918_, v_inst_919_, v_inst_920_, v_x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___redArg(lean_object* v_f_923_, lean_object* v_w_924_, lean_object* v_indent_925_, lean_object* v_inst_926_, lean_object* v_inst_927_){
_start:
{
lean_object* v___x_928_; uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_928_ = lean_box(1);
v___x_929_ = 0;
v___x_930_ = lean_nat_to_int(v_indent_925_);
v___x_931_ = lean_unsigned_to_nat(0u);
v___x_932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_932_, 0, v_f_923_);
lean_ctor_set(v___x_932_, 1, v___x_930_);
lean_ctor_set(v___x_932_, 2, v___x_931_);
v___x_933_ = lean_box(0);
v___x_934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_932_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_935_, 0, v___x_928_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*2, v___x_929_);
v___x_936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_933_);
v___x_937_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_924_, v_inst_926_, v_inst_927_, v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM(lean_object* v_m_938_, lean_object* v_f_939_, lean_object* v_w_940_, lean_object* v_indent_941_, lean_object* v_inst_942_, lean_object* v_inst_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Std_Format_prettyM___redArg(v_f_939_, v_w_940_, v_indent_941_, v_inst_942_, v_inst_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_bracket(lean_object* v_l_945_, lean_object* v_f_946_, lean_object* v_r_947_){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; lean_object* v___x_956_; 
v___x_948_ = lean_string_length(v_l_945_);
v___x_949_ = lean_nat_to_int(v___x_948_);
v___x_950_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_950_, 0, v_l_945_);
v___x_951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v_f_946_);
v___x_952_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_952_, 0, v_r_947_);
v___x_953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_949_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = 0;
v___x_956_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set_uint8(v___x_956_, sizeof(void*)*1, v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l_Std_Format_paren___closed__2(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l_Std_Format_paren___closed__0));
v___x_960_ = lean_string_length(v___x_959_);
return v___x_960_;
}
}
static lean_object* _init_l_Std_Format_paren___closed__3(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_obj_once(&l_Std_Format_paren___closed__2, &l_Std_Format_paren___closed__2_once, _init_l_Std_Format_paren___closed__2);
v___x_962_ = lean_nat_to_int(v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_paren(lean_object* v_f_967_){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; lean_object* v___x_975_; 
v___x_968_ = lean_obj_once(&l_Std_Format_paren___closed__3, &l_Std_Format_paren___closed__3_once, _init_l_Std_Format_paren___closed__3);
v___x_969_ = ((lean_object*)(l_Std_Format_paren___closed__4));
v___x_970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v_f_967_);
v___x_971_ = ((lean_object*)(l_Std_Format_paren___closed__5));
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_968_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = 0;
v___x_975_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*1, v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l_Std_Format_sbracket___closed__2(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l_Std_Format_sbracket___closed__0));
v___x_979_ = lean_string_length(v___x_978_);
return v___x_979_;
}
}
static lean_object* _init_l_Std_Format_sbracket___closed__3(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_obj_once(&l_Std_Format_sbracket___closed__2, &l_Std_Format_sbracket___closed__2_once, _init_l_Std_Format_sbracket___closed__2);
v___x_981_ = lean_nat_to_int(v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_sbracket(lean_object* v_f_986_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; uint8_t v___x_993_; lean_object* v___x_994_; 
v___x_987_ = lean_obj_once(&l_Std_Format_sbracket___closed__3, &l_Std_Format_sbracket___closed__3_once, _init_l_Std_Format_sbracket___closed__3);
v___x_988_ = ((lean_object*)(l_Std_Format_sbracket___closed__4));
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set(v___x_989_, 1, v_f_986_);
v___x_990_ = ((lean_object*)(l_Std_Format_sbracket___closed__5));
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_987_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = 0;
v___x_994_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*1, v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_bracketFill(lean_object* v_l_995_, lean_object* v_f_996_, lean_object* v_r_997_){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_998_ = lean_string_length(v_l_995_);
v___x_999_ = lean_nat_to_int(v___x_998_);
v___x_1000_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1000_, 0, v_l_995_);
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v_f_996_);
v___x_1002_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1002_, 0, v_r_997_);
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_999_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = l_Std_Format_fill(v___x_1004_);
return v___x_1005_;
}
}
static lean_object* _init_l_Std_Format_defIndent(void){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_unsigned_to_nat(2u);
return v___x_1006_;
}
}
static uint8_t _init_l_Std_Format_defUnicode(void){
_start:
{
uint8_t v___x_1007_; 
v___x_1007_ = 1;
return v___x_1007_;
}
}
static lean_object* _init_l_Std_Format_defWidth(void){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_unsigned_to_nat(120u);
return v___x_1008_;
}
}
static lean_object* _init_l_Std_Format_nestD___closed__0(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_unsigned_to_nat(2u);
v___x_1010_ = lean_nat_to_int(v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nestD(lean_object* v_f_1011_){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_obj_once(&l_Std_Format_nestD___closed__0, &l_Std_Format_nestD___closed__0_once, _init_l_Std_Format_nestD___closed__0);
v___x_1013_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v_f_1011_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_indentD(lean_object* v_f_1014_){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = lean_box(1);
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v_f_1014_);
v___x_1017_ = l_Std_Format_nestD(v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(lean_object* v_s_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_out_1020_; lean_object* v_column_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1033_; 
v_out_1020_ = lean_ctor_get(v___y_1019_, 0);
v_column_1021_ = lean_ctor_get(v___y_1019_, 1);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___y_1019_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1023_ = v___y_1019_;
v_isShared_1024_ = v_isSharedCheck_1033_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_column_1021_);
lean_inc(v_out_1020_);
lean_dec(v___y_1019_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1033_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_string_append(v_out_1020_, v_s_1018_);
v___x_1027_ = lean_string_length(v_s_1018_);
v___x_1028_ = lean_nat_add(v_column_1021_, v___x_1027_);
lean_dec(v___x_1027_);
lean_dec(v_column_1021_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___x_1028_);
lean_ctor_set(v___x_1023_, 0, v___x_1026_);
v___x_1030_ = v___x_1023_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1031_; 
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1025_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
return v___x_1031_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0___boxed(lean_object* v_s_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(v_s_1034_, v___y_1035_);
lean_dec_ref(v_s_1034_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1(lean_object* v_indent_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_out_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1053_; 
v_out_1040_ = lean_ctor_get(v___y_1039_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___y_1039_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; 
v_unused_1054_ = lean_ctor_get(v___y_1039_, 1);
lean_dec(v_unused_1054_);
v___x_1042_ = v___y_1039_;
v_isShared_1043_ = v_isSharedCheck_1053_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_out_1040_);
lean_dec(v___y_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1053_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; uint32_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1044_ = lean_box(0);
v___x_1045_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1046_ = 32;
lean_inc(v_indent_1038_);
v___x_1047_ = lean_string_pushn(v___x_1045_, v___x_1046_, v_indent_1038_);
v___x_1048_ = lean_string_append(v_out_1040_, v___x_1047_);
lean_dec_ref(v___x_1047_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 1, v_indent_1038_);
lean_ctor_set(v___x_1042_, 0, v___x_1048_);
v___x_1050_ = v___x_1042_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_indent_1038_);
v___x_1050_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1044_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
return v___x_1051_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__2(lean_object* v_____do__lift_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_column_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
v_column_1057_ = lean_ctor_get(v_____do__lift_1055_, 1);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_____do__lift_1055_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v_____do__lift_1055_, 0);
lean_dec(v_unused_1065_);
v___x_1059_ = v_____do__lift_1055_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_column_1057_);
lean_dec(v_____do__lift_1055_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 1, v___y_1056_);
lean_ctor_set(v___x_1059_, 0, v_column_1057_);
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_column_1057_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___y_1056_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(lean_object* v_x_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_box(0);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___y_1067_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3___boxed(lean_object* v_x_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(v_x_1070_, v___y_1071_);
lean_dec(v_x_1070_);
return v_res_1072_;
}
}
static lean_object* _init_l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16(void){
_start:
{
lean_object* v___f_1102_; lean_object* v___x_1103_; lean_object* v___f_1104_; lean_object* v___f_1105_; lean_object* v___x_1106_; 
v___f_1102_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__3));
v___x_1103_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__15));
v___f_1104_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__1));
v___f_1105_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__0));
v___x_1106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1106_, 0, v___f_1105_);
lean_ctor_set(v___x_1106_, 1, v___f_1104_);
lean_ctor_set(v___x_1106_, 2, v___x_1103_);
lean_ctor_set(v___x_1106_, 3, v___f_1102_);
lean_ctor_set(v___x_1106_, 4, v___f_1102_);
return v___x_1106_;
}
}
static lean_object* _init_l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState(void){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16, &l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(uint8_t v_flb_1108_, lean_object* v_items_1109_, lean_object* v_gs_1110_, lean_object* v_w_1111_, lean_object* v___y_1112_){
_start:
{
uint8_t v___y_1114_; lean_object* v_column_1119_; uint8_t v___x_1120_; uint8_t v___x_1121_; lean_object* v___x_1122_; lean_object* v_g_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_r_1127_; lean_object* v___y_1129_; uint8_t v_foundLine_1134_; lean_object* v_space_1135_; uint8_t v___y_1137_; uint8_t v___x_1151_; 
v_column_1119_ = lean_ctor_get(v___y_1112_, 1);
v___x_1120_ = 0;
v___x_1121_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_1108_, v___x_1120_);
v___x_1122_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1122_, 0, v___x_1121_);
lean_inc(v_items_1109_);
v_g_1123_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_1123_, 0, v___x_1122_);
lean_ctor_set(v_g_1123_, 1, v_items_1109_);
lean_ctor_set_uint8(v_g_1123_, sizeof(void*)*2, v_flb_1108_);
v___x_1124_ = lean_box(0);
v___x_1125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1125_, 0, v_g_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = lean_nat_sub(v_w_1111_, v_column_1119_);
lean_inc(v___x_1126_);
lean_inc(v_column_1119_);
v_r_1127_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_1125_, v_column_1119_, v___x_1126_);
v_foundLine_1134_ = lean_ctor_get_uint8(v_r_1127_, sizeof(void*)*1);
v_space_1135_ = lean_ctor_get(v_r_1127_, 0);
lean_inc(v_space_1135_);
v___x_1151_ = lean_nat_dec_lt(v___x_1126_, v_space_1135_);
if (v___x_1151_ == 0)
{
v___y_1137_ = v_foundLine_1134_;
goto v___jp_1136_;
}
else
{
v___y_1137_ = v___x_1151_;
goto v___jp_1136_;
}
v___jp_1113_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1115_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1115_, 0, v___y_1114_);
v___x_1116_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v_items_1109_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*2, v_flb_1108_);
v___x_1117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v_gs_1110_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v___y_1112_);
return v___x_1118_;
}
v___jp_1128_:
{
uint8_t v_foundFlattenedHardLine_1130_; 
v_foundFlattenedHardLine_1130_ = lean_ctor_get_uint8(v_r_1127_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_1127_);
if (v_foundFlattenedHardLine_1130_ == 0)
{
lean_object* v_space_1131_; uint8_t v___x_1132_; 
v_space_1131_ = lean_ctor_get(v___y_1129_, 0);
lean_inc(v_space_1131_);
lean_dec_ref(v___y_1129_);
v___x_1132_ = lean_nat_dec_le(v_space_1131_, v___x_1126_);
lean_dec(v___x_1126_);
lean_dec(v_space_1131_);
v___y_1114_ = v___x_1132_;
goto v___jp_1113_;
}
else
{
uint8_t v___x_1133_; 
lean_dec_ref(v___y_1129_);
lean_dec(v___x_1126_);
v___x_1133_ = 0;
v___y_1114_ = v___x_1133_;
goto v___jp_1113_;
}
}
v___jp_1136_:
{
if (v___y_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v_r_u2082_1139_; uint8_t v_foundLine_1140_; uint8_t v_foundFlattenedHardLine_1141_; lean_object* v_space_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1150_; 
v___x_1138_ = lean_nat_sub(v___x_1126_, v_space_1135_);
lean_inc(v_column_1119_);
lean_inc(v_gs_1110_);
v_r_u2082_1139_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_1110_, v_column_1119_, v___x_1138_);
v_foundLine_1140_ = lean_ctor_get_uint8(v_r_u2082_1139_, sizeof(void*)*1);
v_foundFlattenedHardLine_1141_ = lean_ctor_get_uint8(v_r_u2082_1139_, sizeof(void*)*1 + 1);
v_space_1142_ = lean_ctor_get(v_r_u2082_1139_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_r_u2082_1139_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1144_ = v_r_u2082_1139_;
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_space_1142_);
lean_dec(v_r_u2082_1139_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1146_ = lean_nat_add(v_space_1135_, v_space_1142_);
lean_dec(v_space_1142_);
lean_dec(v_space_1135_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1146_);
v___x_1148_ = v___x_1144_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, sizeof(void*)*1, v_foundLine_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_1141_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
v___y_1129_ = v___x_1148_;
goto v___jp_1128_;
}
}
}
else
{
lean_dec(v_space_1135_);
lean_inc_ref(v_r_1127_);
v___y_1129_ = v_r_1127_;
goto v___jp_1128_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1___boxed(lean_object* v_flb_1152_, lean_object* v_items_1153_, lean_object* v_gs_1154_, lean_object* v_w_1155_, lean_object* v___y_1156_){
_start:
{
uint8_t v_flb_boxed_1157_; lean_object* v_res_1158_; 
v_flb_boxed_1157_ = lean_unbox(v_flb_1152_);
v_res_1158_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_boxed_1157_, v_items_1153_, v_gs_1154_, v_w_1155_, v___y_1156_);
lean_dec(v_w_1155_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(lean_object* v_msg_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v___f_1175_; lean_object* v___f_1176_; lean_object* v___f_1177_; lean_object* v___f_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_4462__overap_1187_; lean_object* v___x_1188_; 
v___f_1175_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0));
v___f_1176_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1));
v___f_1177_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2));
v___f_1178_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3));
v___x_1179_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4));
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
lean_ctor_set(v___x_1180_, 1, v___f_1175_);
v___x_1181_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5));
v___x_1182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
lean_ctor_set(v___x_1182_, 2, v___f_1176_);
lean_ctor_set(v___x_1182_, 3, v___f_1177_);
lean_ctor_set(v___x_1182_, 4, v___f_1178_);
v___x_1183_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6));
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = lean_box(0);
v___x_1186_ = l_instInhabitedOfMonad___redArg(v___x_1184_, v___x_1185_);
v___x_4462__overap_1187_ = lean_panic_fn(v___x_1186_, v_msg_1173_);
v___x_1188_ = lean_apply_1(v___x_4462__overap_1187_, v___y_1174_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(lean_object* v_w_1189_, lean_object* v_x_1190_, lean_object* v___y_1191_){
_start:
{
if (lean_obj_tag(v_x_1190_) == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_box(0);
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v___y_1191_);
return v___x_1193_;
}
else
{
lean_object* v_head_1194_; lean_object* v_items_1195_; 
v_head_1194_ = lean_ctor_get(v_x_1190_, 0);
v_items_1195_ = lean_ctor_get(v_head_1194_, 1);
lean_inc(v_items_1195_);
if (lean_obj_tag(v_items_1195_) == 0)
{
lean_object* v_tail_1196_; 
v_tail_1196_ = lean_ctor_get(v_x_1190_, 1);
lean_inc(v_tail_1196_);
lean_dec_ref(v_x_1190_);
v_x_1190_ = v_tail_1196_;
goto _start;
}
else
{
lean_object* v_head_1198_; lean_object* v_tail_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1465_; 
lean_inc(v_head_1194_);
v_head_1198_ = lean_ctor_get(v_items_1195_, 0);
lean_inc(v_head_1198_);
v_tail_1199_ = lean_ctor_get(v_x_1190_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_x_1190_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v_x_1190_, 0);
lean_dec(v_unused_1466_);
v___x_1201_ = v_x_1190_;
v_isShared_1202_ = v_isSharedCheck_1465_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_tail_1199_);
lean_dec(v_x_1190_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1465_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v_fla_1203_; uint8_t v_flb_1204_; lean_object* v_tail_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1463_; 
v_fla_1203_ = lean_ctor_get(v_head_1194_, 0);
lean_inc(v_fla_1203_);
v_flb_1204_ = lean_ctor_get_uint8(v_head_1194_, sizeof(void*)*2);
lean_dec(v_head_1194_);
v_tail_1205_ = lean_ctor_get(v_items_1195_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_items_1195_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v_items_1195_, 0);
lean_dec(v_unused_1464_);
v___x_1207_ = v_items_1195_;
v_isShared_1208_ = v_isSharedCheck_1463_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_tail_1205_);
lean_dec(v_items_1195_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1463_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v_f_1209_; lean_object* v_indent_1210_; lean_object* v_activeTags_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1462_; 
v_f_1209_ = lean_ctor_get(v_head_1198_, 0);
v_indent_1210_ = lean_ctor_get(v_head_1198_, 1);
v_activeTags_1211_ = lean_ctor_get(v_head_1198_, 2);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_head_1198_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1213_ = v_head_1198_;
v_isShared_1214_ = v_isSharedCheck_1462_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_activeTags_1211_);
lean_inc(v_indent_1210_);
lean_inc(v_f_1209_);
lean_dec(v_head_1198_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1462_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___y_1216_; uint8_t v___y_1250_; 
switch(lean_obj_tag(v_f_1209_))
{
case 0:
{
lean_object* v___x_1253_; 
lean_del_object(v___x_1213_);
lean_dec(v_activeTags_1211_);
lean_dec(v_indent_1210_);
lean_del_object(v___x_1207_);
lean_del_object(v___x_1201_);
v___x_1253_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1203_, v_flb_1204_, v_tail_1199_, v_tail_1205_);
v_x_1190_ = v___x_1253_;
goto _start;
}
case 1:
{
lean_del_object(v___x_1213_);
lean_dec(v_activeTags_1211_);
lean_del_object(v___x_1207_);
lean_del_object(v___x_1201_);
if (v_flb_1204_ == 0)
{
uint8_t v___x_1255_; 
v___x_1255_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1203_);
if (v___x_1255_ == 0)
{
lean_object* v_out_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1268_; 
v_out_1256_ = lean_ctor_get(v___y_1191_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___y_1191_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; 
v_unused_1269_ = lean_ctor_get(v___y_1191_, 1);
lean_dec(v_unused_1269_);
v___x_1258_ = v___y_1191_;
v_isShared_1259_ = v_isSharedCheck_1268_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_out_1256_);
lean_dec(v___y_1191_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1268_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; uint32_t v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1260_ = l_Int_toNat(v_indent_1210_);
lean_dec(v_indent_1210_);
v___x_1261_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1262_ = 32;
lean_inc(v___x_1260_);
v___x_1263_ = lean_string_pushn(v___x_1261_, v___x_1262_, v___x_1260_);
v___x_1264_ = lean_string_append(v_out_1256_, v___x_1263_);
lean_dec_ref(v___x_1263_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 1, v___x_1260_);
lean_ctor_set(v___x_1258_, 0, v___x_1264_);
v___x_1266_ = v___x_1258_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v___x_1260_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
v___y_1216_ = v___x_1266_;
goto v___jp_1215_;
}
}
}
else
{
lean_object* v_out_1270_; lean_object* v_column_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v_indent_1210_);
v_out_1270_ = lean_ctor_get(v___y_1191_, 0);
v_column_1271_ = lean_ctor_get(v___y_1191_, 1);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___y_1191_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1273_ = v___y_1191_;
v_isShared_1274_ = v_isSharedCheck_1282_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_column_1271_);
lean_inc(v_out_1270_);
lean_dec(v___y_1191_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1282_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1275_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_1276_ = lean_string_append(v_out_1270_, v___x_1275_);
v___x_1277_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_1278_ = lean_nat_add(v_column_1271_, v___x_1277_);
lean_dec(v_column_1271_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v___x_1278_);
lean_ctor_set(v___x_1273_, 0, v___x_1276_);
v___x_1280_ = v___x_1273_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
v___y_1216_ = v___x_1280_;
goto v___jp_1215_;
}
}
}
}
else
{
lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1283_ = l_Int_toNat(v_indent_1210_);
lean_dec(v_indent_1210_);
v___x_1284_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1203_);
lean_dec(v_fla_1203_);
if (v___x_1284_ == 0)
{
lean_object* v_out_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1300_; 
v_out_1285_ = lean_ctor_get(v___y_1191_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___y_1191_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; 
v_unused_1301_ = lean_ctor_get(v___y_1191_, 1);
lean_dec(v_unused_1301_);
v___x_1287_ = v___y_1191_;
v_isShared_1288_ = v_isSharedCheck_1300_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_out_1285_);
lean_dec(v___y_1191_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1300_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; uint32_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1289_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1290_ = 32;
lean_inc(v___x_1283_);
v___x_1291_ = lean_string_pushn(v___x_1289_, v___x_1290_, v___x_1283_);
v___x_1292_ = lean_string_append(v_out_1285_, v___x_1291_);
lean_dec_ref(v___x_1291_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 1, v___x_1283_);
lean_ctor_set(v___x_1287_, 0, v___x_1292_);
v___x_1294_ = v___x_1287_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v___x_1283_);
v___x_1294_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1295_; lean_object* v_fst_1296_; lean_object* v_snd_1297_; 
v___x_1295_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1204_, v_tail_1205_, v_tail_1199_, v_w_1189_, v___x_1294_);
v_fst_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_fst_1296_);
v_snd_1297_ = lean_ctor_get(v___x_1295_, 1);
lean_inc(v_snd_1297_);
lean_dec_ref(v___x_1295_);
v_x_1190_ = v_fst_1296_;
v___y_1191_ = v_snd_1297_;
goto _start;
}
}
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v_fst_1306_; 
v___x_1302_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_1303_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_1304_ = lean_nat_sub(v_w_1189_, v___x_1303_);
lean_inc(v_tail_1199_);
lean_inc(v_tail_1205_);
v___x_1305_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1204_, v_tail_1205_, v_tail_1199_, v___x_1304_, v___y_1191_);
lean_dec(v___x_1304_);
v_fst_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_fst_1306_);
if (lean_obj_tag(v_fst_1306_) == 1)
{
lean_object* v_head_1307_; lean_object* v_snd_1308_; lean_object* v_fla_1309_; uint8_t v___x_1310_; 
v_head_1307_ = lean_ctor_get(v_fst_1306_, 0);
v_snd_1308_ = lean_ctor_get(v___x_1305_, 1);
lean_inc(v_snd_1308_);
lean_dec_ref(v___x_1305_);
v_fla_1309_ = lean_ctor_get(v_head_1307_, 0);
v___x_1310_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1309_);
if (v___x_1310_ == 0)
{
lean_object* v_out_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref(v_fst_1306_);
v_out_1311_ = lean_ctor_get(v_snd_1308_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_snd_1308_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; 
v_unused_1327_ = lean_ctor_get(v_snd_1308_, 1);
lean_dec(v_unused_1327_);
v___x_1313_ = v_snd_1308_;
v_isShared_1314_ = v_isSharedCheck_1326_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_out_1311_);
lean_dec(v_snd_1308_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1326_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; uint32_t v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1315_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1316_ = 32;
lean_inc(v___x_1283_);
v___x_1317_ = lean_string_pushn(v___x_1315_, v___x_1316_, v___x_1283_);
v___x_1318_ = lean_string_append(v_out_1311_, v___x_1317_);
lean_dec_ref(v___x_1317_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 1, v___x_1283_);
lean_ctor_set(v___x_1313_, 0, v___x_1318_);
v___x_1320_ = v___x_1313_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1318_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1283_);
v___x_1320_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
lean_object* v___x_1321_; lean_object* v_fst_1322_; lean_object* v_snd_1323_; 
v___x_1321_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1204_, v_tail_1205_, v_tail_1199_, v_w_1189_, v___x_1320_);
v_fst_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_fst_1322_);
v_snd_1323_ = lean_ctor_get(v___x_1321_, 1);
lean_inc(v_snd_1323_);
lean_dec_ref(v___x_1321_);
v_x_1190_ = v_fst_1322_;
v___y_1191_ = v_snd_1323_;
goto _start;
}
}
}
else
{
lean_object* v_out_1328_; lean_object* v_column_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1339_; 
lean_dec(v___x_1283_);
lean_dec(v_tail_1205_);
lean_dec(v_tail_1199_);
v_out_1328_ = lean_ctor_get(v_snd_1308_, 0);
v_column_1329_ = lean_ctor_get(v_snd_1308_, 1);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_snd_1308_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1331_ = v_snd_1308_;
v_isShared_1332_ = v_isSharedCheck_1339_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_column_1329_);
lean_inc(v_out_1328_);
lean_dec(v_snd_1308_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1339_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1333_ = lean_string_append(v_out_1328_, v___x_1302_);
v___x_1334_ = lean_nat_add(v_column_1329_, v___x_1303_);
lean_dec(v_column_1329_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 1, v___x_1334_);
lean_ctor_set(v___x_1331_, 0, v___x_1333_);
v___x_1336_ = v___x_1331_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1333_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v___x_1334_);
v___x_1336_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
v_x_1190_ = v_fst_1306_;
v___y_1191_ = v___x_1336_;
goto _start;
}
}
}
}
else
{
lean_object* v_snd_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec(v_fst_1306_);
lean_dec(v___x_1283_);
lean_dec(v_tail_1205_);
lean_dec(v_tail_1199_);
v_snd_1340_ = lean_ctor_get(v___x_1305_, 1);
lean_inc(v_snd_1340_);
lean_dec_ref(v___x_1305_);
v___x_1341_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___closed__0));
v___x_1342_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(v___x_1341_, v_snd_1340_);
return v___x_1342_;
}
}
}
}
case 2:
{
uint8_t v_force_1343_; uint8_t v___x_1344_; 
lean_del_object(v___x_1213_);
lean_dec(v_activeTags_1211_);
lean_del_object(v___x_1207_);
lean_del_object(v___x_1201_);
v_force_1343_ = lean_ctor_get_uint8(v_f_1209_, 0);
lean_dec_ref(v_f_1209_);
v___x_1344_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1203_);
if (v___x_1344_ == 0)
{
v___y_1250_ = v___x_1344_;
goto v___jp_1249_;
}
else
{
if (v_force_1343_ == 0)
{
v___y_1250_ = v___x_1344_;
goto v___jp_1249_;
}
else
{
goto v___jp_1219_;
}
}
}
case 3:
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1401_; 
lean_del_object(v___x_1201_);
v_a_1345_ = lean_ctor_get(v_f_1209_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_f_1209_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1347_ = v_f_1209_;
v_isShared_1348_ = v_isSharedCheck_1401_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v_f_1209_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1401_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
uint32_t v___x_1349_; lean_object* v_p_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1349_ = 10;
lean_inc_ref(v_a_1345_);
v_p_1350_ = lean_string_posof(v_a_1345_, v___x_1349_);
v___x_1351_ = lean_string_utf8_byte_size(v_a_1345_);
v___x_1352_ = lean_nat_dec_eq(v_p_1350_, v___x_1351_);
if (v___x_1352_ == 0)
{
lean_object* v_out_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1387_; 
v_out_1353_ = lean_ctor_get(v___y_1191_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___y_1191_);
if (v_isSharedCheck_1387_ == 0)
{
lean_object* v_unused_1388_; 
v_unused_1388_ = lean_ctor_get(v___y_1191_, 1);
lean_dec(v_unused_1388_);
v___x_1355_ = v___y_1191_;
v_isShared_1356_ = v_isSharedCheck_1387_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_out_1353_);
lean_dec(v___y_1191_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1387_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; uint32_t v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = lean_string_utf8_extract(v_a_1345_, v___x_1357_, v_p_1350_);
v___x_1359_ = lean_string_append(v_out_1353_, v___x_1358_);
lean_dec_ref(v___x_1358_);
v___x_1360_ = l_Int_toNat(v_indent_1210_);
v___x_1361_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1362_ = 32;
lean_inc(v___x_1360_);
v___x_1363_ = lean_string_pushn(v___x_1361_, v___x_1362_, v___x_1360_);
v___x_1364_ = lean_string_append(v___x_1359_, v___x_1363_);
lean_dec_ref(v___x_1363_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v___x_1360_);
lean_ctor_set(v___x_1355_, 0, v___x_1364_);
v___x_1366_ = v___x_1355_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v___x_1360_);
v___x_1366_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1367_ = lean_string_utf8_next(v_a_1345_, v_p_1350_);
lean_dec(v_p_1350_);
v___x_1368_ = lean_string_utf8_extract(v_a_1345_, v___x_1367_, v___x_1351_);
lean_dec(v___x_1367_);
lean_dec_ref(v_a_1345_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1368_);
v___x_1370_ = v___x_1347_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1372_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1370_);
v___x_1372_ = v___x_1213_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_indent_1210_);
lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_activeTags_1211_);
v___x_1372_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v_is_1374_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1372_);
v_is_1374_ = v___x_1207_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_tail_1205_);
v_is_1374_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1375_ = lean_box(1);
v___x_1376_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_1203_, v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v_fst_1378_; lean_object* v_snd_1379_; 
lean_dec(v_fla_1203_);
v___x_1377_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1204_, v_is_1374_, v_tail_1199_, v_w_1189_, v___x_1366_);
v_fst_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_fst_1378_);
v_snd_1379_ = lean_ctor_get(v___x_1377_, 1);
lean_inc(v_snd_1379_);
lean_dec_ref(v___x_1377_);
v_x_1190_ = v_fst_1378_;
v___y_1191_ = v_snd_1379_;
goto _start;
}
else
{
lean_object* v___x_1381_; 
v___x_1381_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1203_, v_flb_1204_, v_tail_1199_, v_is_1374_);
v_x_1190_ = v___x_1381_;
v___y_1191_ = v___x_1366_;
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
lean_object* v_out_1389_; lean_object* v_column_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1400_; 
lean_dec(v_p_1350_);
lean_del_object(v___x_1347_);
lean_del_object(v___x_1213_);
lean_dec(v_activeTags_1211_);
lean_dec(v_indent_1210_);
lean_del_object(v___x_1207_);
v_out_1389_ = lean_ctor_get(v___y_1191_, 0);
v_column_1390_ = lean_ctor_get(v___y_1191_, 1);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___y_1191_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1392_ = v___y_1191_;
v_isShared_1393_ = v_isSharedCheck_1400_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_column_1390_);
lean_inc(v_out_1389_);
lean_dec(v___y_1191_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1400_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1394_ = lean_string_append(v_out_1389_, v_a_1345_);
v___x_1395_ = lean_string_length(v_a_1345_);
lean_dec_ref(v_a_1345_);
v___x_1396_ = lean_nat_add(v_column_1390_, v___x_1395_);
lean_dec(v___x_1395_);
lean_dec(v_column_1390_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 1, v___x_1396_);
lean_ctor_set(v___x_1392_, 0, v___x_1394_);
v___x_1398_ = v___x_1392_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
v___y_1216_ = v___x_1398_;
goto v___jp_1215_;
}
}
}
}
}
case 4:
{
lean_object* v_indent_1402_; lean_object* v_f_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
lean_del_object(v___x_1201_);
v_indent_1402_ = lean_ctor_get(v_f_1209_, 0);
lean_inc(v_indent_1402_);
v_f_1403_ = lean_ctor_get(v_f_1209_, 1);
lean_inc(v_f_1403_);
lean_dec_ref(v_f_1209_);
v___x_1404_ = lean_int_add(v_indent_1210_, v_indent_1402_);
lean_dec(v_indent_1402_);
lean_dec(v_indent_1210_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 1, v___x_1404_);
lean_ctor_set(v___x_1213_, 0, v_f_1403_);
v___x_1406_ = v___x_1213_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_f_1403_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1412_, 2, v_activeTags_1211_);
v___x_1406_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1408_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1406_);
v___x_1408_ = v___x_1207_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_tail_1205_);
v___x_1408_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; 
v___x_1409_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1203_, v_flb_1204_, v_tail_1199_, v___x_1408_);
v_x_1190_ = v___x_1409_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_1413_; lean_object* v_a_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v_a_1413_ = lean_ctor_get(v_f_1209_, 0);
lean_inc(v_a_1413_);
v_a_1414_ = lean_ctor_get(v_f_1209_, 1);
lean_inc(v_a_1414_);
lean_dec_ref(v_f_1209_);
v___x_1415_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_1210_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 2, v___x_1415_);
lean_ctor_set(v___x_1213_, 0, v_a_1413_);
v___x_1417_ = v___x_1213_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1413_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_indent_1210_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1418_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1418_, 0, v_a_1414_);
lean_ctor_set(v___x_1418_, 1, v_indent_1210_);
lean_ctor_set(v___x_1418_, 2, v_activeTags_1211_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1418_);
v___x_1420_ = v___x_1207_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_tail_1205_);
v___x_1420_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1422_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 1, v___x_1420_);
lean_ctor_set(v___x_1201_, 0, v___x_1417_);
v___x_1422_ = v___x_1201_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1423_; 
v___x_1423_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1203_, v_flb_1204_, v_tail_1199_, v___x_1422_);
v_x_1190_ = v___x_1423_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_1428_; uint8_t v_behavior_1429_; uint8_t v___x_1430_; 
lean_del_object(v___x_1201_);
v_a_1428_ = lean_ctor_get(v_f_1209_, 0);
lean_inc(v_a_1428_);
v_behavior_1429_ = lean_ctor_get_uint8(v_f_1209_, sizeof(void*)*1);
lean_dec_ref(v_f_1209_);
v___x_1430_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1203_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1432_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v_a_1428_);
v___x_1432_ = v___x_1213_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1428_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_indent_1210_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v_activeTags_1211_);
v___x_1432_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1433_ = lean_box(0);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v___x_1433_);
lean_ctor_set(v___x_1207_, 0, v___x_1432_);
v___x_1435_ = v___x_1207_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v_fst_1438_; lean_object* v_snd_1439_; 
v___x_1436_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1203_, v_flb_1204_, v_tail_1199_, v_tail_1205_);
v___x_1437_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_behavior_1429_, v___x_1435_, v___x_1436_, v_w_1189_, v___y_1191_);
v_fst_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_fst_1438_);
v_snd_1439_ = lean_ctor_get(v___x_1437_, 1);
lean_inc(v_snd_1439_);
lean_dec_ref(v___x_1437_);
v_x_1190_ = v_fst_1438_;
v___y_1191_ = v_snd_1439_;
goto _start;
}
}
}
else
{
lean_object* v___x_1444_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v_a_1428_);
v___x_1444_ = v___x_1213_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1428_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_indent_1210_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_activeTags_1211_);
v___x_1444_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1446_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1444_);
v___x_1446_ = v___x_1207_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_tail_1205_);
v___x_1446_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; 
v___x_1447_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1203_, v_flb_1204_, v_tail_1199_, v___x_1446_);
v_x_1190_ = v___x_1447_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
lean_del_object(v___x_1201_);
v_a_1451_ = lean_ctor_get(v_f_1209_, 1);
lean_inc(v_a_1451_);
lean_dec_ref(v_f_1209_);
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = lean_nat_add(v_activeTags_1211_, v___x_1452_);
lean_dec(v_activeTags_1211_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 2, v___x_1453_);
lean_ctor_set(v___x_1213_, 0, v_a_1451_);
v___x_1455_ = v___x_1213_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1451_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_indent_1210_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1457_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1455_);
v___x_1457_ = v___x_1207_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_tail_1205_);
v___x_1457_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; 
v___x_1458_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1203_, v_flb_1204_, v_tail_1199_, v___x_1457_);
v_x_1190_ = v___x_1458_;
goto _start;
}
}
}
}
v___jp_1215_:
{
lean_object* v___x_1217_; 
v___x_1217_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1203_, v_flb_1204_, v_tail_1199_, v_tail_1205_);
v_x_1190_ = v___x_1217_;
v___y_1191_ = v___y_1216_;
goto _start;
}
v___jp_1219_:
{
lean_object* v_out_1220_; lean_object* v_column_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1248_; 
v_out_1220_ = lean_ctor_get(v___y_1191_, 0);
v_column_1221_ = lean_ctor_get(v___y_1191_, 1);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___y_1191_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1223_ = v___y_1191_;
v_isShared_1224_ = v_isSharedCheck_1248_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_column_1221_);
lean_inc(v_out_1220_);
lean_dec(v___y_1191_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1248_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; uint8_t v___x_1226_; 
lean_inc(v_column_1221_);
v___x_1225_ = lean_nat_to_int(v_column_1221_);
v___x_1226_ = lean_int_dec_lt(v___x_1225_, v_indent_1210_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; uint32_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1233_; 
lean_dec(v___x_1225_);
lean_dec(v_column_1221_);
v___x_1227_ = l_Int_toNat(v_indent_1210_);
lean_dec(v_indent_1210_);
v___x_1228_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1229_ = 32;
lean_inc(v___x_1227_);
v___x_1230_ = lean_string_pushn(v___x_1228_, v___x_1229_, v___x_1227_);
v___x_1231_ = lean_string_append(v_out_1220_, v___x_1230_);
lean_dec_ref(v___x_1230_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v___x_1227_);
lean_ctor_set(v___x_1223_, 0, v___x_1231_);
v___x_1233_ = v___x_1223_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v___x_1227_);
v___x_1233_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1234_; 
v___x_1234_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1203_, v_flb_1204_, v_tail_1199_, v_tail_1205_);
v_x_1190_ = v___x_1234_;
v___y_1191_ = v___x_1233_;
goto _start;
}
}
else
{
lean_object* v___x_1237_; uint32_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1237_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_1238_ = 32;
v___x_1239_ = lean_int_sub(v_indent_1210_, v___x_1225_);
lean_dec(v___x_1225_);
lean_dec(v_indent_1210_);
v___x_1240_ = l_Int_toNat(v___x_1239_);
lean_dec(v___x_1239_);
v___x_1241_ = lean_string_pushn(v___x_1237_, v___x_1238_, v___x_1240_);
v___x_1242_ = lean_string_append(v_out_1220_, v___x_1241_);
v___x_1243_ = lean_string_length(v___x_1241_);
lean_dec_ref(v___x_1241_);
v___x_1244_ = lean_nat_add(v_column_1221_, v___x_1243_);
lean_dec(v___x_1243_);
lean_dec(v_column_1221_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v___x_1244_);
lean_ctor_set(v___x_1223_, 0, v___x_1242_);
v___x_1246_ = v___x_1223_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
v___y_1216_ = v___x_1246_;
goto v___jp_1215_;
}
}
}
}
v___jp_1249_:
{
if (v___y_1250_ == 0)
{
goto v___jp_1219_;
}
else
{
lean_object* v___x_1251_; 
lean_dec(v_indent_1210_);
v___x_1251_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1203_, v_flb_1204_, v_tail_1199_, v_tail_1205_);
v_x_1190_ = v___x_1251_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0___boxed(lean_object* v_w_1467_, lean_object* v_x_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_1467_, v_x_1468_, v___y_1469_);
lean_dec(v_w_1467_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(lean_object* v_f_1471_, lean_object* v_w_1472_, lean_object* v_indent_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1475_; uint8_t v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1475_ = lean_box(1);
v___x_1476_ = 0;
v___x_1477_ = lean_nat_to_int(v_indent_1473_);
v___x_1478_ = lean_unsigned_to_nat(0u);
v___x_1479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1479_, 0, v_f_1471_);
lean_ctor_set(v___x_1479_, 1, v___x_1477_);
lean_ctor_set(v___x_1479_, 2, v___x_1478_);
v___x_1480_ = lean_box(0);
v___x_1481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1479_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
v___x_1482_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1482_, 0, v___x_1475_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
lean_ctor_set_uint8(v___x_1482_, sizeof(void*)*2, v___x_1476_);
v___x_1483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
lean_ctor_set(v___x_1483_, 1, v___x_1480_);
v___x_1484_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_1472_, v___x_1483_, v___y_1474_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0___boxed(lean_object* v_f_1485_, lean_object* v_w_1486_, lean_object* v_indent_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(v_f_1485_, v_w_1486_, v_indent_1487_, v___y_1488_);
lean_dec(v_w_1486_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty(lean_object* v_f_1490_, lean_object* v_width_1491_, lean_object* v_indent_1492_, lean_object* v_column_1493_){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v_snd_1497_; lean_object* v_out_1498_; 
v___x_1494_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v_column_1493_);
v___x_1496_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(v_f_1490_, v_width_1491_, v_indent_1492_, v___x_1495_);
v_snd_1497_ = lean_ctor_get(v___x_1496_, 1);
lean_inc(v_snd_1497_);
lean_dec_ref(v___x_1496_);
v_out_1498_ = lean_ctor_get(v_snd_1497_, 0);
lean_inc_ref(v_out_1498_);
lean_dec(v_snd_1497_);
return v_out_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty___boxed(lean_object* v_f_1499_, lean_object* v_width_1500_, lean_object* v_indent_1501_, lean_object* v_column_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Std_Format_pretty(v_f_1499_, v_width_1500_, v_indent_1501_, v_column_1502_);
lean_dec(v_width_1500_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0(lean_object* v_f_1504_){
_start:
{
lean_inc(v_f_1504_);
return v_f_1504_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object* v_f_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Std_instToFormatFormat___lam__0(v_f_1505_);
lean_dec(v_f_1505_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatString___lam__0(lean_object* v_s_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_s_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg___lam__0(lean_object* v_x_1513_, lean_object* v_inst_1514_, lean_object* v_x1_1515_, lean_object* v_x2_1516_){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1517_, 0, v_x1_1515_);
lean_ctor_set(v___x_1517_, 1, v_x_1513_);
v___x_1518_ = lean_apply_1(v_inst_1514_, v_x2_1516_);
v___x_1519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg(lean_object* v_inst_1520_, lean_object* v_x_1521_, lean_object* v_x_1522_){
_start:
{
if (lean_obj_tag(v_x_1521_) == 0)
{
lean_object* v___x_1523_; 
lean_dec(v_x_1522_);
lean_dec_ref(v_inst_1520_);
v___x_1523_ = lean_box(0);
return v___x_1523_;
}
else
{
lean_object* v_tail_1524_; 
v_tail_1524_ = lean_ctor_get(v_x_1521_, 1);
if (lean_obj_tag(v_tail_1524_) == 0)
{
lean_object* v_head_1525_; lean_object* v___x_1526_; 
lean_dec(v_x_1522_);
v_head_1525_ = lean_ctor_get(v_x_1521_, 0);
lean_inc(v_head_1525_);
lean_dec_ref(v_x_1521_);
v___x_1526_ = lean_apply_1(v_inst_1520_, v_head_1525_);
return v___x_1526_;
}
else
{
lean_object* v_head_1527_; lean_object* v___f_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_inc(v_tail_1524_);
v_head_1527_ = lean_ctor_get(v_x_1521_, 0);
lean_inc(v_head_1527_);
lean_dec_ref(v_x_1521_);
lean_inc_ref(v_inst_1520_);
v___f_1528_ = lean_alloc_closure((void*)(l_Std_Format_joinSep___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1528_, 0, v_x_1522_);
lean_closure_set(v___f_1528_, 1, v_inst_1520_);
v___x_1529_ = lean_apply_1(v_inst_1520_, v_head_1527_);
v___x_1530_ = l_List_foldl___redArg(v___f_1528_, v___x_1529_, v_tail_1524_);
return v___x_1530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep(lean_object* v_00_u03b1_1531_, lean_object* v_inst_1532_, lean_object* v_x_1533_, lean_object* v_x_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Std_Format_joinSep___redArg(v_inst_1532_, v_x_1533_, v_x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg___lam__0(lean_object* v_pre_1536_, lean_object* v_inst_1537_, lean_object* v_x1_1538_, lean_object* v_x2_1539_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1540_, 0, v_x1_1538_);
lean_ctor_set(v___x_1540_, 1, v_pre_1536_);
v___x_1541_ = lean_apply_1(v_inst_1537_, v_x2_1539_);
v___x_1542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg(lean_object* v_inst_1543_, lean_object* v_pre_1544_, lean_object* v_x_1545_){
_start:
{
if (lean_obj_tag(v_x_1545_) == 0)
{
lean_object* v___x_1546_; 
lean_dec(v_pre_1544_);
lean_dec_ref(v_inst_1543_);
v___x_1546_ = lean_box(0);
return v___x_1546_;
}
else
{
lean_object* v_head_1547_; lean_object* v_tail_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1558_; 
v_head_1547_ = lean_ctor_get(v_x_1545_, 0);
v_tail_1548_ = lean_ctor_get(v_x_1545_, 1);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_x_1545_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1550_ = v_x_1545_;
v_isShared_1551_ = v_isSharedCheck_1558_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_tail_1548_);
lean_inc(v_head_1547_);
lean_dec(v_x_1545_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1558_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___f_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
lean_inc_ref(v_inst_1543_);
lean_inc(v_pre_1544_);
v___f_1552_ = lean_alloc_closure((void*)(l_Std_Format_prefixJoin___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1552_, 0, v_pre_1544_);
lean_closure_set(v___f_1552_, 1, v_inst_1543_);
v___x_1553_ = lean_apply_1(v_inst_1543_, v_head_1547_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set_tag(v___x_1550_, 5);
lean_ctor_set(v___x_1550_, 1, v___x_1553_);
lean_ctor_set(v___x_1550_, 0, v_pre_1544_);
v___x_1555_ = v___x_1550_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_pre_1544_);
lean_ctor_set(v_reuseFailAlloc_1557_, 1, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_List_foldl___redArg(v___f_1552_, v___x_1555_, v_tail_1548_);
return v___x_1556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin(lean_object* v_00_u03b1_1559_, lean_object* v_inst_1560_, lean_object* v_pre_1561_, lean_object* v_x_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Std_Format_prefixJoin___redArg(v_inst_1560_, v_pre_1561_, v_x_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg___lam__0(lean_object* v_inst_1564_, lean_object* v_x_1565_, lean_object* v_x1_1566_, lean_object* v_x2_1567_){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = lean_apply_1(v_inst_1564_, v_x2_1567_);
v___x_1569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1569_, 0, v_x1_1566_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
lean_ctor_set(v___x_1570_, 1, v_x_1565_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg(lean_object* v_inst_1571_, lean_object* v_x_1572_, lean_object* v_x_1573_){
_start:
{
if (lean_obj_tag(v_x_1572_) == 0)
{
lean_object* v___x_1574_; 
lean_dec(v_x_1573_);
lean_dec_ref(v_inst_1571_);
v___x_1574_ = lean_box(0);
return v___x_1574_;
}
else
{
lean_object* v_head_1575_; lean_object* v_tail_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1586_; 
v_head_1575_ = lean_ctor_get(v_x_1572_, 0);
v_tail_1576_ = lean_ctor_get(v_x_1572_, 1);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_x_1572_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1578_ = v_x_1572_;
v_isShared_1579_ = v_isSharedCheck_1586_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_tail_1576_);
lean_inc(v_head_1575_);
lean_dec(v_x_1572_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1586_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___f_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; 
lean_inc(v_x_1573_);
lean_inc_ref(v_inst_1571_);
v___f_1580_ = lean_alloc_closure((void*)(l_Std_Format_joinSuffix___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1580_, 0, v_inst_1571_);
lean_closure_set(v___f_1580_, 1, v_x_1573_);
v___x_1581_ = lean_apply_1(v_inst_1571_, v_head_1575_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set_tag(v___x_1578_, 5);
lean_ctor_set(v___x_1578_, 1, v_x_1573_);
lean_ctor_set(v___x_1578_, 0, v___x_1581_);
v___x_1583_ = v___x_1578_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_x_1573_);
v___x_1583_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_List_foldl___redArg(v___f_1580_, v___x_1583_, v_tail_1576_);
return v___x_1584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix(lean_object* v_00_u03b1_1587_, lean_object* v_inst_1588_, lean_object* v_x_1589_, lean_object* v_x_1590_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Std_Format_joinSuffix___redArg(v_inst_1588_, v_x_1589_, v_x_1590_);
return v___x_1591_;
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
res = runtime_initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
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
res = initialize_Init_Data_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Format_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
