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
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_string_posof(lean_object*, uint32_t);
lean_object* lean_string_offsetofpos(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_pushn(lean_object*, uint32_t, lean_object*);
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
static const lean_ctor_object l_Std_Format_instInhabitedSpaceResult_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Format_instInhabitedSpaceResult_default___closed__0 = (const lean_object*)&l_Std_Format_instInhabitedSpaceResult_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Format_instInhabitedSpaceResult_default = (const lean_object*)&l_Std_Format_instInhabitedSpaceResult_default___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instInhabitedSpaceResult = (const lean_object*)&l_Std_Format_instInhabitedSpaceResult_default___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unreachable"};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__0_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__1_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__15_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__3_value),((lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__3_value)}};
static const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16 = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16_value;
LEAN_EXPORT const lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState = (const lean_object*)&l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___closed__16_value;
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
lean_dec_ref_known(v_t_79_, 0);
v___x_82_ = lean_box(v_force_81_);
v___x_83_ = lean_apply_1(v_k_80_, v___x_82_);
return v___x_83_;
}
case 3:
{
lean_object* v_a_84_; lean_object* v___x_85_; 
v_a_84_ = lean_ctor_get(v_t_79_, 0);
lean_inc_ref(v_a_84_);
lean_dec_ref_known(v_t_79_, 1);
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
lean_dec_ref_known(v_t_79_, 2);
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
lean_dec_ref_known(v_t_79_, 2);
v___x_91_ = lean_apply_2(v_k_80_, v_a_89_, v_a_90_);
return v___x_91_;
}
case 6:
{
lean_object* v_a_92_; uint8_t v_behavior_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_a_92_ = lean_ctor_get(v_t_79_, 0);
lean_inc(v_a_92_);
v_behavior_93_ = lean_ctor_get_uint8(v_t_79_, sizeof(void*)*1);
lean_dec_ref_known(v_t_79_, 1);
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
lean_dec_ref_known(v_t_79_, 2);
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
v___x_281_ = ((lean_object*)(l_Std_Format_instInhabitedSpaceResult_default___closed__0));
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
lean_dec_ref_known(v_x_267_, 0);
v___y_272_ = v_x_268_;
goto v___jp_271_;
}
else
{
uint8_t v_force_286_; uint8_t v___x_287_; 
v_force_286_ = lean_ctor_get_uint8(v_x_267_, 0);
lean_dec_ref_known(v_x_267_, 0);
v___x_287_ = lean_bool_not(v_force_286_);
if (v___x_287_ == 0)
{
v___y_272_ = v___x_287_;
goto v___jp_271_;
}
else
{
lean_object* v___x_288_; 
lean_dec(v_x_270_);
lean_dec(v_x_269_);
v___x_288_ = ((lean_object*)(l_Std_Format_instInhabitedSpaceResult_default___closed__0));
return v___x_288_;
}
}
}
case 3:
{
lean_object* v_a_289_; uint32_t v___x_290_; lean_object* v_p_291_; lean_object* v_off_292_; lean_object* v___x_293_; uint8_t v___x_294_; uint8_t v___x_295_; 
lean_dec(v_x_270_);
lean_dec(v_x_269_);
v_a_289_ = lean_ctor_get(v_x_267_, 0);
lean_inc_ref_n(v_a_289_, 3);
lean_dec_ref_known(v_x_267_, 1);
v___x_290_ = 10;
v_p_291_ = lean_string_posof(v_a_289_, v___x_290_);
lean_inc(v_p_291_);
v_off_292_ = lean_string_offsetofpos(v_a_289_, v_p_291_);
v___x_293_ = lean_string_utf8_byte_size(v_a_289_);
lean_dec_ref(v_a_289_);
v___x_294_ = lean_nat_dec_eq(v_p_291_, v___x_293_);
lean_dec(v_p_291_);
v___x_295_ = lean_bool_not(v___x_294_);
if (v_x_268_ == 0)
{
lean_object* v___x_296_; 
v___x_296_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_296_, 0, v_off_292_);
lean_ctor_set_uint8(v___x_296_, sizeof(void*)*1, v___x_295_);
lean_ctor_set_uint8(v___x_296_, sizeof(void*)*1 + 1, v_x_268_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; 
v___x_297_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_297_, 0, v_off_292_);
lean_ctor_set_uint8(v___x_297_, sizeof(void*)*1, v___x_295_);
lean_ctor_set_uint8(v___x_297_, sizeof(void*)*1 + 1, v___x_295_);
return v___x_297_;
}
}
case 4:
{
lean_object* v_indent_298_; lean_object* v_f_299_; lean_object* v___x_300_; 
v_indent_298_ = lean_ctor_get(v_x_267_, 0);
lean_inc(v_indent_298_);
v_f_299_ = lean_ctor_get(v_x_267_, 1);
lean_inc(v_f_299_);
lean_dec_ref_known(v_x_267_, 2);
v___x_300_ = lean_int_sub(v_x_269_, v_indent_298_);
lean_dec(v_indent_298_);
lean_dec(v_x_269_);
v_x_267_ = v_f_299_;
v_x_269_ = v___x_300_;
goto _start;
}
case 5:
{
lean_object* v_a_302_; lean_object* v_a_303_; lean_object* v___x_304_; uint8_t v_foundLine_305_; lean_object* v_space_306_; uint8_t v___y_308_; uint8_t v___x_322_; 
v_a_302_ = lean_ctor_get(v_x_267_, 0);
lean_inc(v_a_302_);
v_a_303_ = lean_ctor_get(v_x_267_, 1);
lean_inc(v_a_303_);
lean_dec_ref_known(v_x_267_, 2);
lean_inc(v_x_270_);
lean_inc(v_x_269_);
v___x_304_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_a_302_, v_x_268_, v_x_269_, v_x_270_);
v_foundLine_305_ = lean_ctor_get_uint8(v___x_304_, sizeof(void*)*1);
v_space_306_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_space_306_);
v___x_322_ = lean_nat_dec_lt(v_x_270_, v_space_306_);
if (v___x_322_ == 0)
{
v___y_308_ = v_foundLine_305_;
goto v___jp_307_;
}
else
{
v___y_308_ = v___x_322_;
goto v___jp_307_;
}
v___jp_307_:
{
if (v___y_308_ == 0)
{
lean_object* v___x_309_; lean_object* v_r_u2082_310_; uint8_t v_foundLine_311_; uint8_t v_foundFlattenedHardLine_312_; lean_object* v_space_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_321_; 
lean_dec_ref(v___x_304_);
v___x_309_ = lean_nat_sub(v_x_270_, v_space_306_);
lean_dec(v_x_270_);
v_r_u2082_310_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_a_303_, v_x_268_, v_x_269_, v___x_309_);
v_foundLine_311_ = lean_ctor_get_uint8(v_r_u2082_310_, sizeof(void*)*1);
v_foundFlattenedHardLine_312_ = lean_ctor_get_uint8(v_r_u2082_310_, sizeof(void*)*1 + 1);
v_space_313_ = lean_ctor_get(v_r_u2082_310_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v_r_u2082_310_);
if (v_isSharedCheck_321_ == 0)
{
v___x_315_ = v_r_u2082_310_;
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_space_313_);
lean_dec(v_r_u2082_310_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = lean_nat_add(v_space_306_, v_space_313_);
lean_dec(v_space_313_);
lean_dec(v_space_306_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_317_);
v___x_319_ = v___x_315_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
lean_ctor_set_uint8(v_reuseFailAlloc_320_, sizeof(void*)*1, v_foundLine_311_);
lean_ctor_set_uint8(v_reuseFailAlloc_320_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_312_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
else
{
lean_dec(v_space_306_);
lean_dec(v_a_303_);
lean_dec(v_x_270_);
lean_dec(v_x_269_);
return v___x_304_;
}
}
}
case 6:
{
lean_object* v_a_323_; uint8_t v___x_324_; 
v_a_323_ = lean_ctor_get(v_x_267_, 0);
lean_inc(v_a_323_);
lean_dec_ref_known(v_x_267_, 1);
v___x_324_ = 1;
v_x_267_ = v_a_323_;
v_x_268_ = v___x_324_;
goto _start;
}
default: 
{
lean_object* v_a_326_; 
v_a_326_ = lean_ctor_get(v_x_267_, 1);
lean_inc(v_a_326_);
lean_dec_ref_known(v_x_267_, 2);
v_x_267_ = v_a_326_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___boxed(lean_object* v_x_328_, lean_object* v_x_329_, lean_object* v_x_330_, lean_object* v_x_331_){
_start:
{
uint8_t v_x_401__boxed_332_; lean_object* v_res_333_; 
v_x_401__boxed_332_ = lean_unbox(v_x_329_);
v_res_333_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_x_328_, v_x_401__boxed_332_, v_x_330_, v_x_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx(lean_object* v_x_334_){
_start:
{
if (lean_obj_tag(v_x_334_) == 0)
{
lean_object* v___x_335_; 
v___x_335_ = lean_unsigned_to_nat(0u);
return v___x_335_;
}
else
{
lean_object* v___x_336_; 
v___x_336_ = lean_unsigned_to_nat(1u);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx___boxed(lean_object* v_x_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Std_Format_FlattenAllowability_ctorIdx(v_x_337_);
lean_dec(v_x_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___redArg(lean_object* v_t_339_, lean_object* v_k_340_){
_start:
{
if (lean_obj_tag(v_t_339_) == 0)
{
uint8_t v_fits_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_fits_341_ = lean_ctor_get_uint8(v_t_339_, 0);
v___x_342_ = lean_box(v_fits_341_);
v___x_343_ = lean_apply_1(v_k_340_, v___x_342_);
return v___x_343_;
}
else
{
return v_k_340_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___redArg___boxed(lean_object* v_t_344_, lean_object* v_k_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_344_, v_k_345_);
lean_dec(v_t_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim(lean_object* v_motive_347_, lean_object* v_ctorIdx_348_, lean_object* v_t_349_, lean_object* v_h_350_, lean_object* v_k_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_349_, v_k_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___boxed(lean_object* v_motive_353_, lean_object* v_ctorIdx_354_, lean_object* v_t_355_, lean_object* v_h_356_, lean_object* v_k_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_Format_FlattenAllowability_ctorElim(v_motive_353_, v_ctorIdx_354_, v_t_355_, v_h_356_, v_k_357_);
lean_dec(v_t_355_);
lean_dec(v_ctorIdx_354_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___redArg(lean_object* v_t_359_, lean_object* v_allow_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_359_, v_allow_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___redArg___boxed(lean_object* v_t_362_, lean_object* v_allow_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Std_Format_FlattenAllowability_allow_elim___redArg(v_t_362_, v_allow_363_);
lean_dec(v_t_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim(lean_object* v_motive_365_, lean_object* v_t_366_, lean_object* v_h_367_, lean_object* v_allow_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_366_, v_allow_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___boxed(lean_object* v_motive_370_, lean_object* v_t_371_, lean_object* v_h_372_, lean_object* v_allow_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Std_Format_FlattenAllowability_allow_elim(v_motive_370_, v_t_371_, v_h_372_, v_allow_373_);
lean_dec(v_t_371_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___redArg(lean_object* v_t_375_, lean_object* v_disallow_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_375_, v_disallow_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___redArg___boxed(lean_object* v_t_378_, lean_object* v_disallow_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Std_Format_FlattenAllowability_disallow_elim___redArg(v_t_378_, v_disallow_379_);
lean_dec(v_t_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim(lean_object* v_motive_381_, lean_object* v_t_382_, lean_object* v_h_383_, lean_object* v_disallow_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_382_, v_disallow_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___boxed(lean_object* v_motive_386_, lean_object* v_t_387_, lean_object* v_h_388_, lean_object* v_disallow_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_Format_FlattenAllowability_disallow_elim(v_motive_386_, v_t_387_, v_h_388_, v_disallow_389_);
lean_dec(v_t_387_);
return v_res_390_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_instBEqFlattenAllowability_beq(lean_object* v_x_391_, lean_object* v_x_392_){
_start:
{
if (lean_obj_tag(v_x_391_) == 0)
{
if (lean_obj_tag(v_x_392_) == 0)
{
uint8_t v_fits_393_; 
v_fits_393_ = lean_ctor_get_uint8(v_x_391_, 0);
if (v_fits_393_ == 0)
{
uint8_t v_fits_394_; 
v_fits_394_ = lean_ctor_get_uint8(v_x_392_, 0);
if (v_fits_394_ == 0)
{
uint8_t v___x_395_; 
v___x_395_ = 1;
return v___x_395_;
}
else
{
return v_fits_393_;
}
}
else
{
uint8_t v_fits_396_; 
v_fits_396_ = lean_ctor_get_uint8(v_x_392_, 0);
return v_fits_396_;
}
}
else
{
uint8_t v___x_397_; 
v___x_397_ = 0;
return v___x_397_;
}
}
else
{
if (lean_obj_tag(v_x_392_) == 1)
{
uint8_t v___x_398_; 
v___x_398_ = 1;
return v___x_398_;
}
else
{
uint8_t v___x_399_; 
v___x_399_ = 0;
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_instBEqFlattenAllowability_beq___boxed(lean_object* v_x_400_, lean_object* v_x_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_Std_Format_instBEqFlattenAllowability_beq(v_x_400_, v_x_401_);
lean_dec(v_x_401_);
lean_dec(v_x_400_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_FlattenAllowability_shouldFlatten(lean_object* v_x_406_){
_start:
{
if (lean_obj_tag(v_x_406_) == 0)
{
uint8_t v_fits_407_; 
v_fits_407_ = lean_ctor_get_uint8(v_x_406_, 0);
if (v_fits_407_ == 1)
{
return v_fits_407_;
}
else
{
uint8_t v___x_408_; 
v___x_408_ = 0;
return v___x_408_;
}
}
else
{
uint8_t v___x_409_; 
v___x_409_ = 0;
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_shouldFlatten___boxed(lean_object* v_x_410_){
_start:
{
uint8_t v_res_411_; lean_object* v_r_412_; 
v_res_411_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_x_410_);
lean_dec(v_x_410_);
v_r_412_ = lean_box(v_res_411_);
return v_r_412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(lean_object* v_x_413_, lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
if (lean_obj_tag(v_x_413_) == 0)
{
lean_object* v___x_416_; 
lean_dec(v_x_415_);
lean_dec(v_x_414_);
v___x_416_ = ((lean_object*)(l_Std_Format_instInhabitedSpaceResult_default___closed__0));
return v___x_416_;
}
else
{
lean_object* v_head_417_; lean_object* v_items_418_; 
v_head_417_ = lean_ctor_get(v_x_413_, 0);
lean_inc(v_head_417_);
v_items_418_ = lean_ctor_get(v_head_417_, 1);
lean_inc(v_items_418_);
if (lean_obj_tag(v_items_418_) == 0)
{
lean_object* v_tail_419_; 
lean_dec(v_head_417_);
v_tail_419_ = lean_ctor_get(v_x_413_, 1);
lean_inc(v_tail_419_);
lean_dec_ref_known(v_x_413_, 2);
v_x_413_ = v_tail_419_;
goto _start;
}
else
{
lean_object* v_head_421_; lean_object* v_tail_422_; lean_object* v_fla_423_; uint8_t v_flb_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_466_; 
v_head_421_ = lean_ctor_get(v_items_418_, 0);
lean_inc(v_head_421_);
v_tail_422_ = lean_ctor_get(v_x_413_, 1);
lean_inc(v_tail_422_);
lean_dec_ref_known(v_x_413_, 2);
v_fla_423_ = lean_ctor_get(v_head_417_, 0);
v_flb_424_ = lean_ctor_get_uint8(v_head_417_, sizeof(void*)*2);
v_isSharedCheck_466_ = !lean_is_exclusive(v_head_417_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; 
v_unused_467_ = lean_ctor_get(v_head_417_, 1);
lean_dec(v_unused_467_);
v___x_426_ = v_head_417_;
v_isShared_427_ = v_isSharedCheck_466_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_fla_423_);
lean_dec(v_head_417_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_466_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_tail_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_464_; 
v_tail_428_ = lean_ctor_get(v_items_418_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v_items_418_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v_items_418_, 0);
lean_dec(v_unused_465_);
v___x_430_ = v_items_418_;
v_isShared_431_ = v_isSharedCheck_464_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_tail_428_);
lean_dec(v_items_418_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_464_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v_f_432_; lean_object* v_indent_433_; uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v_foundLine_440_; lean_object* v_space_441_; lean_object* v___x_443_; 
v_f_432_ = lean_ctor_get(v_head_421_, 0);
lean_inc(v_f_432_);
v_indent_433_ = lean_ctor_get(v_head_421_, 1);
lean_inc(v_indent_433_);
lean_dec(v_head_421_);
v___x_434_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_423_);
lean_inc_n(v_x_415_, 2);
v___x_435_ = lean_nat_to_int(v_x_415_);
lean_inc(v_x_414_);
v___x_436_ = lean_nat_to_int(v_x_414_);
v___x_437_ = lean_int_add(v___x_435_, v___x_436_);
lean_dec(v___x_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_int_sub(v___x_437_, v_indent_433_);
lean_dec(v_indent_433_);
lean_dec(v___x_437_);
v___x_439_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_f_432_, v___x_434_, v___x_438_, v_x_415_);
v_foundLine_440_ = lean_ctor_get_uint8(v___x_439_, sizeof(void*)*1);
v_space_441_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_space_441_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v_tail_428_);
v___x_443_ = v___x_426_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_fla_423_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_tail_428_);
lean_ctor_set_uint8(v_reuseFailAlloc_463_, sizeof(void*)*2, v_flb_424_);
v___x_443_ = v_reuseFailAlloc_463_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_445_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v_tail_422_);
lean_ctor_set(v___x_430_, 0, v___x_443_);
v___x_445_ = v___x_430_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_tail_422_);
v___x_445_ = v_reuseFailAlloc_462_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
uint8_t v___y_447_; uint8_t v___x_461_; 
v___x_461_ = lean_nat_dec_lt(v_x_415_, v_space_441_);
if (v___x_461_ == 0)
{
v___y_447_ = v_foundLine_440_;
goto v___jp_446_;
}
else
{
v___y_447_ = v___x_461_;
goto v___jp_446_;
}
v___jp_446_:
{
if (v___y_447_ == 0)
{
lean_object* v___x_448_; lean_object* v_r_u2082_449_; uint8_t v_foundLine_450_; uint8_t v_foundFlattenedHardLine_451_; lean_object* v_space_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_460_; 
lean_dec_ref(v___x_439_);
v___x_448_ = lean_nat_sub(v_x_415_, v_space_441_);
lean_dec(v_x_415_);
v_r_u2082_449_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_445_, v_x_414_, v___x_448_);
v_foundLine_450_ = lean_ctor_get_uint8(v_r_u2082_449_, sizeof(void*)*1);
v_foundFlattenedHardLine_451_ = lean_ctor_get_uint8(v_r_u2082_449_, sizeof(void*)*1 + 1);
v_space_452_ = lean_ctor_get(v_r_u2082_449_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v_r_u2082_449_);
if (v_isSharedCheck_460_ == 0)
{
v___x_454_ = v_r_u2082_449_;
v_isShared_455_ = v_isSharedCheck_460_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_space_452_);
lean_dec(v_r_u2082_449_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_460_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_456_ = lean_nat_add(v_space_441_, v_space_452_);
lean_dec(v_space_452_);
lean_dec(v_space_441_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_456_);
v___x_458_ = v___x_454_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
lean_ctor_set_uint8(v_reuseFailAlloc_459_, sizeof(void*)*1, v_foundLine_450_);
lean_ctor_set_uint8(v_reuseFailAlloc_459_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_451_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
else
{
lean_dec_ref(v___x_445_);
lean_dec(v_space_441_);
lean_dec(v_x_415_);
lean_dec(v_x_414_);
return v___x_439_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(uint8_t v_flb_468_, lean_object* v_items_469_, lean_object* v_w_470_, lean_object* v_gs_471_, lean_object* v_toPure_472_, lean_object* v_k_473_){
_start:
{
uint8_t v___y_475_; uint8_t v___x_480_; uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v_g_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v_r_487_; lean_object* v___y_489_; uint8_t v_foundLine_494_; lean_object* v_space_495_; uint8_t v___y_497_; uint8_t v___x_511_; 
v___x_480_ = 0;
v___x_481_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_468_, v___x_480_);
v___x_482_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_482_, 0, v___x_481_);
lean_inc(v_items_469_);
v_g_483_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_483_, 0, v___x_482_);
lean_ctor_set(v_g_483_, 1, v_items_469_);
lean_ctor_set_uint8(v_g_483_, sizeof(void*)*2, v_flb_468_);
v___x_484_ = lean_box(0);
v___x_485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_485_, 0, v_g_483_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = lean_nat_sub(v_w_470_, v_k_473_);
lean_inc(v___x_486_);
lean_inc(v_k_473_);
v_r_487_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_485_, v_k_473_, v___x_486_);
v_foundLine_494_ = lean_ctor_get_uint8(v_r_487_, sizeof(void*)*1);
v_space_495_ = lean_ctor_get(v_r_487_, 0);
lean_inc(v_space_495_);
v___x_511_ = lean_nat_dec_lt(v___x_486_, v_space_495_);
if (v___x_511_ == 0)
{
v___y_497_ = v_foundLine_494_;
goto v___jp_496_;
}
else
{
v___y_497_ = v___x_511_;
goto v___jp_496_;
}
v___jp_474_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_476_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_476_, 0, v___y_475_);
v___x_477_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v_items_469_);
lean_ctor_set_uint8(v___x_477_, sizeof(void*)*2, v_flb_468_);
v___x_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v_gs_471_);
v___x_479_ = lean_apply_2(v_toPure_472_, lean_box(0), v___x_478_);
return v___x_479_;
}
v___jp_488_:
{
uint8_t v_foundFlattenedHardLine_490_; uint8_t v___x_491_; 
v_foundFlattenedHardLine_490_ = lean_ctor_get_uint8(v_r_487_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_487_);
v___x_491_ = lean_bool_not(v_foundFlattenedHardLine_490_);
if (v___x_491_ == 0)
{
lean_dec_ref(v___y_489_);
lean_dec(v___x_486_);
v___y_475_ = v___x_491_;
goto v___jp_474_;
}
else
{
lean_object* v_space_492_; uint8_t v___x_493_; 
v_space_492_ = lean_ctor_get(v___y_489_, 0);
lean_inc(v_space_492_);
lean_dec_ref(v___y_489_);
v___x_493_ = lean_nat_dec_le(v_space_492_, v___x_486_);
lean_dec(v___x_486_);
lean_dec(v_space_492_);
v___y_475_ = v___x_493_;
goto v___jp_474_;
}
}
v___jp_496_:
{
if (v___y_497_ == 0)
{
lean_object* v___x_498_; lean_object* v_r_u2082_499_; uint8_t v_foundLine_500_; uint8_t v_foundFlattenedHardLine_501_; lean_object* v_space_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_510_; 
v___x_498_ = lean_nat_sub(v___x_486_, v_space_495_);
lean_inc(v_gs_471_);
v_r_u2082_499_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_471_, v_k_473_, v___x_498_);
v_foundLine_500_ = lean_ctor_get_uint8(v_r_u2082_499_, sizeof(void*)*1);
v_foundFlattenedHardLine_501_ = lean_ctor_get_uint8(v_r_u2082_499_, sizeof(void*)*1 + 1);
v_space_502_ = lean_ctor_get(v_r_u2082_499_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_r_u2082_499_);
if (v_isSharedCheck_510_ == 0)
{
v___x_504_ = v_r_u2082_499_;
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_space_502_);
lean_dec(v_r_u2082_499_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_506_ = lean_nat_add(v_space_495_, v_space_502_);
lean_dec(v_space_502_);
lean_dec(v_space_495_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_506_);
v___x_508_ = v___x_504_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
lean_ctor_set_uint8(v_reuseFailAlloc_509_, sizeof(void*)*1, v_foundLine_500_);
lean_ctor_set_uint8(v_reuseFailAlloc_509_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_501_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
v___y_489_ = v___x_508_;
goto v___jp_488_;
}
}
}
else
{
lean_dec(v_space_495_);
lean_dec(v_k_473_);
lean_inc_ref(v_r_487_);
v___y_489_ = v_r_487_;
goto v___jp_488_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed(lean_object* v_flb_512_, lean_object* v_items_513_, lean_object* v_w_514_, lean_object* v_gs_515_, lean_object* v_toPure_516_, lean_object* v_k_517_){
_start:
{
uint8_t v_flb_boxed_518_; lean_object* v_res_519_; 
v_flb_boxed_518_ = lean_unbox(v_flb_512_);
v_res_519_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(v_flb_boxed_518_, v_items_513_, v_w_514_, v_gs_515_, v_toPure_516_, v_k_517_);
lean_dec(v_w_514_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(uint8_t v_flb_520_, lean_object* v_items_521_, lean_object* v_gs_522_, lean_object* v_w_523_, lean_object* v_inst_524_, lean_object* v_inst_525_){
_start:
{
lean_object* v_toApplicative_526_; lean_object* v_toBind_527_; lean_object* v_currColumn_528_; lean_object* v_toPure_529_; lean_object* v___x_530_; lean_object* v___f_531_; lean_object* v___x_532_; 
v_toApplicative_526_ = lean_ctor_get(v_inst_524_, 0);
lean_inc_ref(v_toApplicative_526_);
v_toBind_527_ = lean_ctor_get(v_inst_524_, 1);
lean_inc(v_toBind_527_);
lean_dec_ref(v_inst_524_);
v_currColumn_528_ = lean_ctor_get(v_inst_525_, 2);
lean_inc(v_currColumn_528_);
lean_dec_ref(v_inst_525_);
v_toPure_529_ = lean_ctor_get(v_toApplicative_526_, 1);
lean_inc(v_toPure_529_);
lean_dec_ref(v_toApplicative_526_);
v___x_530_ = lean_box(v_flb_520_);
v___f_531_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_531_, 0, v___x_530_);
lean_closure_set(v___f_531_, 1, v_items_521_);
lean_closure_set(v___f_531_, 2, v_w_523_);
lean_closure_set(v___f_531_, 3, v_gs_522_);
lean_closure_set(v___f_531_, 4, v_toPure_529_);
v___x_532_ = lean_apply_4(v_toBind_527_, lean_box(0), lean_box(0), v_currColumn_528_, v___f_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___boxed(lean_object* v_flb_533_, lean_object* v_items_534_, lean_object* v_gs_535_, lean_object* v_w_536_, lean_object* v_inst_537_, lean_object* v_inst_538_){
_start:
{
uint8_t v_flb_boxed_539_; lean_object* v_res_540_; 
v_flb_boxed_539_ = lean_unbox(v_flb_533_);
v_res_540_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_boxed_539_, v_items_534_, v_gs_535_, v_w_536_, v_inst_537_, v_inst_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(lean_object* v_m_541_, uint8_t v_flb_542_, lean_object* v_items_543_, lean_object* v_gs_544_, lean_object* v_w_545_, lean_object* v_inst_546_, lean_object* v_inst_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_542_, v_items_543_, v_gs_544_, v_w_545_, v_inst_546_, v_inst_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___boxed(lean_object* v_m_549_, lean_object* v_flb_550_, lean_object* v_items_551_, lean_object* v_gs_552_, lean_object* v_w_553_, lean_object* v_inst_554_, lean_object* v_inst_555_){
_start:
{
uint8_t v_flb_boxed_556_; lean_object* v_res_557_; 
v_flb_boxed_556_ = lean_unbox(v_flb_550_);
v_res_557_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(v_m_549_, v_flb_boxed_556_, v_items_551_, v_gs_552_, v_w_553_, v_inst_554_, v_inst_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(lean_object* v_fla_558_, uint8_t v_flb_559_, lean_object* v_tail_560_, lean_object* v_is_x27_561_){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_562_, 0, v_fla_558_);
lean_ctor_set(v___x_562_, 1, v_is_x27_561_);
lean_ctor_set_uint8(v___x_562_, sizeof(void*)*2, v_flb_559_);
v___x_563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v_tail_560_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed(lean_object* v_fla_564_, lean_object* v_flb_565_, lean_object* v_tail_566_, lean_object* v_is_x27_567_){
_start:
{
uint8_t v_flb_1930__boxed_568_; lean_object* v_res_569_; 
v_flb_1930__boxed_568_ = lean_unbox(v_flb_565_);
v_res_569_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_564_, v_flb_1930__boxed_568_, v_tail_566_, v_is_x27_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3(lean_object* v_endTags_570_, lean_object* v_activeTags_571_, lean_object* v_toBind_572_, lean_object* v___f_573_, lean_object* v_____r_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_apply_1(v_endTags_570_, v_activeTags_571_);
v___x_576_ = lean_apply_4(v_toBind_572_, lean_box(0), lean_box(0), v___x_575_, v___f_573_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(lean_object* v_indent_577_, lean_object* v_pushNewline_578_, lean_object* v_toBind_579_, lean_object* v___f_580_, lean_object* v_____r_581_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = l_Int_toNat(v_indent_577_);
v___x_583_ = lean_apply_1(v_pushNewline_578_, v___x_582_);
v___x_584_ = lean_apply_4(v_toBind_579_, lean_box(0), lean_box(0), v___x_583_, v___f_580_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed(lean_object* v_indent_585_, lean_object* v_pushNewline_586_, lean_object* v_toBind_587_, lean_object* v___f_588_, lean_object* v_____r_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(v_indent_585_, v_pushNewline_586_, v_toBind_587_, v___f_588_, v_____r_589_);
lean_dec(v_indent_585_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(lean_object* v_indent_591_, lean_object* v_inst_592_, lean_object* v_toBind_593_, lean_object* v___f_594_, lean_object* v___f_595_, lean_object* v_k_596_){
_start:
{
lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_597_ = lean_nat_to_int(v_k_596_);
v___x_598_ = lean_int_dec_lt(v___x_597_, v_indent_591_);
if (v___x_598_ == 0)
{
lean_object* v_pushNewline_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v___x_597_);
lean_dec(v___f_595_);
v_pushNewline_599_ = lean_ctor_get(v_inst_592_, 1);
lean_inc(v_pushNewline_599_);
lean_dec_ref(v_inst_592_);
v___x_600_ = l_Int_toNat(v_indent_591_);
v___x_601_ = lean_apply_1(v_pushNewline_599_, v___x_600_);
v___x_602_ = lean_apply_4(v_toBind_593_, lean_box(0), lean_box(0), v___x_601_, v___f_594_);
return v___x_602_;
}
else
{
lean_object* v_pushOutput_603_; lean_object* v___x_604_; uint32_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v___f_594_);
v_pushOutput_603_ = lean_ctor_get(v_inst_592_, 0);
lean_inc(v_pushOutput_603_);
lean_dec_ref(v_inst_592_);
v___x_604_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_605_ = 32;
v___x_606_ = lean_int_sub(v_indent_591_, v___x_597_);
lean_dec(v___x_597_);
v___x_607_ = l_Int_toNat(v___x_606_);
lean_dec(v___x_606_);
v___x_608_ = lean_string_pushn(v___x_604_, v___x_605_, v___x_607_);
v___x_609_ = lean_apply_1(v_pushOutput_603_, v___x_608_);
v___x_610_ = lean_apply_4(v_toBind_593_, lean_box(0), lean_box(0), v___x_609_, v___f_595_);
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed(lean_object* v_indent_611_, lean_object* v_inst_612_, lean_object* v_toBind_613_, lean_object* v___f_614_, lean_object* v___f_615_, lean_object* v_k_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(v_indent_611_, v_inst_612_, v_toBind_613_, v___f_614_, v___f_615_, v_k_616_);
lean_dec(v_indent_611_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9(lean_object* v_inst_618_, lean_object* v_activeTags_619_, lean_object* v_toBind_620_, lean_object* v___f_621_, lean_object* v_____r_622_){
_start:
{
lean_object* v_endTags_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_endTags_623_ = lean_ctor_get(v_inst_618_, 4);
lean_inc(v_endTags_623_);
lean_dec_ref(v_inst_618_);
v___x_624_ = lean_apply_1(v_endTags_623_, v_activeTags_619_);
v___x_625_ = lean_apply_4(v_toBind_620_, lean_box(0), lean_box(0), v___x_624_, v___f_621_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1(lean_object* v_gs_x27_626_, lean_object* v_tail_627_, lean_object* v_w_628_, lean_object* v_inst_629_, lean_object* v_inst_630_, lean_object* v_____r_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_apply_1(v_gs_x27_626_, v_tail_627_);
v___x_633_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_628_, v_inst_629_, v_inst_630_, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(uint8_t v_flb_635_, lean_object* v_tail_636_, lean_object* v_tail_637_, lean_object* v_w_638_, lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v_toBind_641_, lean_object* v_____r_642_){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
lean_inc_ref(v_inst_640_);
lean_inc_ref(v_inst_639_);
lean_inc(v_w_638_);
v___x_643_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_635_, v_tail_636_, v_tail_637_, v_w_638_, v_inst_639_, v_inst_640_);
v___x_644_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_644_, 0, v_w_638_);
lean_closure_set(v___x_644_, 1, v_inst_639_);
lean_closure_set(v___x_644_, 2, v_inst_640_);
v___x_645_ = lean_apply_4(v_toBind_641_, lean_box(0), lean_box(0), v___x_643_, v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed(lean_object* v_flb_646_, lean_object* v_tail_647_, lean_object* v_tail_648_, lean_object* v_w_649_, lean_object* v_inst_650_, lean_object* v_inst_651_, lean_object* v_toBind_652_, lean_object* v_____r_653_){
_start:
{
uint8_t v_flb_2022__boxed_654_; lean_object* v_res_655_; 
v_flb_2022__boxed_654_ = lean_unbox(v_flb_646_);
v_res_655_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(v_flb_2022__boxed_654_, v_tail_647_, v_tail_648_, v_w_649_, v_inst_650_, v_inst_651_, v_toBind_652_, v_____r_653_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(lean_object* v_breakHere_657_, lean_object* v_w_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_endTags_661_, lean_object* v_activeTags_662_, lean_object* v_toBind_663_, lean_object* v_pushOutput_664_, lean_object* v___x_665_, lean_object* v_____x_666_){
_start:
{
if (lean_obj_tag(v_____x_666_) == 1)
{
lean_object* v_head_667_; lean_object* v_fla_668_; uint8_t v___x_669_; 
v_head_667_ = lean_ctor_get(v_____x_666_, 0);
v_fla_668_ = lean_ctor_get(v_head_667_, 0);
v___x_669_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_668_);
if (v___x_669_ == 0)
{
lean_dec_ref_known(v_____x_666_, 2);
lean_dec_ref(v___x_665_);
lean_dec(v_pushOutput_664_);
lean_dec(v_toBind_663_);
lean_dec(v_activeTags_662_);
lean_dec(v_endTags_661_);
lean_dec_ref(v_inst_660_);
lean_dec_ref(v_inst_659_);
lean_dec(v_w_658_);
lean_inc(v_breakHere_657_);
return v_breakHere_657_;
}
else
{
lean_object* v___f_670_; lean_object* v___f_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___f_670_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4), 5, 4);
lean_closure_set(v___f_670_, 0, v_w_658_);
lean_closure_set(v___f_670_, 1, v_inst_659_);
lean_closure_set(v___f_670_, 2, v_inst_660_);
lean_closure_set(v___f_670_, 3, v_____x_666_);
lean_inc(v_toBind_663_);
v___f_671_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_671_, 0, v_endTags_661_);
lean_closure_set(v___f_671_, 1, v_activeTags_662_);
lean_closure_set(v___f_671_, 2, v_toBind_663_);
lean_closure_set(v___f_671_, 3, v___f_670_);
v___x_672_ = lean_apply_1(v_pushOutput_664_, v___x_665_);
v___x_673_ = lean_apply_4(v_toBind_663_, lean_box(0), lean_box(0), v___x_672_, v___f_671_);
return v___x_673_;
}
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec(v_____x_666_);
lean_dec_ref(v___x_665_);
lean_dec(v_pushOutput_664_);
lean_dec(v_toBind_663_);
lean_dec(v_activeTags_662_);
lean_dec(v_endTags_661_);
lean_dec_ref(v_inst_660_);
lean_dec(v_w_658_);
v___x_674_ = lean_box(0);
v___x_675_ = l_instInhabitedOfMonad___redArg(v_inst_659_, v___x_674_);
v___x_676_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0));
v___x_677_ = l_panic___redArg(v___x_675_, v___x_676_);
lean_dec(v___x_675_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed(lean_object* v_breakHere_678_, lean_object* v_w_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_endTags_682_, lean_object* v_activeTags_683_, lean_object* v_toBind_684_, lean_object* v_pushOutput_685_, lean_object* v___x_686_, lean_object* v_____x_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(v_breakHere_678_, v_w_679_, v_inst_680_, v_inst_681_, v_endTags_682_, v_activeTags_683_, v_toBind_684_, v_pushOutput_685_, v___x_686_, v_____x_687_);
lean_dec(v_breakHere_678_);
return v_res_688_;
}
}
static lean_object* _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_690_ = lean_string_length(v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(lean_object* v_a_691_, lean_object* v_p_692_, lean_object* v___x_693_, lean_object* v_indent_694_, lean_object* v_activeTags_695_, lean_object* v_tail_696_, lean_object* v_fla_697_, uint8_t v_flb_698_, lean_object* v_tail_699_, lean_object* v_w_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_toBind_703_, lean_object* v_gs_x27_704_, lean_object* v_____r_705_){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v_is_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_706_ = lean_string_utf8_next(v_a_691_, v_p_692_);
v___x_707_ = lean_string_utf8_extract(v_a_691_, v___x_706_, v___x_693_);
lean_dec(v___x_706_);
v___x_708_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
v___x_709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v_indent_694_);
lean_ctor_set(v___x_709_, 2, v_activeTags_695_);
v_is_710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_is_710_, 0, v___x_709_);
lean_ctor_set(v_is_710_, 1, v_tail_696_);
v___x_711_ = lean_box(1);
v___x_712_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_697_, v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec_ref(v_gs_x27_704_);
lean_inc_ref(v_inst_702_);
lean_inc_ref(v_inst_701_);
lean_inc(v_w_700_);
v___x_713_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_698_, v_is_710_, v_tail_699_, v_w_700_, v_inst_701_, v_inst_702_);
v___x_714_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_714_, 0, v_w_700_);
lean_closure_set(v___x_714_, 1, v_inst_701_);
lean_closure_set(v___x_714_, 2, v_inst_702_);
v___x_715_ = lean_apply_4(v_toBind_703_, lean_box(0), lean_box(0), v___x_713_, v___x_714_);
return v___x_715_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec(v_toBind_703_);
lean_dec(v_tail_699_);
v___x_716_ = lean_apply_1(v_gs_x27_704_, v_is_710_);
v___x_717_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_700_, v_inst_701_, v_inst_702_, v___x_716_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed(lean_object* v_a_718_, lean_object* v_p_719_, lean_object* v___x_720_, lean_object* v_indent_721_, lean_object* v_activeTags_722_, lean_object* v_tail_723_, lean_object* v_fla_724_, lean_object* v_flb_725_, lean_object* v_tail_726_, lean_object* v_w_727_, lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_toBind_730_, lean_object* v_gs_x27_731_, lean_object* v_____r_732_){
_start:
{
uint8_t v_flb_2046__boxed_733_; lean_object* v_res_734_; 
v_flb_2046__boxed_733_ = lean_unbox(v_flb_725_);
v_res_734_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(v_a_718_, v_p_719_, v___x_720_, v_indent_721_, v_activeTags_722_, v_tail_723_, v_fla_724_, v_flb_2046__boxed_733_, v_tail_726_, v_w_727_, v_inst_728_, v_inst_729_, v_toBind_730_, v_gs_x27_731_, v_____r_732_);
lean_dec(v_fla_724_);
lean_dec(v___x_720_);
lean_dec(v_p_719_);
lean_dec_ref(v_a_718_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(lean_object* v_activeTags_735_, lean_object* v_a_736_, lean_object* v_indent_737_, lean_object* v_tail_738_, lean_object* v_gs_x27_739_, lean_object* v_w_740_, lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_____r_743_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = lean_nat_add(v_activeTags_735_, v___x_744_);
v___x_746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_746_, 0, v_a_736_);
lean_ctor_set(v___x_746_, 1, v_indent_737_);
lean_ctor_set(v___x_746_, 2, v___x_745_);
v___x_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v_tail_738_);
v___x_748_ = lean_apply_1(v_gs_x27_739_, v___x_747_);
v___x_749_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_740_, v_inst_741_, v_inst_742_, v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed(lean_object* v_activeTags_750_, lean_object* v_a_751_, lean_object* v_indent_752_, lean_object* v_tail_753_, lean_object* v_gs_x27_754_, lean_object* v_w_755_, lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_____r_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(v_activeTags_750_, v_a_751_, v_indent_752_, v_tail_753_, v_gs_x27_754_, v_w_755_, v_inst_756_, v_inst_757_, v_____r_758_);
lean_dec(v_activeTags_750_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(lean_object* v_w_760_, lean_object* v_inst_761_, lean_object* v_inst_762_, lean_object* v_x_763_){
_start:
{
if (lean_obj_tag(v_x_763_) == 0)
{
lean_object* v_toApplicative_764_; lean_object* v_toPure_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v_toApplicative_764_ = lean_ctor_get(v_inst_761_, 0);
lean_inc_ref(v_toApplicative_764_);
lean_dec_ref(v_inst_762_);
lean_dec_ref(v_inst_761_);
lean_dec(v_w_760_);
v_toPure_765_ = lean_ctor_get(v_toApplicative_764_, 1);
lean_inc(v_toPure_765_);
lean_dec_ref(v_toApplicative_764_);
v___x_766_ = lean_box(0);
v___x_767_ = lean_apply_2(v_toPure_765_, lean_box(0), v___x_766_);
return v___x_767_;
}
else
{
lean_object* v_head_768_; lean_object* v_items_769_; 
v_head_768_ = lean_ctor_get(v_x_763_, 0);
v_items_769_ = lean_ctor_get(v_head_768_, 1);
lean_inc(v_items_769_);
if (lean_obj_tag(v_items_769_) == 0)
{
lean_object* v_tail_770_; 
v_tail_770_ = lean_ctor_get(v_x_763_, 1);
lean_inc(v_tail_770_);
lean_dec_ref_known(v_x_763_, 2);
v_x_763_ = v_tail_770_;
goto _start;
}
else
{
lean_object* v_head_772_; lean_object* v_toBind_773_; lean_object* v_tail_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_917_; 
lean_inc(v_head_768_);
v_head_772_ = lean_ctor_get(v_items_769_, 0);
lean_inc(v_head_772_);
v_toBind_773_ = lean_ctor_get(v_inst_761_, 1);
v_tail_774_ = lean_ctor_get(v_x_763_, 1);
v_isSharedCheck_917_ = !lean_is_exclusive(v_x_763_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; 
v_unused_918_ = lean_ctor_get(v_x_763_, 0);
lean_dec(v_unused_918_);
v___x_776_ = v_x_763_;
v_isShared_777_ = v_isSharedCheck_917_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_tail_774_);
lean_dec(v_x_763_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_917_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v_fla_778_; uint8_t v_flb_779_; lean_object* v_tail_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_915_; 
v_fla_778_ = lean_ctor_get(v_head_768_, 0);
lean_inc(v_fla_778_);
v_flb_779_ = lean_ctor_get_uint8(v_head_768_, sizeof(void*)*2);
lean_dec(v_head_768_);
v_tail_780_ = lean_ctor_get(v_items_769_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v_items_769_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; 
v_unused_916_ = lean_ctor_get(v_items_769_, 0);
lean_dec(v_unused_916_);
v___x_782_ = v_items_769_;
v_isShared_783_ = v_isSharedCheck_915_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_tail_780_);
lean_dec(v_items_769_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_915_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v_f_784_; lean_object* v_indent_785_; lean_object* v_activeTags_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_914_; 
v_f_784_ = lean_ctor_get(v_head_772_, 0);
v_indent_785_ = lean_ctor_get(v_head_772_, 1);
v_activeTags_786_ = lean_ctor_get(v_head_772_, 2);
v_isSharedCheck_914_ = !lean_is_exclusive(v_head_772_);
if (v_isSharedCheck_914_ == 0)
{
v___x_788_ = v_head_772_;
v_isShared_789_ = v_isSharedCheck_914_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_activeTags_786_);
lean_inc(v_indent_785_);
lean_inc(v_f_784_);
lean_dec(v_head_772_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_914_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v_gs_x27_791_; 
v___x_790_ = lean_box(v_flb_779_);
lean_inc(v_tail_774_);
lean_inc(v_fla_778_);
v_gs_x27_791_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v_gs_x27_791_, 0, v_fla_778_);
lean_closure_set(v_gs_x27_791_, 1, v___x_790_);
lean_closure_set(v_gs_x27_791_, 2, v_tail_774_);
switch(lean_obj_tag(v_f_784_))
{
case 0:
{
lean_object* v_endTags_792_; lean_object* v___f_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_inc(v_toBind_773_);
lean_del_object(v___x_788_);
lean_dec(v_indent_785_);
lean_del_object(v___x_782_);
lean_dec(v_fla_778_);
lean_del_object(v___x_776_);
lean_dec(v_tail_774_);
v_endTags_792_ = lean_ctor_get(v_inst_762_, 4);
lean_inc(v_endTags_792_);
v___f_793_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_793_, 0, v_gs_x27_791_);
lean_closure_set(v___f_793_, 1, v_tail_780_);
lean_closure_set(v___f_793_, 2, v_w_760_);
lean_closure_set(v___f_793_, 3, v_inst_761_);
lean_closure_set(v___f_793_, 4, v_inst_762_);
v___x_794_ = lean_apply_1(v_endTags_792_, v_activeTags_786_);
v___x_795_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v___x_794_, v___f_793_);
return v___x_795_;
}
case 1:
{
lean_inc(v_toBind_773_);
lean_del_object(v___x_788_);
lean_del_object(v___x_782_);
lean_del_object(v___x_776_);
if (v_flb_779_ == 0)
{
uint8_t v___x_796_; 
lean_dec(v_tail_774_);
v___x_796_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_778_);
lean_dec(v_fla_778_);
if (v___x_796_ == 0)
{
lean_object* v_pushNewline_797_; lean_object* v_endTags_798_; lean_object* v___f_799_; lean_object* v___f_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_pushNewline_797_ = lean_ctor_get(v_inst_762_, 1);
lean_inc(v_pushNewline_797_);
v_endTags_798_ = lean_ctor_get(v_inst_762_, 4);
lean_inc(v_endTags_798_);
v___f_799_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_799_, 0, v_gs_x27_791_);
lean_closure_set(v___f_799_, 1, v_tail_780_);
lean_closure_set(v___f_799_, 2, v_w_760_);
lean_closure_set(v___f_799_, 3, v_inst_761_);
lean_closure_set(v___f_799_, 4, v_inst_762_);
lean_inc(v_toBind_773_);
v___f_800_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_800_, 0, v_endTags_798_);
lean_closure_set(v___f_800_, 1, v_activeTags_786_);
lean_closure_set(v___f_800_, 2, v_toBind_773_);
lean_closure_set(v___f_800_, 3, v___f_799_);
v___x_801_ = l_Int_toNat(v_indent_785_);
lean_dec(v_indent_785_);
v___x_802_ = lean_apply_1(v_pushNewline_797_, v___x_801_);
v___x_803_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v___x_802_, v___f_800_);
return v___x_803_;
}
else
{
lean_object* v_pushOutput_804_; lean_object* v_endTags_805_; lean_object* v___f_806_; lean_object* v___f_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec(v_indent_785_);
v_pushOutput_804_ = lean_ctor_get(v_inst_762_, 0);
lean_inc(v_pushOutput_804_);
v_endTags_805_ = lean_ctor_get(v_inst_762_, 4);
lean_inc(v_endTags_805_);
v___f_806_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_806_, 0, v_gs_x27_791_);
lean_closure_set(v___f_806_, 1, v_tail_780_);
lean_closure_set(v___f_806_, 2, v_w_760_);
lean_closure_set(v___f_806_, 3, v_inst_761_);
lean_closure_set(v___f_806_, 4, v_inst_762_);
lean_inc(v_toBind_773_);
v___f_807_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_807_, 0, v_endTags_805_);
lean_closure_set(v___f_807_, 1, v_activeTags_786_);
lean_closure_set(v___f_807_, 2, v_toBind_773_);
lean_closure_set(v___f_807_, 3, v___f_806_);
v___x_808_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_809_ = lean_apply_1(v_pushOutput_804_, v___x_808_);
v___x_810_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v___x_809_, v___f_807_);
return v___x_810_;
}
}
else
{
lean_object* v_pushOutput_811_; lean_object* v_pushNewline_812_; lean_object* v_endTags_813_; lean_object* v___x_814_; lean_object* v___f_815_; lean_object* v___f_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v_breakHere_819_; uint8_t v___x_820_; 
lean_dec_ref(v_gs_x27_791_);
v_pushOutput_811_ = lean_ctor_get(v_inst_762_, 0);
v_pushNewline_812_ = lean_ctor_get(v_inst_762_, 1);
v_endTags_813_ = lean_ctor_get(v_inst_762_, 4);
v___x_814_ = lean_box(v_flb_779_);
lean_inc_n(v_toBind_773_, 3);
lean_inc_ref(v_inst_762_);
lean_inc_ref(v_inst_761_);
lean_inc(v_w_760_);
lean_inc(v_tail_774_);
lean_inc(v_tail_780_);
v___f_815_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_815_, 0, v___x_814_);
lean_closure_set(v___f_815_, 1, v_tail_780_);
lean_closure_set(v___f_815_, 2, v_tail_774_);
lean_closure_set(v___f_815_, 3, v_w_760_);
lean_closure_set(v___f_815_, 4, v_inst_761_);
lean_closure_set(v___f_815_, 5, v_inst_762_);
lean_closure_set(v___f_815_, 6, v_toBind_773_);
lean_inc(v_activeTags_786_);
lean_inc(v_endTags_813_);
v___f_816_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_816_, 0, v_endTags_813_);
lean_closure_set(v___f_816_, 1, v_activeTags_786_);
lean_closure_set(v___f_816_, 2, v_toBind_773_);
lean_closure_set(v___f_816_, 3, v___f_815_);
v___x_817_ = l_Int_toNat(v_indent_785_);
lean_dec(v_indent_785_);
lean_inc(v_pushNewline_812_);
v___x_818_ = lean_apply_1(v_pushNewline_812_, v___x_817_);
v_breakHere_819_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v___x_818_, v___f_816_);
v___x_820_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_778_);
lean_dec(v_fla_778_);
if (v___x_820_ == 0)
{
lean_dec(v_activeTags_786_);
lean_dec(v_tail_780_);
lean_dec(v_tail_774_);
lean_dec(v_toBind_773_);
lean_dec_ref(v_inst_762_);
lean_dec_ref(v_inst_761_);
lean_dec(v_w_760_);
return v_breakHere_819_;
}
else
{
lean_object* v___x_821_; lean_object* v___f_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_821_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
lean_inc(v_pushOutput_811_);
lean_inc(v_toBind_773_);
lean_inc(v_endTags_813_);
lean_inc_ref(v_inst_762_);
lean_inc_ref(v_inst_761_);
lean_inc(v_w_760_);
v___f_822_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_822_, 0, v_breakHere_819_);
lean_closure_set(v___f_822_, 1, v_w_760_);
lean_closure_set(v___f_822_, 2, v_inst_761_);
lean_closure_set(v___f_822_, 3, v_inst_762_);
lean_closure_set(v___f_822_, 4, v_endTags_813_);
lean_closure_set(v___f_822_, 5, v_activeTags_786_);
lean_closure_set(v___f_822_, 6, v_toBind_773_);
lean_closure_set(v___f_822_, 7, v_pushOutput_811_);
lean_closure_set(v___f_822_, 8, v___x_821_);
v___x_823_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_824_ = lean_nat_sub(v_w_760_, v___x_823_);
lean_dec(v_w_760_);
v___x_825_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_779_, v_tail_780_, v_tail_774_, v___x_824_, v_inst_761_, v_inst_762_);
v___x_826_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v___x_825_, v___f_822_);
return v___x_826_;
}
}
}
case 2:
{
uint8_t v_force_827_; lean_object* v___f_828_; lean_object* v___f_829_; lean_object* v___f_830_; uint8_t v___y_832_; uint8_t v___x_838_; 
lean_inc_n(v_toBind_773_, 3);
lean_del_object(v___x_788_);
lean_del_object(v___x_782_);
lean_del_object(v___x_776_);
lean_dec(v_tail_774_);
v_force_827_ = lean_ctor_get_uint8(v_f_784_, 0);
lean_dec_ref_known(v_f_784_, 0);
lean_inc_ref_n(v_inst_762_, 3);
v___f_828_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_828_, 0, v_gs_x27_791_);
lean_closure_set(v___f_828_, 1, v_tail_780_);
lean_closure_set(v___f_828_, 2, v_w_760_);
lean_closure_set(v___f_828_, 3, v_inst_761_);
lean_closure_set(v___f_828_, 4, v_inst_762_);
lean_inc_ref(v___f_828_);
lean_inc(v_activeTags_786_);
v___f_829_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9), 5, 4);
lean_closure_set(v___f_829_, 0, v_inst_762_);
lean_closure_set(v___f_829_, 1, v_activeTags_786_);
lean_closure_set(v___f_829_, 2, v_toBind_773_);
lean_closure_set(v___f_829_, 3, v___f_828_);
lean_inc_ref(v___f_829_);
v___f_830_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_830_, 0, v_indent_785_);
lean_closure_set(v___f_830_, 1, v_inst_762_);
lean_closure_set(v___f_830_, 2, v_toBind_773_);
lean_closure_set(v___f_830_, 3, v___f_829_);
lean_closure_set(v___f_830_, 4, v___f_829_);
v___x_838_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_778_);
lean_dec(v_fla_778_);
if (v___x_838_ == 0)
{
v___y_832_ = v___x_838_;
goto v___jp_831_;
}
else
{
uint8_t v___x_839_; 
v___x_839_ = lean_bool_not(v_force_827_);
v___y_832_ = v___x_839_;
goto v___jp_831_;
}
v___jp_831_:
{
if (v___y_832_ == 0)
{
lean_object* v_currColumn_833_; lean_object* v___x_834_; 
lean_dec_ref(v___f_828_);
lean_dec(v_activeTags_786_);
v_currColumn_833_ = lean_ctor_get(v_inst_762_, 2);
lean_inc(v_currColumn_833_);
lean_dec_ref(v_inst_762_);
v___x_834_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v_currColumn_833_, v___f_830_);
return v___x_834_;
}
else
{
lean_object* v_endTags_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec_ref(v___f_830_);
v_endTags_835_ = lean_ctor_get(v_inst_762_, 4);
lean_inc(v_endTags_835_);
lean_dec_ref(v_inst_762_);
v___x_836_ = lean_apply_1(v_endTags_835_, v_activeTags_786_);
v___x_837_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v___x_836_, v___f_828_);
return v___x_837_;
}
}
}
case 3:
{
lean_object* v_a_840_; uint32_t v___x_841_; lean_object* v_p_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
lean_inc(v_toBind_773_);
lean_del_object(v___x_788_);
lean_del_object(v___x_782_);
lean_del_object(v___x_776_);
v_a_840_ = lean_ctor_get(v_f_784_, 0);
lean_inc_ref_n(v_a_840_, 2);
lean_dec_ref_known(v_f_784_, 1);
v___x_841_ = 10;
v_p_842_ = lean_string_posof(v_a_840_, v___x_841_);
v___x_843_ = lean_string_utf8_byte_size(v_a_840_);
v___x_844_ = lean_nat_dec_eq(v_p_842_, v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v_pushOutput_845_; lean_object* v_pushNewline_846_; lean_object* v___x_847_; lean_object* v___f_848_; lean_object* v___f_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_pushOutput_845_ = lean_ctor_get(v_inst_762_, 0);
lean_inc(v_pushOutput_845_);
v_pushNewline_846_ = lean_ctor_get(v_inst_762_, 1);
lean_inc(v_pushNewline_846_);
v___x_847_ = lean_box(v_flb_779_);
lean_inc_n(v_toBind_773_, 2);
lean_inc(v_indent_785_);
lean_inc(v_p_842_);
lean_inc_ref(v_a_840_);
v___f_848_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed), 15, 14);
lean_closure_set(v___f_848_, 0, v_a_840_);
lean_closure_set(v___f_848_, 1, v_p_842_);
lean_closure_set(v___f_848_, 2, v___x_843_);
lean_closure_set(v___f_848_, 3, v_indent_785_);
lean_closure_set(v___f_848_, 4, v_activeTags_786_);
lean_closure_set(v___f_848_, 5, v_tail_780_);
lean_closure_set(v___f_848_, 6, v_fla_778_);
lean_closure_set(v___f_848_, 7, v___x_847_);
lean_closure_set(v___f_848_, 8, v_tail_774_);
lean_closure_set(v___f_848_, 9, v_w_760_);
lean_closure_set(v___f_848_, 10, v_inst_761_);
lean_closure_set(v___f_848_, 11, v_inst_762_);
lean_closure_set(v___f_848_, 12, v_toBind_773_);
lean_closure_set(v___f_848_, 13, v_gs_x27_791_);
v___f_849_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_849_, 0, v_indent_785_);
lean_closure_set(v___f_849_, 1, v_pushNewline_846_);
lean_closure_set(v___f_849_, 2, v_toBind_773_);
lean_closure_set(v___f_849_, 3, v___f_848_);
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = lean_string_utf8_extract(v_a_840_, v___x_850_, v_p_842_);
lean_dec(v_p_842_);
lean_dec_ref(v_a_840_);
v___x_852_ = lean_apply_1(v_pushOutput_845_, v___x_851_);
v___x_853_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v___x_852_, v___f_849_);
return v___x_853_;
}
else
{
lean_object* v_pushOutput_854_; lean_object* v_endTags_855_; lean_object* v___f_856_; lean_object* v___f_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec(v_p_842_);
lean_dec(v_indent_785_);
lean_dec(v_fla_778_);
lean_dec(v_tail_774_);
v_pushOutput_854_ = lean_ctor_get(v_inst_762_, 0);
lean_inc(v_pushOutput_854_);
v_endTags_855_ = lean_ctor_get(v_inst_762_, 4);
lean_inc(v_endTags_855_);
v___f_856_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_856_, 0, v_gs_x27_791_);
lean_closure_set(v___f_856_, 1, v_tail_780_);
lean_closure_set(v___f_856_, 2, v_w_760_);
lean_closure_set(v___f_856_, 3, v_inst_761_);
lean_closure_set(v___f_856_, 4, v_inst_762_);
lean_inc(v_toBind_773_);
v___f_857_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_857_, 0, v_endTags_855_);
lean_closure_set(v___f_857_, 1, v_activeTags_786_);
lean_closure_set(v___f_857_, 2, v_toBind_773_);
lean_closure_set(v___f_857_, 3, v___f_856_);
v___x_858_ = lean_apply_1(v_pushOutput_854_, v_a_840_);
v___x_859_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v___x_858_, v___f_857_);
return v___x_859_;
}
}
case 4:
{
lean_object* v_indent_860_; lean_object* v_f_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
lean_dec_ref(v_gs_x27_791_);
lean_del_object(v___x_776_);
v_indent_860_ = lean_ctor_get(v_f_784_, 0);
lean_inc(v_indent_860_);
v_f_861_ = lean_ctor_get(v_f_784_, 1);
lean_inc(v_f_861_);
lean_dec_ref_known(v_f_784_, 2);
v___x_862_ = lean_int_add(v_indent_785_, v_indent_860_);
lean_dec(v_indent_860_);
lean_dec(v_indent_785_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v___x_862_);
lean_ctor_set(v___x_788_, 0, v_f_861_);
v___x_864_ = v___x_788_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_f_861_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_activeTags_786_);
v___x_864_ = v_reuseFailAlloc_870_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_866_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_864_);
v___x_866_ = v___x_782_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_tail_780_);
v___x_866_ = v_reuseFailAlloc_869_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_867_; 
v___x_867_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_778_, v_flb_779_, v_tail_774_, v___x_866_);
v_x_763_ = v___x_867_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_871_; lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
lean_dec_ref(v_gs_x27_791_);
v_a_871_ = lean_ctor_get(v_f_784_, 0);
lean_inc(v_a_871_);
v_a_872_ = lean_ctor_get(v_f_784_, 1);
lean_inc(v_a_872_);
lean_dec_ref_known(v_f_784_, 2);
v___x_873_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_785_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 2, v___x_873_);
lean_ctor_set(v___x_788_, 0, v_a_871_);
v___x_875_ = v___x_788_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_871_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_indent_785_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v___x_873_);
v___x_875_ = v_reuseFailAlloc_885_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_876_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_876_, 0, v_a_872_);
lean_ctor_set(v___x_876_, 1, v_indent_785_);
lean_ctor_set(v___x_876_, 2, v_activeTags_786_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_876_);
v___x_878_ = v___x_782_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_tail_780_);
v___x_878_ = v_reuseFailAlloc_884_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v___x_878_);
lean_ctor_set(v___x_776_, 0, v___x_875_);
v___x_880_ = v___x_776_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v___x_878_);
v___x_880_ = v_reuseFailAlloc_883_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; 
v___x_881_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_778_, v_flb_779_, v_tail_774_, v___x_880_);
v_x_763_ = v___x_881_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_886_; uint8_t v_behavior_887_; uint8_t v___x_888_; 
lean_dec_ref(v_gs_x27_791_);
lean_del_object(v___x_776_);
v_a_886_ = lean_ctor_get(v_f_784_, 0);
lean_inc(v_a_886_);
v_behavior_887_ = lean_ctor_get_uint8(v_f_784_, sizeof(void*)*1);
lean_dec_ref_known(v_f_784_, 1);
v___x_888_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_778_);
if (v___x_888_ == 0)
{
lean_object* v___x_890_; 
lean_inc(v_toBind_773_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v_a_886_);
v___x_890_ = v___x_788_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_886_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_indent_785_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_activeTags_786_);
v___x_890_ = v_reuseFailAlloc_899_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_891_ = lean_box(0);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v___x_891_);
lean_ctor_set(v___x_782_, 0, v___x_890_);
v___x_893_ = v___x_782_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v___x_891_);
v___x_893_ = v_reuseFailAlloc_898_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_894_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_778_, v_flb_779_, v_tail_774_, v_tail_780_);
lean_inc_ref(v_inst_762_);
lean_inc_ref(v_inst_761_);
lean_inc(v_w_760_);
v___x_895_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_behavior_887_, v___x_893_, v___x_894_, v_w_760_, v_inst_761_, v_inst_762_);
v___x_896_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_896_, 0, v_w_760_);
lean_closure_set(v___x_896_, 1, v_inst_761_);
lean_closure_set(v___x_896_, 2, v_inst_762_);
v___x_897_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v___x_895_, v___x_896_);
return v___x_897_;
}
}
}
else
{
lean_object* v___x_901_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v_a_886_);
v___x_901_ = v___x_788_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_886_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_indent_785_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_activeTags_786_);
v___x_901_ = v_reuseFailAlloc_907_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_903_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_901_);
v___x_903_ = v___x_782_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_901_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_tail_780_);
v___x_903_ = v_reuseFailAlloc_906_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; 
v___x_904_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_778_, v_flb_779_, v_tail_774_, v___x_903_);
v_x_763_ = v___x_904_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_908_; lean_object* v_a_909_; lean_object* v_startTag_910_; lean_object* v___f_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_inc(v_toBind_773_);
lean_del_object(v___x_788_);
lean_del_object(v___x_782_);
lean_dec(v_fla_778_);
lean_del_object(v___x_776_);
lean_dec(v_tail_774_);
v_a_908_ = lean_ctor_get(v_f_784_, 0);
lean_inc(v_a_908_);
v_a_909_ = lean_ctor_get(v_f_784_, 1);
lean_inc(v_a_909_);
lean_dec_ref_known(v_f_784_, 2);
v_startTag_910_ = lean_ctor_get(v_inst_762_, 3);
lean_inc(v_startTag_910_);
v___f_911_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed), 9, 8);
lean_closure_set(v___f_911_, 0, v_activeTags_786_);
lean_closure_set(v___f_911_, 1, v_a_909_);
lean_closure_set(v___f_911_, 2, v_indent_785_);
lean_closure_set(v___f_911_, 3, v_tail_780_);
lean_closure_set(v___f_911_, 4, v_gs_x27_791_);
lean_closure_set(v___f_911_, 5, v_w_760_);
lean_closure_set(v___f_911_, 6, v_inst_761_);
lean_closure_set(v___f_911_, 7, v_inst_762_);
v___x_912_ = lean_apply_1(v_startTag_910_, v_a_908_);
v___x_913_ = lean_apply_4(v_toBind_773_, lean_box(0), lean_box(0), v___x_912_, v___f_911_);
return v___x_913_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4(lean_object* v_w_919_, lean_object* v_inst_920_, lean_object* v_inst_921_, lean_object* v_____x_922_, lean_object* v_____r_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_919_, v_inst_920_, v_inst_921_, v_____x_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be(lean_object* v_m_925_, lean_object* v_w_926_, lean_object* v_inst_927_, lean_object* v_inst_928_, lean_object* v_x_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_926_, v_inst_927_, v_inst_928_, v_x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___redArg(lean_object* v_f_931_, lean_object* v_w_932_, lean_object* v_indent_933_, lean_object* v_inst_934_, lean_object* v_inst_935_){
_start:
{
lean_object* v___x_936_; uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_936_ = lean_box(1);
v___x_937_ = 0;
v___x_938_ = lean_nat_to_int(v_indent_933_);
v___x_939_ = lean_unsigned_to_nat(0u);
v___x_940_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_940_, 0, v_f_931_);
lean_ctor_set(v___x_940_, 1, v___x_938_);
lean_ctor_set(v___x_940_, 2, v___x_939_);
v___x_941_ = lean_box(0);
v___x_942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_943_, 0, v___x_936_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
lean_ctor_set_uint8(v___x_943_, sizeof(void*)*2, v___x_937_);
v___x_944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___x_941_);
v___x_945_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_932_, v_inst_934_, v_inst_935_, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM(lean_object* v_m_946_, lean_object* v_f_947_, lean_object* v_w_948_, lean_object* v_indent_949_, lean_object* v_inst_950_, lean_object* v_inst_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Std_Format_prettyM___redArg(v_f_947_, v_w_948_, v_indent_949_, v_inst_950_, v_inst_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_bracket(lean_object* v_l_953_, lean_object* v_f_954_, lean_object* v_r_955_){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; lean_object* v___x_964_; 
v___x_956_ = lean_string_length(v_l_953_);
v___x_957_ = lean_nat_to_int(v___x_956_);
v___x_958_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_958_, 0, v_l_953_);
v___x_959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set(v___x_959_, 1, v_f_954_);
v___x_960_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_960_, 0, v_r_955_);
v___x_961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_957_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = 0;
v___x_964_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*1, v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l_Std_Format_paren___closed__2(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_Std_Format_paren___closed__0));
v___x_968_ = lean_string_length(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l_Std_Format_paren___closed__3(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = lean_obj_once(&l_Std_Format_paren___closed__2, &l_Std_Format_paren___closed__2_once, _init_l_Std_Format_paren___closed__2);
v___x_970_ = lean_nat_to_int(v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_paren(lean_object* v_f_975_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; lean_object* v___x_983_; 
v___x_976_ = lean_obj_once(&l_Std_Format_paren___closed__3, &l_Std_Format_paren___closed__3_once, _init_l_Std_Format_paren___closed__3);
v___x_977_ = ((lean_object*)(l_Std_Format_paren___closed__4));
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v_f_975_);
v___x_979_ = ((lean_object*)(l_Std_Format_paren___closed__5));
v___x_980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_976_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = 0;
v___x_983_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*1, v___x_982_);
return v___x_983_;
}
}
static lean_object* _init_l_Std_Format_sbracket___closed__2(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l_Std_Format_sbracket___closed__0));
v___x_987_ = lean_string_length(v___x_986_);
return v___x_987_;
}
}
static lean_object* _init_l_Std_Format_sbracket___closed__3(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_obj_once(&l_Std_Format_sbracket___closed__2, &l_Std_Format_sbracket___closed__2_once, _init_l_Std_Format_sbracket___closed__2);
v___x_989_ = lean_nat_to_int(v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_sbracket(lean_object* v_f_994_){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; lean_object* v___x_1002_; 
v___x_995_ = lean_obj_once(&l_Std_Format_sbracket___closed__3, &l_Std_Format_sbracket___closed__3_once, _init_l_Std_Format_sbracket___closed__3);
v___x_996_ = ((lean_object*)(l_Std_Format_sbracket___closed__4));
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v_f_994_);
v___x_998_ = ((lean_object*)(l_Std_Format_sbracket___closed__5));
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_995_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = 0;
v___x_1002_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*1, v___x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_bracketFill(lean_object* v_l_1003_, lean_object* v_f_1004_, lean_object* v_r_1005_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1006_ = lean_string_length(v_l_1003_);
v___x_1007_ = lean_nat_to_int(v___x_1006_);
v___x_1008_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1008_, 0, v_l_1003_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v_f_1004_);
v___x_1010_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1010_, 0, v_r_1005_);
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1007_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Std_Format_fill(v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_Std_Format_defIndent(void){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_unsigned_to_nat(2u);
return v___x_1014_;
}
}
static uint8_t _init_l_Std_Format_defUnicode(void){
_start:
{
uint8_t v___x_1015_; 
v___x_1015_ = 1;
return v___x_1015_;
}
}
static lean_object* _init_l_Std_Format_defWidth(void){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_unsigned_to_nat(120u);
return v___x_1016_;
}
}
static lean_object* _init_l_Std_Format_nestD___closed__0(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_unsigned_to_nat(2u);
v___x_1018_ = lean_nat_to_int(v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nestD(lean_object* v_f_1019_){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_obj_once(&l_Std_Format_nestD___closed__0, &l_Std_Format_nestD___closed__0_once, _init_l_Std_Format_nestD___closed__0);
v___x_1021_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v_f_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_indentD(lean_object* v_f_1022_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = lean_box(1);
v___x_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v_f_1022_);
v___x_1025_ = l_Std_Format_nestD(v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(lean_object* v_s_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_out_1028_; lean_object* v_column_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1041_; 
v_out_1028_ = lean_ctor_get(v___y_1027_, 0);
v_column_1029_ = lean_ctor_get(v___y_1027_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___y_1027_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1031_ = v___y_1027_;
v_isShared_1032_ = v_isSharedCheck_1041_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_column_1029_);
lean_inc(v_out_1028_);
lean_dec(v___y_1027_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1041_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1033_ = lean_box(0);
v___x_1034_ = lean_string_append(v_out_1028_, v_s_1026_);
v___x_1035_ = lean_string_length(v_s_1026_);
v___x_1036_ = lean_nat_add(v_column_1029_, v___x_1035_);
lean_dec(v___x_1035_);
lean_dec(v_column_1029_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 1, v___x_1036_);
lean_ctor_set(v___x_1031_, 0, v___x_1034_);
v___x_1038_ = v___x_1031_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1033_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
return v___x_1039_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0___boxed(lean_object* v_s_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(v_s_1042_, v___y_1043_);
lean_dec_ref(v_s_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1(lean_object* v_indent_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_out_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1061_; 
v_out_1048_ = lean_ctor_get(v___y_1047_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___y_1047_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; 
v_unused_1062_ = lean_ctor_get(v___y_1047_, 1);
lean_dec(v_unused_1062_);
v___x_1050_ = v___y_1047_;
v_isShared_1051_ = v_isSharedCheck_1061_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_out_1048_);
lean_dec(v___y_1047_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1061_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; uint32_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1052_ = lean_box(0);
v___x_1053_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1054_ = 32;
lean_inc(v_indent_1046_);
v___x_1055_ = lean_string_pushn(v___x_1053_, v___x_1054_, v_indent_1046_);
v___x_1056_ = lean_string_append(v_out_1048_, v___x_1055_);
lean_dec_ref(v___x_1055_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v_indent_1046_);
lean_ctor_set(v___x_1050_, 0, v___x_1056_);
v___x_1058_ = v___x_1050_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_indent_1046_);
v___x_1058_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1052_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__2(lean_object* v_____do__lift_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_column_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
v_column_1065_ = lean_ctor_get(v_____do__lift_1063_, 1);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_____do__lift_1063_);
if (v_isSharedCheck_1072_ == 0)
{
lean_object* v_unused_1073_; 
v_unused_1073_ = lean_ctor_get(v_____do__lift_1063_, 0);
lean_dec(v_unused_1073_);
v___x_1067_ = v_____do__lift_1063_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_column_1065_);
lean_dec(v_____do__lift_1063_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 1, v___y_1064_);
lean_ctor_set(v___x_1067_, 0, v_column_1065_);
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_column_1065_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v___y_1064_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(lean_object* v_x_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___y_1075_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3___boxed(lean_object* v_x_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(v_x_1078_, v___y_1079_);
lean_dec(v_x_1078_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(uint8_t v_flb_1116_, lean_object* v_items_1117_, lean_object* v_gs_1118_, lean_object* v_w_1119_, lean_object* v___y_1120_){
_start:
{
uint8_t v___y_1122_; lean_object* v_column_1127_; uint8_t v___x_1128_; uint8_t v___x_1129_; lean_object* v___x_1130_; lean_object* v_g_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v_r_1135_; lean_object* v___y_1137_; uint8_t v_foundLine_1142_; lean_object* v_space_1143_; uint8_t v___y_1145_; uint8_t v___x_1159_; 
v_column_1127_ = lean_ctor_get(v___y_1120_, 1);
v___x_1128_ = 0;
v___x_1129_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_1116_, v___x_1128_);
v___x_1130_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1130_, 0, v___x_1129_);
lean_inc(v_items_1117_);
v_g_1131_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_1131_, 0, v___x_1130_);
lean_ctor_set(v_g_1131_, 1, v_items_1117_);
lean_ctor_set_uint8(v_g_1131_, sizeof(void*)*2, v_flb_1116_);
v___x_1132_ = lean_box(0);
v___x_1133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1133_, 0, v_g_1131_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = lean_nat_sub(v_w_1119_, v_column_1127_);
lean_inc(v___x_1134_);
lean_inc(v_column_1127_);
v_r_1135_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_1133_, v_column_1127_, v___x_1134_);
v_foundLine_1142_ = lean_ctor_get_uint8(v_r_1135_, sizeof(void*)*1);
v_space_1143_ = lean_ctor_get(v_r_1135_, 0);
lean_inc(v_space_1143_);
v___x_1159_ = lean_nat_dec_lt(v___x_1134_, v_space_1143_);
if (v___x_1159_ == 0)
{
v___y_1145_ = v_foundLine_1142_;
goto v___jp_1144_;
}
else
{
v___y_1145_ = v___x_1159_;
goto v___jp_1144_;
}
v___jp_1121_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1123_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1123_, 0, v___y_1122_);
v___x_1124_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
lean_ctor_set(v___x_1124_, 1, v_items_1117_);
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*2, v_flb_1116_);
v___x_1125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
lean_ctor_set(v___x_1125_, 1, v_gs_1118_);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v___y_1120_);
return v___x_1126_;
}
v___jp_1136_:
{
uint8_t v_foundFlattenedHardLine_1138_; uint8_t v___x_1139_; 
v_foundFlattenedHardLine_1138_ = lean_ctor_get_uint8(v_r_1135_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_1135_);
v___x_1139_ = lean_bool_not(v_foundFlattenedHardLine_1138_);
if (v___x_1139_ == 0)
{
lean_dec_ref(v___y_1137_);
lean_dec(v___x_1134_);
v___y_1122_ = v___x_1139_;
goto v___jp_1121_;
}
else
{
lean_object* v_space_1140_; uint8_t v___x_1141_; 
v_space_1140_ = lean_ctor_get(v___y_1137_, 0);
lean_inc(v_space_1140_);
lean_dec_ref(v___y_1137_);
v___x_1141_ = lean_nat_dec_le(v_space_1140_, v___x_1134_);
lean_dec(v___x_1134_);
lean_dec(v_space_1140_);
v___y_1122_ = v___x_1141_;
goto v___jp_1121_;
}
}
v___jp_1144_:
{
if (v___y_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v_r_u2082_1147_; uint8_t v_foundLine_1148_; uint8_t v_foundFlattenedHardLine_1149_; lean_object* v_space_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1158_; 
v___x_1146_ = lean_nat_sub(v___x_1134_, v_space_1143_);
lean_inc(v_column_1127_);
lean_inc(v_gs_1118_);
v_r_u2082_1147_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_1118_, v_column_1127_, v___x_1146_);
v_foundLine_1148_ = lean_ctor_get_uint8(v_r_u2082_1147_, sizeof(void*)*1);
v_foundFlattenedHardLine_1149_ = lean_ctor_get_uint8(v_r_u2082_1147_, sizeof(void*)*1 + 1);
v_space_1150_ = lean_ctor_get(v_r_u2082_1147_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_r_u2082_1147_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1152_ = v_r_u2082_1147_;
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_space_1150_);
lean_dec(v_r_u2082_1147_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = lean_nat_add(v_space_1143_, v_space_1150_);
lean_dec(v_space_1150_);
lean_dec(v_space_1143_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1154_);
v___x_1156_ = v___x_1152_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
lean_ctor_set_uint8(v_reuseFailAlloc_1157_, sizeof(void*)*1, v_foundLine_1148_);
lean_ctor_set_uint8(v_reuseFailAlloc_1157_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_1149_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
v___y_1137_ = v___x_1156_;
goto v___jp_1136_;
}
}
}
else
{
lean_dec(v_space_1143_);
lean_inc_ref(v_r_1135_);
v___y_1137_ = v_r_1135_;
goto v___jp_1136_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1___boxed(lean_object* v_flb_1160_, lean_object* v_items_1161_, lean_object* v_gs_1162_, lean_object* v_w_1163_, lean_object* v___y_1164_){
_start:
{
uint8_t v_flb_boxed_1165_; lean_object* v_res_1166_; 
v_flb_boxed_1165_ = lean_unbox(v_flb_1160_);
v_res_1166_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_boxed_1165_, v_items_1161_, v_gs_1162_, v_w_1163_, v___y_1164_);
lean_dec(v_w_1163_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(lean_object* v_msg_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___f_1183_; lean_object* v___f_1184_; lean_object* v___f_1185_; lean_object* v___f_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_4858__overap_1195_; lean_object* v___x_1196_; 
v___f_1183_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0));
v___f_1184_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1));
v___f_1185_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2));
v___f_1186_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3));
v___x_1187_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4));
v___x_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
lean_ctor_set(v___x_1188_, 1, v___f_1183_);
v___x_1189_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5));
v___x_1190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
lean_ctor_set(v___x_1190_, 2, v___f_1184_);
lean_ctor_set(v___x_1190_, 3, v___f_1185_);
lean_ctor_set(v___x_1190_, 4, v___f_1186_);
v___x_1191_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6));
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = lean_box(0);
v___x_1194_ = l_instInhabitedOfMonad___redArg(v___x_1192_, v___x_1193_);
v___x_4858__overap_1195_ = lean_panic_fn_borrowed(v___x_1194_, v_msg_1181_);
lean_dec(v___x_1194_);
v___x_1196_ = lean_apply_1(v___x_4858__overap_1195_, v___y_1182_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(lean_object* v_w_1197_, lean_object* v_x_1198_, lean_object* v___y_1199_){
_start:
{
if (lean_obj_tag(v_x_1198_) == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_box(0);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
lean_ctor_set(v___x_1201_, 1, v___y_1199_);
return v___x_1201_;
}
else
{
lean_object* v_head_1202_; lean_object* v_items_1203_; 
v_head_1202_ = lean_ctor_get(v_x_1198_, 0);
v_items_1203_ = lean_ctor_get(v_head_1202_, 1);
lean_inc(v_items_1203_);
if (lean_obj_tag(v_items_1203_) == 0)
{
lean_object* v_tail_1204_; 
v_tail_1204_ = lean_ctor_get(v_x_1198_, 1);
lean_inc(v_tail_1204_);
lean_dec_ref_known(v_x_1198_, 2);
v_x_1198_ = v_tail_1204_;
goto _start;
}
else
{
lean_object* v_head_1206_; lean_object* v_tail_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1477_; 
lean_inc(v_head_1202_);
v_head_1206_ = lean_ctor_get(v_items_1203_, 0);
lean_inc(v_head_1206_);
v_tail_1207_ = lean_ctor_get(v_x_1198_, 1);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_x_1198_);
if (v_isSharedCheck_1477_ == 0)
{
lean_object* v_unused_1478_; 
v_unused_1478_ = lean_ctor_get(v_x_1198_, 0);
lean_dec(v_unused_1478_);
v___x_1209_ = v_x_1198_;
v_isShared_1210_ = v_isSharedCheck_1477_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_tail_1207_);
lean_dec(v_x_1198_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1477_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v_fla_1211_; uint8_t v_flb_1212_; lean_object* v_tail_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1475_; 
v_fla_1211_ = lean_ctor_get(v_head_1202_, 0);
lean_inc(v_fla_1211_);
v_flb_1212_ = lean_ctor_get_uint8(v_head_1202_, sizeof(void*)*2);
lean_dec(v_head_1202_);
v_tail_1213_ = lean_ctor_get(v_items_1203_, 1);
v_isSharedCheck_1475_ = !lean_is_exclusive(v_items_1203_);
if (v_isSharedCheck_1475_ == 0)
{
lean_object* v_unused_1476_; 
v_unused_1476_ = lean_ctor_get(v_items_1203_, 0);
lean_dec(v_unused_1476_);
v___x_1215_ = v_items_1203_;
v_isShared_1216_ = v_isSharedCheck_1475_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_tail_1213_);
lean_dec(v_items_1203_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1475_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v_f_1217_; lean_object* v_indent_1218_; lean_object* v_activeTags_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1474_; 
v_f_1217_ = lean_ctor_get(v_head_1206_, 0);
v_indent_1218_ = lean_ctor_get(v_head_1206_, 1);
v_activeTags_1219_ = lean_ctor_get(v_head_1206_, 2);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_head_1206_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1221_ = v_head_1206_;
v_isShared_1222_ = v_isSharedCheck_1474_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_activeTags_1219_);
lean_inc(v_indent_1218_);
lean_inc(v_f_1217_);
lean_dec(v_head_1206_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1474_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
uint8_t v___y_1224_; 
switch(lean_obj_tag(v_f_1217_))
{
case 0:
{
lean_object* v___x_1258_; 
lean_del_object(v___x_1221_);
lean_dec(v_activeTags_1219_);
lean_dec(v_indent_1218_);
lean_del_object(v___x_1215_);
lean_del_object(v___x_1209_);
v___x_1258_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1211_, v_flb_1212_, v_tail_1207_, v_tail_1213_);
v_x_1198_ = v___x_1258_;
goto _start;
}
case 1:
{
lean_del_object(v___x_1221_);
lean_dec(v_activeTags_1219_);
lean_del_object(v___x_1215_);
lean_del_object(v___x_1209_);
if (v_flb_1212_ == 0)
{
uint8_t v___x_1260_; 
v___x_1260_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1211_);
if (v___x_1260_ == 0)
{
lean_object* v_out_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1275_; 
v_out_1261_ = lean_ctor_get(v___y_1199_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___y_1199_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v___y_1199_, 1);
lean_dec(v_unused_1276_);
v___x_1263_ = v___y_1199_;
v_isShared_1264_ = v_isSharedCheck_1275_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_out_1261_);
lean_dec(v___y_1199_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1275_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; uint32_t v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1265_ = l_Int_toNat(v_indent_1218_);
lean_dec(v_indent_1218_);
v___x_1266_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1267_ = 32;
lean_inc(v___x_1265_);
v___x_1268_ = lean_string_pushn(v___x_1266_, v___x_1267_, v___x_1265_);
v___x_1269_ = lean_string_append(v_out_1261_, v___x_1268_);
lean_dec_ref(v___x_1268_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 1, v___x_1265_);
lean_ctor_set(v___x_1263_, 0, v___x_1269_);
v___x_1271_ = v___x_1263_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v___x_1265_);
v___x_1271_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; 
v___x_1272_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1211_, v_flb_1212_, v_tail_1207_, v_tail_1213_);
v_x_1198_ = v___x_1272_;
v___y_1199_ = v___x_1271_;
goto _start;
}
}
}
else
{
lean_object* v_out_1277_; lean_object* v_column_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1291_; 
lean_dec(v_indent_1218_);
v_out_1277_ = lean_ctor_get(v___y_1199_, 0);
v_column_1278_ = lean_ctor_get(v___y_1199_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___y_1199_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1280_ = v___y_1199_;
v_isShared_1281_ = v_isSharedCheck_1291_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_column_1278_);
lean_inc(v_out_1277_);
lean_dec(v___y_1199_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1291_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1282_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_1283_ = lean_string_append(v_out_1277_, v___x_1282_);
v___x_1284_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_1285_ = lean_nat_add(v_column_1278_, v___x_1284_);
lean_dec(v_column_1278_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v___x_1285_);
lean_ctor_set(v___x_1280_, 0, v___x_1283_);
v___x_1287_ = v___x_1280_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1288_; 
v___x_1288_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1211_, v_flb_1212_, v_tail_1207_, v_tail_1213_);
v_x_1198_ = v___x_1288_;
v___y_1199_ = v___x_1287_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = l_Int_toNat(v_indent_1218_);
lean_dec(v_indent_1218_);
v___x_1293_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1211_);
lean_dec(v_fla_1211_);
if (v___x_1293_ == 0)
{
lean_object* v_out_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1309_; 
v_out_1294_ = lean_ctor_get(v___y_1199_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___y_1199_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v___y_1199_, 1);
lean_dec(v_unused_1310_);
v___x_1296_ = v___y_1199_;
v_isShared_1297_ = v_isSharedCheck_1309_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_out_1294_);
lean_dec(v___y_1199_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1309_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; uint32_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1298_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1299_ = 32;
lean_inc(v___x_1292_);
v___x_1300_ = lean_string_pushn(v___x_1298_, v___x_1299_, v___x_1292_);
v___x_1301_ = lean_string_append(v_out_1294_, v___x_1300_);
lean_dec_ref(v___x_1300_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 1, v___x_1292_);
lean_ctor_set(v___x_1296_, 0, v___x_1301_);
v___x_1303_ = v___x_1296_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v___x_1292_);
v___x_1303_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1304_; lean_object* v_fst_1305_; lean_object* v_snd_1306_; 
v___x_1304_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1212_, v_tail_1213_, v_tail_1207_, v_w_1197_, v___x_1303_);
v_fst_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_fst_1305_);
v_snd_1306_ = lean_ctor_get(v___x_1304_, 1);
lean_inc(v_snd_1306_);
lean_dec_ref(v___x_1304_);
v_x_1198_ = v_fst_1305_;
v___y_1199_ = v_snd_1306_;
goto _start;
}
}
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v_fst_1315_; 
v___x_1311_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_1312_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_1313_ = lean_nat_sub(v_w_1197_, v___x_1312_);
lean_inc(v_tail_1207_);
lean_inc(v_tail_1213_);
v___x_1314_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1212_, v_tail_1213_, v_tail_1207_, v___x_1313_, v___y_1199_);
lean_dec(v___x_1313_);
v_fst_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_fst_1315_);
if (lean_obj_tag(v_fst_1315_) == 1)
{
lean_object* v_head_1316_; lean_object* v_snd_1317_; lean_object* v_fla_1318_; uint8_t v___x_1319_; 
v_head_1316_ = lean_ctor_get(v_fst_1315_, 0);
v_snd_1317_ = lean_ctor_get(v___x_1314_, 1);
lean_inc(v_snd_1317_);
lean_dec_ref(v___x_1314_);
v_fla_1318_ = lean_ctor_get(v_head_1316_, 0);
v___x_1319_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1318_);
if (v___x_1319_ == 0)
{
lean_object* v_out_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref_known(v_fst_1315_, 2);
v_out_1320_ = lean_ctor_get(v_snd_1317_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_snd_1317_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; 
v_unused_1336_ = lean_ctor_get(v_snd_1317_, 1);
lean_dec(v_unused_1336_);
v___x_1322_ = v_snd_1317_;
v_isShared_1323_ = v_isSharedCheck_1335_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_out_1320_);
lean_dec(v_snd_1317_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1335_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; uint32_t v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1324_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1325_ = 32;
lean_inc(v___x_1292_);
v___x_1326_ = lean_string_pushn(v___x_1324_, v___x_1325_, v___x_1292_);
v___x_1327_ = lean_string_append(v_out_1320_, v___x_1326_);
lean_dec_ref(v___x_1326_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 1, v___x_1292_);
lean_ctor_set(v___x_1322_, 0, v___x_1327_);
v___x_1329_ = v___x_1322_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v___x_1292_);
v___x_1329_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1330_; lean_object* v_fst_1331_; lean_object* v_snd_1332_; 
v___x_1330_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1212_, v_tail_1213_, v_tail_1207_, v_w_1197_, v___x_1329_);
v_fst_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_fst_1331_);
v_snd_1332_ = lean_ctor_get(v___x_1330_, 1);
lean_inc(v_snd_1332_);
lean_dec_ref(v___x_1330_);
v_x_1198_ = v_fst_1331_;
v___y_1199_ = v_snd_1332_;
goto _start;
}
}
}
else
{
lean_object* v_out_1337_; lean_object* v_column_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1348_; 
lean_dec(v___x_1292_);
lean_dec(v_tail_1213_);
lean_dec(v_tail_1207_);
v_out_1337_ = lean_ctor_get(v_snd_1317_, 0);
v_column_1338_ = lean_ctor_get(v_snd_1317_, 1);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_snd_1317_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1340_ = v_snd_1317_;
v_isShared_1341_ = v_isSharedCheck_1348_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_column_1338_);
lean_inc(v_out_1337_);
lean_dec(v_snd_1317_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1348_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1342_ = lean_string_append(v_out_1337_, v___x_1311_);
v___x_1343_ = lean_nat_add(v_column_1338_, v___x_1312_);
lean_dec(v_column_1338_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 1, v___x_1343_);
lean_ctor_set(v___x_1340_, 0, v___x_1342_);
v___x_1345_ = v___x_1340_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1342_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
v_x_1198_ = v_fst_1315_;
v___y_1199_ = v___x_1345_;
goto _start;
}
}
}
}
else
{
lean_object* v_snd_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_dec(v_fst_1315_);
lean_dec(v___x_1292_);
lean_dec(v_tail_1213_);
lean_dec(v_tail_1207_);
v_snd_1349_ = lean_ctor_get(v___x_1314_, 1);
lean_inc(v_snd_1349_);
lean_dec_ref(v___x_1314_);
v___x_1350_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0));
v___x_1351_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(v___x_1350_, v_snd_1349_);
return v___x_1351_;
}
}
}
}
case 2:
{
uint8_t v_force_1352_; uint8_t v___x_1353_; 
lean_del_object(v___x_1221_);
lean_dec(v_activeTags_1219_);
lean_del_object(v___x_1215_);
lean_del_object(v___x_1209_);
v_force_1352_ = lean_ctor_get_uint8(v_f_1217_, 0);
lean_dec_ref_known(v_f_1217_, 0);
v___x_1353_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1211_);
if (v___x_1353_ == 0)
{
v___y_1224_ = v___x_1353_;
goto v___jp_1223_;
}
else
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_bool_not(v_force_1352_);
v___y_1224_ = v___x_1354_;
goto v___jp_1223_;
}
}
case 3:
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1413_; 
lean_del_object(v___x_1209_);
v_a_1355_ = lean_ctor_get(v_f_1217_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_f_1217_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1357_ = v_f_1217_;
v_isShared_1358_ = v_isSharedCheck_1413_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v_f_1217_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1413_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
uint32_t v___x_1359_; lean_object* v_p_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1359_ = 10;
lean_inc_ref(v_a_1355_);
v_p_1360_ = lean_string_posof(v_a_1355_, v___x_1359_);
v___x_1361_ = lean_string_utf8_byte_size(v_a_1355_);
v___x_1362_ = lean_nat_dec_eq(v_p_1360_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_object* v_out_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1397_; 
v_out_1363_ = lean_ctor_get(v___y_1199_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___y_1199_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; 
v_unused_1398_ = lean_ctor_get(v___y_1199_, 1);
lean_dec(v_unused_1398_);
v___x_1365_ = v___y_1199_;
v_isShared_1366_ = v_isSharedCheck_1397_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_out_1363_);
lean_dec(v___y_1199_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1397_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; uint32_t v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = lean_string_utf8_extract(v_a_1355_, v___x_1367_, v_p_1360_);
v___x_1369_ = lean_string_append(v_out_1363_, v___x_1368_);
lean_dec_ref(v___x_1368_);
v___x_1370_ = l_Int_toNat(v_indent_1218_);
v___x_1371_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1372_ = 32;
lean_inc(v___x_1370_);
v___x_1373_ = lean_string_pushn(v___x_1371_, v___x_1372_, v___x_1370_);
v___x_1374_ = lean_string_append(v___x_1369_, v___x_1373_);
lean_dec_ref(v___x_1373_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v___x_1370_);
lean_ctor_set(v___x_1365_, 0, v___x_1374_);
v___x_1376_ = v___x_1365_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___x_1370_);
v___x_1376_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1377_ = lean_string_utf8_next(v_a_1355_, v_p_1360_);
lean_dec(v_p_1360_);
v___x_1378_ = lean_string_utf8_extract(v_a_1355_, v___x_1377_, v___x_1361_);
lean_dec(v___x_1377_);
lean_dec_ref(v_a_1355_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1378_);
v___x_1380_ = v___x_1357_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1382_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1380_);
v___x_1382_ = v___x_1221_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_indent_1218_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_activeTags_1219_);
v___x_1382_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v_is_1384_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1382_);
v_is_1384_ = v___x_1215_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_tail_1213_);
v_is_1384_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1385_ = lean_box(1);
v___x_1386_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_1211_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; lean_object* v_fst_1388_; lean_object* v_snd_1389_; 
lean_dec(v_fla_1211_);
v___x_1387_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1212_, v_is_1384_, v_tail_1207_, v_w_1197_, v___x_1376_);
v_fst_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_fst_1388_);
v_snd_1389_ = lean_ctor_get(v___x_1387_, 1);
lean_inc(v_snd_1389_);
lean_dec_ref(v___x_1387_);
v_x_1198_ = v_fst_1388_;
v___y_1199_ = v_snd_1389_;
goto _start;
}
else
{
lean_object* v___x_1391_; 
v___x_1391_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1211_, v_flb_1212_, v_tail_1207_, v_is_1384_);
v_x_1198_ = v___x_1391_;
v___y_1199_ = v___x_1376_;
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
lean_object* v_out_1399_; lean_object* v_column_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1412_; 
lean_dec(v_p_1360_);
lean_del_object(v___x_1357_);
lean_del_object(v___x_1221_);
lean_dec(v_activeTags_1219_);
lean_dec(v_indent_1218_);
lean_del_object(v___x_1215_);
v_out_1399_ = lean_ctor_get(v___y_1199_, 0);
v_column_1400_ = lean_ctor_get(v___y_1199_, 1);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___y_1199_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1402_ = v___y_1199_;
v_isShared_1403_ = v_isSharedCheck_1412_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_column_1400_);
lean_inc(v_out_1399_);
lean_dec(v___y_1199_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1412_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1404_ = lean_string_append(v_out_1399_, v_a_1355_);
v___x_1405_ = lean_string_length(v_a_1355_);
lean_dec_ref(v_a_1355_);
v___x_1406_ = lean_nat_add(v_column_1400_, v___x_1405_);
lean_dec(v___x_1405_);
lean_dec(v_column_1400_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 1, v___x_1406_);
lean_ctor_set(v___x_1402_, 0, v___x_1404_);
v___x_1408_ = v___x_1402_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; 
v___x_1409_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1211_, v_flb_1212_, v_tail_1207_, v_tail_1213_);
v_x_1198_ = v___x_1409_;
v___y_1199_ = v___x_1408_;
goto _start;
}
}
}
}
}
case 4:
{
lean_object* v_indent_1414_; lean_object* v_f_1415_; lean_object* v___x_1416_; lean_object* v___x_1418_; 
lean_del_object(v___x_1209_);
v_indent_1414_ = lean_ctor_get(v_f_1217_, 0);
lean_inc(v_indent_1414_);
v_f_1415_ = lean_ctor_get(v_f_1217_, 1);
lean_inc(v_f_1415_);
lean_dec_ref_known(v_f_1217_, 2);
v___x_1416_ = lean_int_add(v_indent_1218_, v_indent_1414_);
lean_dec(v_indent_1414_);
lean_dec(v_indent_1218_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 1, v___x_1416_);
lean_ctor_set(v___x_1221_, 0, v_f_1415_);
v___x_1418_ = v___x_1221_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_f_1415_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_activeTags_1219_);
v___x_1418_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1420_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1418_);
v___x_1420_ = v___x_1215_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_tail_1213_);
v___x_1420_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; 
v___x_1421_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1211_, v_flb_1212_, v_tail_1207_, v___x_1420_);
v_x_1198_ = v___x_1421_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_1425_; lean_object* v_a_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v_a_1425_ = lean_ctor_get(v_f_1217_, 0);
lean_inc(v_a_1425_);
v_a_1426_ = lean_ctor_get(v_f_1217_, 1);
lean_inc(v_a_1426_);
lean_dec_ref_known(v_f_1217_, 2);
v___x_1427_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_1218_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 2, v___x_1427_);
lean_ctor_set(v___x_1221_, 0, v_a_1425_);
v___x_1429_ = v___x_1221_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1425_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_indent_1218_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1430_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1430_, 0, v_a_1426_);
lean_ctor_set(v___x_1430_, 1, v_indent_1218_);
lean_ctor_set(v___x_1430_, 2, v_activeTags_1219_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1430_);
v___x_1432_ = v___x_1215_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_tail_1213_);
v___x_1432_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1434_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v___x_1432_);
lean_ctor_set(v___x_1209_, 0, v___x_1429_);
v___x_1434_ = v___x_1209_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; 
v___x_1435_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1211_, v_flb_1212_, v_tail_1207_, v___x_1434_);
v_x_1198_ = v___x_1435_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_1440_; uint8_t v_behavior_1441_; uint8_t v___x_1442_; 
lean_del_object(v___x_1209_);
v_a_1440_ = lean_ctor_get(v_f_1217_, 0);
lean_inc(v_a_1440_);
v_behavior_1441_ = lean_ctor_get_uint8(v_f_1217_, sizeof(void*)*1);
lean_dec_ref_known(v_f_1217_, 1);
v___x_1442_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1211_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1444_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v_a_1440_);
v___x_1444_ = v___x_1221_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1440_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_indent_1218_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_activeTags_1219_);
v___x_1444_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1445_ = lean_box(0);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 1, v___x_1445_);
lean_ctor_set(v___x_1215_, 0, v___x_1444_);
v___x_1447_ = v___x_1215_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v_fst_1450_; lean_object* v_snd_1451_; 
v___x_1448_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1211_, v_flb_1212_, v_tail_1207_, v_tail_1213_);
v___x_1449_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_behavior_1441_, v___x_1447_, v___x_1448_, v_w_1197_, v___y_1199_);
v_fst_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_fst_1450_);
v_snd_1451_ = lean_ctor_get(v___x_1449_, 1);
lean_inc(v_snd_1451_);
lean_dec_ref(v___x_1449_);
v_x_1198_ = v_fst_1450_;
v___y_1199_ = v_snd_1451_;
goto _start;
}
}
}
else
{
lean_object* v___x_1456_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v_a_1440_);
v___x_1456_ = v___x_1221_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1440_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_indent_1218_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_activeTags_1219_);
v___x_1456_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1458_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1456_);
v___x_1458_ = v___x_1215_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_tail_1213_);
v___x_1458_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1459_; 
v___x_1459_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1211_, v_flb_1212_, v_tail_1207_, v___x_1458_);
v_x_1198_ = v___x_1459_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1467_; 
lean_del_object(v___x_1209_);
v_a_1463_ = lean_ctor_get(v_f_1217_, 1);
lean_inc(v_a_1463_);
lean_dec_ref_known(v_f_1217_, 2);
v___x_1464_ = lean_unsigned_to_nat(1u);
v___x_1465_ = lean_nat_add(v_activeTags_1219_, v___x_1464_);
lean_dec(v_activeTags_1219_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 2, v___x_1465_);
lean_ctor_set(v___x_1221_, 0, v_a_1463_);
v___x_1467_ = v___x_1221_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1463_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_indent_1218_);
lean_ctor_set(v_reuseFailAlloc_1473_, 2, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1469_; 
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1467_);
v___x_1469_ = v___x_1215_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_tail_1213_);
v___x_1469_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1470_; 
v___x_1470_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1211_, v_flb_1212_, v_tail_1207_, v___x_1469_);
v_x_1198_ = v___x_1470_;
goto _start;
}
}
}
}
v___jp_1223_:
{
if (v___y_1224_ == 0)
{
lean_object* v_out_1225_; lean_object* v_column_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1255_; 
v_out_1225_ = lean_ctor_get(v___y_1199_, 0);
v_column_1226_ = lean_ctor_get(v___y_1199_, 1);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___y_1199_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1228_ = v___y_1199_;
v_isShared_1229_ = v_isSharedCheck_1255_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_column_1226_);
lean_inc(v_out_1225_);
lean_dec(v___y_1199_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1255_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; uint8_t v___x_1231_; 
lean_inc(v_column_1226_);
v___x_1230_ = lean_nat_to_int(v_column_1226_);
v___x_1231_ = lean_int_dec_lt(v___x_1230_, v_indent_1218_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; lean_object* v___x_1233_; uint32_t v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
lean_dec(v___x_1230_);
lean_dec(v_column_1226_);
v___x_1232_ = l_Int_toNat(v_indent_1218_);
lean_dec(v_indent_1218_);
v___x_1233_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1234_ = 32;
lean_inc(v___x_1232_);
v___x_1235_ = lean_string_pushn(v___x_1233_, v___x_1234_, v___x_1232_);
v___x_1236_ = lean_string_append(v_out_1225_, v___x_1235_);
lean_dec_ref(v___x_1235_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v___x_1232_);
lean_ctor_set(v___x_1228_, 0, v___x_1236_);
v___x_1238_ = v___x_1228_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___x_1232_);
v___x_1238_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1239_; 
v___x_1239_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1211_, v_flb_1212_, v_tail_1207_, v_tail_1213_);
v_x_1198_ = v___x_1239_;
v___y_1199_ = v___x_1238_;
goto _start;
}
}
else
{
lean_object* v___x_1242_; uint32_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1242_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_1243_ = 32;
v___x_1244_ = lean_int_sub(v_indent_1218_, v___x_1230_);
lean_dec(v___x_1230_);
lean_dec(v_indent_1218_);
v___x_1245_ = l_Int_toNat(v___x_1244_);
lean_dec(v___x_1244_);
v___x_1246_ = lean_string_pushn(v___x_1242_, v___x_1243_, v___x_1245_);
v___x_1247_ = lean_string_append(v_out_1225_, v___x_1246_);
v___x_1248_ = lean_string_length(v___x_1246_);
lean_dec_ref(v___x_1246_);
v___x_1249_ = lean_nat_add(v_column_1226_, v___x_1248_);
lean_dec(v___x_1248_);
lean_dec(v_column_1226_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v___x_1249_);
lean_ctor_set(v___x_1228_, 0, v___x_1247_);
v___x_1251_ = v___x_1228_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; 
v___x_1252_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1211_, v_flb_1212_, v_tail_1207_, v_tail_1213_);
v_x_1198_ = v___x_1252_;
v___y_1199_ = v___x_1251_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1256_; 
lean_dec(v_indent_1218_);
v___x_1256_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1211_, v_flb_1212_, v_tail_1207_, v_tail_1213_);
v_x_1198_ = v___x_1256_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0___boxed(lean_object* v_w_1479_, lean_object* v_x_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_1479_, v_x_1480_, v___y_1481_);
lean_dec(v_w_1479_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(lean_object* v_f_1483_, lean_object* v_w_1484_, lean_object* v_indent_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v___x_1487_; uint8_t v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1487_ = lean_box(1);
v___x_1488_ = 0;
v___x_1489_ = lean_nat_to_int(v_indent_1485_);
v___x_1490_ = lean_unsigned_to_nat(0u);
v___x_1491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1491_, 0, v_f_1483_);
lean_ctor_set(v___x_1491_, 1, v___x_1489_);
lean_ctor_set(v___x_1491_, 2, v___x_1490_);
v___x_1492_ = lean_box(0);
v___x_1493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1491_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1494_, 0, v___x_1487_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
lean_ctor_set_uint8(v___x_1494_, sizeof(void*)*2, v___x_1488_);
v___x_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v___x_1492_);
v___x_1496_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_1484_, v___x_1495_, v___y_1486_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0___boxed(lean_object* v_f_1497_, lean_object* v_w_1498_, lean_object* v_indent_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(v_f_1497_, v_w_1498_, v_indent_1499_, v___y_1500_);
lean_dec(v_w_1498_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty(lean_object* v_f_1502_, lean_object* v_width_1503_, lean_object* v_indent_1504_, lean_object* v_column_1505_){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v_snd_1509_; lean_object* v_out_1510_; 
v___x_1506_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
lean_ctor_set(v___x_1507_, 1, v_column_1505_);
v___x_1508_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(v_f_1502_, v_width_1503_, v_indent_1504_, v___x_1507_);
v_snd_1509_ = lean_ctor_get(v___x_1508_, 1);
lean_inc(v_snd_1509_);
lean_dec_ref(v___x_1508_);
v_out_1510_ = lean_ctor_get(v_snd_1509_, 0);
lean_inc_ref(v_out_1510_);
lean_dec(v_snd_1509_);
return v_out_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty___boxed(lean_object* v_f_1511_, lean_object* v_width_1512_, lean_object* v_indent_1513_, lean_object* v_column_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Std_Format_pretty(v_f_1511_, v_width_1512_, v_indent_1513_, v_column_1514_);
lean_dec(v_width_1512_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0(lean_object* v_f_1516_){
_start:
{
lean_inc(v_f_1516_);
return v_f_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object* v_f_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Std_instToFormatFormat___lam__0(v_f_1517_);
lean_dec(v_f_1517_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatString___lam__0(lean_object* v_s_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1522_, 0, v_s_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg___lam__0(lean_object* v_x_1525_, lean_object* v_inst_1526_, lean_object* v_x1_1527_, lean_object* v_x2_1528_){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_x1_1527_);
lean_ctor_set(v___x_1529_, 1, v_x_1525_);
v___x_1530_ = lean_apply_1(v_inst_1526_, v_x2_1528_);
v___x_1531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg(lean_object* v_inst_1532_, lean_object* v_x_1533_, lean_object* v_x_1534_){
_start:
{
if (lean_obj_tag(v_x_1533_) == 0)
{
lean_object* v___x_1535_; 
lean_dec(v_x_1534_);
lean_dec_ref(v_inst_1532_);
v___x_1535_ = lean_box(0);
return v___x_1535_;
}
else
{
lean_object* v_tail_1536_; 
v_tail_1536_ = lean_ctor_get(v_x_1533_, 1);
if (lean_obj_tag(v_tail_1536_) == 0)
{
lean_object* v_head_1537_; lean_object* v___x_1538_; 
lean_dec(v_x_1534_);
v_head_1537_ = lean_ctor_get(v_x_1533_, 0);
lean_inc(v_head_1537_);
lean_dec_ref_known(v_x_1533_, 2);
v___x_1538_ = lean_apply_1(v_inst_1532_, v_head_1537_);
return v___x_1538_;
}
else
{
lean_object* v_head_1539_; lean_object* v___f_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
lean_inc(v_tail_1536_);
v_head_1539_ = lean_ctor_get(v_x_1533_, 0);
lean_inc(v_head_1539_);
lean_dec_ref_known(v_x_1533_, 2);
lean_inc_ref(v_inst_1532_);
v___f_1540_ = lean_alloc_closure((void*)(l_Std_Format_joinSep___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1540_, 0, v_x_1534_);
lean_closure_set(v___f_1540_, 1, v_inst_1532_);
v___x_1541_ = lean_apply_1(v_inst_1532_, v_head_1539_);
v___x_1542_ = l_List_foldl___redArg(v___f_1540_, v___x_1541_, v_tail_1536_);
return v___x_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep(lean_object* v_00_u03b1_1543_, lean_object* v_inst_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Std_Format_joinSep___redArg(v_inst_1544_, v_x_1545_, v_x_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg___lam__0(lean_object* v_pre_1548_, lean_object* v_inst_1549_, lean_object* v_x1_1550_, lean_object* v_x2_1551_){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1552_, 0, v_x1_1550_);
lean_ctor_set(v___x_1552_, 1, v_pre_1548_);
v___x_1553_ = lean_apply_1(v_inst_1549_, v_x2_1551_);
v___x_1554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg(lean_object* v_inst_1555_, lean_object* v_pre_1556_, lean_object* v_x_1557_){
_start:
{
if (lean_obj_tag(v_x_1557_) == 0)
{
lean_object* v___x_1558_; 
lean_dec(v_pre_1556_);
lean_dec_ref(v_inst_1555_);
v___x_1558_ = lean_box(0);
return v___x_1558_;
}
else
{
lean_object* v_head_1559_; lean_object* v_tail_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1570_; 
v_head_1559_ = lean_ctor_get(v_x_1557_, 0);
v_tail_1560_ = lean_ctor_get(v_x_1557_, 1);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_x_1557_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1562_ = v_x_1557_;
v_isShared_1563_ = v_isSharedCheck_1570_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_tail_1560_);
lean_inc(v_head_1559_);
lean_dec(v_x_1557_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1570_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___f_1564_; lean_object* v___x_1565_; lean_object* v___x_1567_; 
lean_inc_ref(v_inst_1555_);
lean_inc(v_pre_1556_);
v___f_1564_ = lean_alloc_closure((void*)(l_Std_Format_prefixJoin___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1564_, 0, v_pre_1556_);
lean_closure_set(v___f_1564_, 1, v_inst_1555_);
v___x_1565_ = lean_apply_1(v_inst_1555_, v_head_1559_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set_tag(v___x_1562_, 5);
lean_ctor_set(v___x_1562_, 1, v___x_1565_);
lean_ctor_set(v___x_1562_, 0, v_pre_1556_);
v___x_1567_ = v___x_1562_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_pre_1556_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_List_foldl___redArg(v___f_1564_, v___x_1567_, v_tail_1560_);
return v___x_1568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin(lean_object* v_00_u03b1_1571_, lean_object* v_inst_1572_, lean_object* v_pre_1573_, lean_object* v_x_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Std_Format_prefixJoin___redArg(v_inst_1572_, v_pre_1573_, v_x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg___lam__0(lean_object* v_inst_1576_, lean_object* v_x_1577_, lean_object* v_x1_1578_, lean_object* v_x2_1579_){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = lean_apply_1(v_inst_1576_, v_x2_1579_);
v___x_1581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1581_, 0, v_x1_1578_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
lean_ctor_set(v___x_1582_, 1, v_x_1577_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg(lean_object* v_inst_1583_, lean_object* v_x_1584_, lean_object* v_x_1585_){
_start:
{
if (lean_obj_tag(v_x_1584_) == 0)
{
lean_object* v___x_1586_; 
lean_dec(v_x_1585_);
lean_dec_ref(v_inst_1583_);
v___x_1586_ = lean_box(0);
return v___x_1586_;
}
else
{
lean_object* v_head_1587_; lean_object* v_tail_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1598_; 
v_head_1587_ = lean_ctor_get(v_x_1584_, 0);
v_tail_1588_ = lean_ctor_get(v_x_1584_, 1);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1590_ = v_x_1584_;
v_isShared_1591_ = v_isSharedCheck_1598_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_tail_1588_);
lean_inc(v_head_1587_);
lean_dec(v_x_1584_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1598_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___f_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
lean_inc(v_x_1585_);
lean_inc_ref(v_inst_1583_);
v___f_1592_ = lean_alloc_closure((void*)(l_Std_Format_joinSuffix___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1592_, 0, v_inst_1583_);
lean_closure_set(v___f_1592_, 1, v_x_1585_);
v___x_1593_ = lean_apply_1(v_inst_1583_, v_head_1587_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set_tag(v___x_1590_, 5);
lean_ctor_set(v___x_1590_, 1, v_x_1585_);
lean_ctor_set(v___x_1590_, 0, v___x_1593_);
v___x_1595_ = v___x_1590_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_x_1585_);
v___x_1595_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_List_foldl___redArg(v___f_1592_, v___x_1595_, v_tail_1588_);
return v___x_1596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix(lean_object* v_00_u03b1_1599_, lean_object* v_inst_1600_, lean_object* v_x_1601_, lean_object* v_x_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Std_Format_joinSuffix___redArg(v_inst_1600_, v_x_1601_, v_x_1602_);
return v___x_1603_;
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
