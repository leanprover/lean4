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
lean_inc_ref_n(v_a_290_, 3);
lean_dec_ref(v_x_267_);
v___x_291_ = 10;
v_p_292_ = lean_string_posof(v_a_290_, v___x_291_);
lean_inc(v_p_292_);
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
uint8_t v_x_415__boxed_336_; lean_object* v_res_337_; 
v_x_415__boxed_336_ = lean_unbox(v_x_333_);
v_res_337_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_x_332_, v_x_415__boxed_336_, v_x_334_, v_x_335_);
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
v___x_420_ = ((lean_object*)(l_Std_Format_instInhabitedSpaceResult_default___closed__0));
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
lean_inc_n(v_x_419_, 2);
v___x_439_ = lean_nat_to_int(v_x_419_);
lean_inc(v_x_418_);
v___x_440_ = lean_nat_to_int(v_x_418_);
v___x_441_ = lean_int_add(v___x_439_, v___x_440_);
lean_dec(v___x_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_int_sub(v___x_441_, v_indent_437_);
lean_dec(v_indent_437_);
lean_dec(v___x_441_);
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
uint8_t v_flb_1984__boxed_572_; lean_object* v_res_573_; 
v_flb_1984__boxed_572_ = lean_unbox(v_flb_569_);
v_res_573_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_568_, v_flb_1984__boxed_572_, v_tail_570_, v_is_x27_571_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(lean_object* v_indent_581_, lean_object* v_pushNewline_582_, lean_object* v_toBind_583_, lean_object* v___f_584_, lean_object* v_____r_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_586_ = l_Int_toNat(v_indent_581_);
v___x_587_ = lean_apply_1(v_pushNewline_582_, v___x_586_);
v___x_588_ = lean_apply_4(v_toBind_583_, lean_box(0), lean_box(0), v___x_587_, v___f_584_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed(lean_object* v_indent_589_, lean_object* v_pushNewline_590_, lean_object* v_toBind_591_, lean_object* v___f_592_, lean_object* v_____r_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(v_indent_589_, v_pushNewline_590_, v_toBind_591_, v___f_592_, v_____r_593_);
lean_dec(v_indent_589_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(lean_object* v_indent_595_, lean_object* v_inst_596_, lean_object* v_toBind_597_, lean_object* v___f_598_, lean_object* v___f_599_, lean_object* v_k_600_){
_start:
{
lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_601_ = lean_nat_to_int(v_k_600_);
v___x_602_ = lean_int_dec_lt(v___x_601_, v_indent_595_);
if (v___x_602_ == 0)
{
lean_object* v_pushNewline_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v___x_601_);
lean_dec(v___f_599_);
v_pushNewline_603_ = lean_ctor_get(v_inst_596_, 1);
lean_inc(v_pushNewline_603_);
lean_dec_ref(v_inst_596_);
v___x_604_ = l_Int_toNat(v_indent_595_);
v___x_605_ = lean_apply_1(v_pushNewline_603_, v___x_604_);
v___x_606_ = lean_apply_4(v_toBind_597_, lean_box(0), lean_box(0), v___x_605_, v___f_598_);
return v___x_606_;
}
else
{
lean_object* v_pushOutput_607_; lean_object* v___x_608_; uint32_t v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v___f_598_);
v_pushOutput_607_ = lean_ctor_get(v_inst_596_, 0);
lean_inc(v_pushOutput_607_);
lean_dec_ref(v_inst_596_);
v___x_608_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_609_ = 32;
v___x_610_ = lean_int_sub(v_indent_595_, v___x_601_);
lean_dec(v___x_601_);
v___x_611_ = l_Int_toNat(v___x_610_);
lean_dec(v___x_610_);
v___x_612_ = lean_string_pushn(v___x_608_, v___x_609_, v___x_611_);
v___x_613_ = lean_apply_1(v_pushOutput_607_, v___x_612_);
v___x_614_ = lean_apply_4(v_toBind_597_, lean_box(0), lean_box(0), v___x_613_, v___f_599_);
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed(lean_object* v_indent_615_, lean_object* v_inst_616_, lean_object* v_toBind_617_, lean_object* v___f_618_, lean_object* v___f_619_, lean_object* v_k_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(v_indent_615_, v_inst_616_, v_toBind_617_, v___f_618_, v___f_619_, v_k_620_);
lean_dec(v_indent_615_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9(lean_object* v_inst_622_, lean_object* v_activeTags_623_, lean_object* v_toBind_624_, lean_object* v___f_625_, lean_object* v_____r_626_){
_start:
{
lean_object* v_endTags_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_endTags_627_ = lean_ctor_get(v_inst_622_, 4);
lean_inc(v_endTags_627_);
lean_dec_ref(v_inst_622_);
v___x_628_ = lean_apply_1(v_endTags_627_, v_activeTags_623_);
v___x_629_ = lean_apply_4(v_toBind_624_, lean_box(0), lean_box(0), v___x_628_, v___f_625_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1(lean_object* v_gs_x27_630_, lean_object* v_tail_631_, lean_object* v_w_632_, lean_object* v_inst_633_, lean_object* v_inst_634_, lean_object* v_____r_635_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_apply_1(v_gs_x27_630_, v_tail_631_);
v___x_637_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_632_, v_inst_633_, v_inst_634_, v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(uint8_t v_flb_639_, lean_object* v_tail_640_, lean_object* v_tail_641_, lean_object* v_w_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_toBind_645_, lean_object* v_____r_646_){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
lean_inc_ref(v_inst_644_);
lean_inc_ref(v_inst_643_);
lean_inc(v_w_642_);
v___x_647_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_639_, v_tail_640_, v_tail_641_, v_w_642_, v_inst_643_, v_inst_644_);
v___x_648_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_648_, 0, v_w_642_);
lean_closure_set(v___x_648_, 1, v_inst_643_);
lean_closure_set(v___x_648_, 2, v_inst_644_);
v___x_649_ = lean_apply_4(v_toBind_645_, lean_box(0), lean_box(0), v___x_647_, v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed(lean_object* v_flb_650_, lean_object* v_tail_651_, lean_object* v_tail_652_, lean_object* v_w_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_toBind_656_, lean_object* v_____r_657_){
_start:
{
uint8_t v_flb_2076__boxed_658_; lean_object* v_res_659_; 
v_flb_2076__boxed_658_ = lean_unbox(v_flb_650_);
v_res_659_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(v_flb_2076__boxed_658_, v_tail_651_, v_tail_652_, v_w_653_, v_inst_654_, v_inst_655_, v_toBind_656_, v_____r_657_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(lean_object* v_breakHere_661_, lean_object* v_w_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_endTags_665_, lean_object* v_activeTags_666_, lean_object* v_toBind_667_, lean_object* v_pushOutput_668_, lean_object* v___x_669_, lean_object* v_____x_670_){
_start:
{
if (lean_obj_tag(v_____x_670_) == 1)
{
lean_object* v_head_671_; lean_object* v_fla_672_; uint8_t v___x_673_; 
v_head_671_ = lean_ctor_get(v_____x_670_, 0);
v_fla_672_ = lean_ctor_get(v_head_671_, 0);
v___x_673_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_672_);
if (v___x_673_ == 0)
{
lean_dec_ref(v_____x_670_);
lean_dec_ref(v___x_669_);
lean_dec(v_pushOutput_668_);
lean_dec(v_toBind_667_);
lean_dec(v_activeTags_666_);
lean_dec(v_endTags_665_);
lean_dec_ref(v_inst_664_);
lean_dec_ref(v_inst_663_);
lean_dec(v_w_662_);
lean_inc(v_breakHere_661_);
return v_breakHere_661_;
}
else
{
lean_object* v___f_674_; lean_object* v___f_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___f_674_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4), 5, 4);
lean_closure_set(v___f_674_, 0, v_w_662_);
lean_closure_set(v___f_674_, 1, v_inst_663_);
lean_closure_set(v___f_674_, 2, v_inst_664_);
lean_closure_set(v___f_674_, 3, v_____x_670_);
lean_inc(v_toBind_667_);
v___f_675_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_675_, 0, v_endTags_665_);
lean_closure_set(v___f_675_, 1, v_activeTags_666_);
lean_closure_set(v___f_675_, 2, v_toBind_667_);
lean_closure_set(v___f_675_, 3, v___f_674_);
v___x_676_ = lean_apply_1(v_pushOutput_668_, v___x_669_);
v___x_677_ = lean_apply_4(v_toBind_667_, lean_box(0), lean_box(0), v___x_676_, v___f_675_);
return v___x_677_;
}
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
lean_dec(v_____x_670_);
lean_dec_ref(v___x_669_);
lean_dec(v_pushOutput_668_);
lean_dec(v_toBind_667_);
lean_dec(v_activeTags_666_);
lean_dec(v_endTags_665_);
lean_dec_ref(v_inst_664_);
lean_dec(v_w_662_);
v___x_678_ = lean_box(0);
v___x_679_ = l_instInhabitedOfMonad___redArg(v_inst_663_, v___x_678_);
v___x_680_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0));
v___x_681_ = l_panic___redArg(v___x_679_, v___x_680_);
lean_dec(v___x_679_);
return v___x_681_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed(lean_object* v_breakHere_682_, lean_object* v_w_683_, lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_endTags_686_, lean_object* v_activeTags_687_, lean_object* v_toBind_688_, lean_object* v_pushOutput_689_, lean_object* v___x_690_, lean_object* v_____x_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(v_breakHere_682_, v_w_683_, v_inst_684_, v_inst_685_, v_endTags_686_, v_activeTags_687_, v_toBind_688_, v_pushOutput_689_, v___x_690_, v_____x_691_);
lean_dec(v_breakHere_682_);
return v_res_692_;
}
}
static lean_object* _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_694_ = lean_string_length(v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(lean_object* v_a_695_, lean_object* v_p_696_, lean_object* v___x_697_, lean_object* v_indent_698_, lean_object* v_activeTags_699_, lean_object* v_tail_700_, lean_object* v_fla_701_, uint8_t v_flb_702_, lean_object* v_tail_703_, lean_object* v_w_704_, lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v_toBind_707_, lean_object* v_gs_x27_708_, lean_object* v_____r_709_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v_is_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_710_ = lean_string_utf8_next(v_a_695_, v_p_696_);
v___x_711_ = lean_string_utf8_extract(v_a_695_, v___x_710_, v___x_697_);
lean_dec(v___x_710_);
v___x_712_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
v___x_713_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
lean_ctor_set(v___x_713_, 1, v_indent_698_);
lean_ctor_set(v___x_713_, 2, v_activeTags_699_);
v_is_714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_is_714_, 0, v___x_713_);
lean_ctor_set(v_is_714_, 1, v_tail_700_);
v___x_715_ = lean_box(1);
v___x_716_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_701_, v___x_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec_ref(v_gs_x27_708_);
lean_inc_ref(v_inst_706_);
lean_inc_ref(v_inst_705_);
lean_inc(v_w_704_);
v___x_717_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_702_, v_is_714_, v_tail_703_, v_w_704_, v_inst_705_, v_inst_706_);
v___x_718_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_718_, 0, v_w_704_);
lean_closure_set(v___x_718_, 1, v_inst_705_);
lean_closure_set(v___x_718_, 2, v_inst_706_);
v___x_719_ = lean_apply_4(v_toBind_707_, lean_box(0), lean_box(0), v___x_717_, v___x_718_);
return v___x_719_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; 
lean_dec(v_toBind_707_);
lean_dec(v_tail_703_);
v___x_720_ = lean_apply_1(v_gs_x27_708_, v_is_714_);
v___x_721_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_704_, v_inst_705_, v_inst_706_, v___x_720_);
return v___x_721_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed(lean_object* v_a_722_, lean_object* v_p_723_, lean_object* v___x_724_, lean_object* v_indent_725_, lean_object* v_activeTags_726_, lean_object* v_tail_727_, lean_object* v_fla_728_, lean_object* v_flb_729_, lean_object* v_tail_730_, lean_object* v_w_731_, lean_object* v_inst_732_, lean_object* v_inst_733_, lean_object* v_toBind_734_, lean_object* v_gs_x27_735_, lean_object* v_____r_736_){
_start:
{
uint8_t v_flb_2100__boxed_737_; lean_object* v_res_738_; 
v_flb_2100__boxed_737_ = lean_unbox(v_flb_729_);
v_res_738_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(v_a_722_, v_p_723_, v___x_724_, v_indent_725_, v_activeTags_726_, v_tail_727_, v_fla_728_, v_flb_2100__boxed_737_, v_tail_730_, v_w_731_, v_inst_732_, v_inst_733_, v_toBind_734_, v_gs_x27_735_, v_____r_736_);
lean_dec(v_fla_728_);
lean_dec(v___x_724_);
lean_dec(v_p_723_);
lean_dec_ref(v_a_722_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(lean_object* v_activeTags_739_, lean_object* v_a_740_, lean_object* v_indent_741_, lean_object* v_tail_742_, lean_object* v_gs_x27_743_, lean_object* v_w_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_____r_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = lean_nat_add(v_activeTags_739_, v___x_748_);
v___x_750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_750_, 0, v_a_740_);
lean_ctor_set(v___x_750_, 1, v_indent_741_);
lean_ctor_set(v___x_750_, 2, v___x_749_);
v___x_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v_tail_742_);
v___x_752_ = lean_apply_1(v_gs_x27_743_, v___x_751_);
v___x_753_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_744_, v_inst_745_, v_inst_746_, v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed(lean_object* v_activeTags_754_, lean_object* v_a_755_, lean_object* v_indent_756_, lean_object* v_tail_757_, lean_object* v_gs_x27_758_, lean_object* v_w_759_, lean_object* v_inst_760_, lean_object* v_inst_761_, lean_object* v_____r_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(v_activeTags_754_, v_a_755_, v_indent_756_, v_tail_757_, v_gs_x27_758_, v_w_759_, v_inst_760_, v_inst_761_, v_____r_762_);
lean_dec(v_activeTags_754_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(lean_object* v_w_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_x_767_){
_start:
{
if (lean_obj_tag(v_x_767_) == 0)
{
lean_object* v_toApplicative_768_; lean_object* v_toPure_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_toApplicative_768_ = lean_ctor_get(v_inst_765_, 0);
lean_inc_ref(v_toApplicative_768_);
lean_dec_ref(v_inst_766_);
lean_dec_ref(v_inst_765_);
lean_dec(v_w_764_);
v_toPure_769_ = lean_ctor_get(v_toApplicative_768_, 1);
lean_inc(v_toPure_769_);
lean_dec_ref(v_toApplicative_768_);
v___x_770_ = lean_box(0);
v___x_771_ = lean_apply_2(v_toPure_769_, lean_box(0), v___x_770_);
return v___x_771_;
}
else
{
lean_object* v_head_772_; lean_object* v_items_773_; 
v_head_772_ = lean_ctor_get(v_x_767_, 0);
v_items_773_ = lean_ctor_get(v_head_772_, 1);
lean_inc(v_items_773_);
if (lean_obj_tag(v_items_773_) == 0)
{
lean_object* v_tail_774_; 
v_tail_774_ = lean_ctor_get(v_x_767_, 1);
lean_inc(v_tail_774_);
lean_dec_ref(v_x_767_);
v_x_767_ = v_tail_774_;
goto _start;
}
else
{
lean_object* v_head_776_; lean_object* v_toBind_777_; lean_object* v_tail_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_921_; 
lean_inc(v_head_772_);
v_head_776_ = lean_ctor_get(v_items_773_, 0);
lean_inc(v_head_776_);
v_toBind_777_ = lean_ctor_get(v_inst_765_, 1);
v_tail_778_ = lean_ctor_get(v_x_767_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_x_767_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; 
v_unused_922_ = lean_ctor_get(v_x_767_, 0);
lean_dec(v_unused_922_);
v___x_780_ = v_x_767_;
v_isShared_781_ = v_isSharedCheck_921_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_tail_778_);
lean_dec(v_x_767_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_921_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v_fla_782_; uint8_t v_flb_783_; lean_object* v_tail_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_919_; 
v_fla_782_ = lean_ctor_get(v_head_772_, 0);
lean_inc(v_fla_782_);
v_flb_783_ = lean_ctor_get_uint8(v_head_772_, sizeof(void*)*2);
lean_dec(v_head_772_);
v_tail_784_ = lean_ctor_get(v_items_773_, 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v_items_773_);
if (v_isSharedCheck_919_ == 0)
{
lean_object* v_unused_920_; 
v_unused_920_ = lean_ctor_get(v_items_773_, 0);
lean_dec(v_unused_920_);
v___x_786_ = v_items_773_;
v_isShared_787_ = v_isSharedCheck_919_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_tail_784_);
lean_dec(v_items_773_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_919_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v_f_788_; lean_object* v_indent_789_; lean_object* v_activeTags_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_918_; 
v_f_788_ = lean_ctor_get(v_head_776_, 0);
v_indent_789_ = lean_ctor_get(v_head_776_, 1);
v_activeTags_790_ = lean_ctor_get(v_head_776_, 2);
v_isSharedCheck_918_ = !lean_is_exclusive(v_head_776_);
if (v_isSharedCheck_918_ == 0)
{
v___x_792_ = v_head_776_;
v_isShared_793_ = v_isSharedCheck_918_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_activeTags_790_);
lean_inc(v_indent_789_);
lean_inc(v_f_788_);
lean_dec(v_head_776_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_918_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v_gs_x27_795_; 
v___x_794_ = lean_box(v_flb_783_);
lean_inc(v_tail_778_);
lean_inc(v_fla_782_);
v_gs_x27_795_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v_gs_x27_795_, 0, v_fla_782_);
lean_closure_set(v_gs_x27_795_, 1, v___x_794_);
lean_closure_set(v_gs_x27_795_, 2, v_tail_778_);
switch(lean_obj_tag(v_f_788_))
{
case 0:
{
lean_object* v_endTags_796_; lean_object* v___f_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_inc(v_toBind_777_);
lean_del_object(v___x_792_);
lean_dec(v_indent_789_);
lean_del_object(v___x_786_);
lean_dec(v_fla_782_);
lean_del_object(v___x_780_);
lean_dec(v_tail_778_);
v_endTags_796_ = lean_ctor_get(v_inst_766_, 4);
lean_inc(v_endTags_796_);
v___f_797_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_797_, 0, v_gs_x27_795_);
lean_closure_set(v___f_797_, 1, v_tail_784_);
lean_closure_set(v___f_797_, 2, v_w_764_);
lean_closure_set(v___f_797_, 3, v_inst_765_);
lean_closure_set(v___f_797_, 4, v_inst_766_);
v___x_798_ = lean_apply_1(v_endTags_796_, v_activeTags_790_);
v___x_799_ = lean_apply_4(v_toBind_777_, lean_box(0), lean_box(0), v___x_798_, v___f_797_);
return v___x_799_;
}
case 1:
{
lean_inc(v_toBind_777_);
lean_del_object(v___x_792_);
lean_del_object(v___x_786_);
lean_del_object(v___x_780_);
if (v_flb_783_ == 0)
{
uint8_t v___x_800_; 
lean_dec(v_tail_778_);
v___x_800_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_782_);
lean_dec(v_fla_782_);
if (v___x_800_ == 0)
{
lean_object* v_pushNewline_801_; lean_object* v_endTags_802_; lean_object* v___f_803_; lean_object* v___f_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_pushNewline_801_ = lean_ctor_get(v_inst_766_, 1);
lean_inc(v_pushNewline_801_);
v_endTags_802_ = lean_ctor_get(v_inst_766_, 4);
lean_inc(v_endTags_802_);
v___f_803_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_803_, 0, v_gs_x27_795_);
lean_closure_set(v___f_803_, 1, v_tail_784_);
lean_closure_set(v___f_803_, 2, v_w_764_);
lean_closure_set(v___f_803_, 3, v_inst_765_);
lean_closure_set(v___f_803_, 4, v_inst_766_);
lean_inc(v_toBind_777_);
v___f_804_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_804_, 0, v_endTags_802_);
lean_closure_set(v___f_804_, 1, v_activeTags_790_);
lean_closure_set(v___f_804_, 2, v_toBind_777_);
lean_closure_set(v___f_804_, 3, v___f_803_);
v___x_805_ = l_Int_toNat(v_indent_789_);
lean_dec(v_indent_789_);
v___x_806_ = lean_apply_1(v_pushNewline_801_, v___x_805_);
v___x_807_ = lean_apply_4(v_toBind_777_, lean_box(0), lean_box(0), v___x_806_, v___f_804_);
return v___x_807_;
}
else
{
lean_object* v_pushOutput_808_; lean_object* v_endTags_809_; lean_object* v___f_810_; lean_object* v___f_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec(v_indent_789_);
v_pushOutput_808_ = lean_ctor_get(v_inst_766_, 0);
lean_inc(v_pushOutput_808_);
v_endTags_809_ = lean_ctor_get(v_inst_766_, 4);
lean_inc(v_endTags_809_);
v___f_810_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_810_, 0, v_gs_x27_795_);
lean_closure_set(v___f_810_, 1, v_tail_784_);
lean_closure_set(v___f_810_, 2, v_w_764_);
lean_closure_set(v___f_810_, 3, v_inst_765_);
lean_closure_set(v___f_810_, 4, v_inst_766_);
lean_inc(v_toBind_777_);
v___f_811_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_811_, 0, v_endTags_809_);
lean_closure_set(v___f_811_, 1, v_activeTags_790_);
lean_closure_set(v___f_811_, 2, v_toBind_777_);
lean_closure_set(v___f_811_, 3, v___f_810_);
v___x_812_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_813_ = lean_apply_1(v_pushOutput_808_, v___x_812_);
v___x_814_ = lean_apply_4(v_toBind_777_, lean_box(0), lean_box(0), v___x_813_, v___f_811_);
return v___x_814_;
}
}
else
{
lean_object* v_pushOutput_815_; lean_object* v_pushNewline_816_; lean_object* v_endTags_817_; lean_object* v___x_818_; lean_object* v___f_819_; lean_object* v___f_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v_breakHere_823_; uint8_t v___x_824_; 
lean_dec_ref(v_gs_x27_795_);
v_pushOutput_815_ = lean_ctor_get(v_inst_766_, 0);
v_pushNewline_816_ = lean_ctor_get(v_inst_766_, 1);
v_endTags_817_ = lean_ctor_get(v_inst_766_, 4);
v___x_818_ = lean_box(v_flb_783_);
lean_inc_n(v_toBind_777_, 3);
lean_inc_ref(v_inst_766_);
lean_inc_ref(v_inst_765_);
lean_inc(v_w_764_);
lean_inc(v_tail_778_);
lean_inc(v_tail_784_);
v___f_819_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_819_, 0, v___x_818_);
lean_closure_set(v___f_819_, 1, v_tail_784_);
lean_closure_set(v___f_819_, 2, v_tail_778_);
lean_closure_set(v___f_819_, 3, v_w_764_);
lean_closure_set(v___f_819_, 4, v_inst_765_);
lean_closure_set(v___f_819_, 5, v_inst_766_);
lean_closure_set(v___f_819_, 6, v_toBind_777_);
lean_inc(v_activeTags_790_);
lean_inc(v_endTags_817_);
v___f_820_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_820_, 0, v_endTags_817_);
lean_closure_set(v___f_820_, 1, v_activeTags_790_);
lean_closure_set(v___f_820_, 2, v_toBind_777_);
lean_closure_set(v___f_820_, 3, v___f_819_);
v___x_821_ = l_Int_toNat(v_indent_789_);
lean_dec(v_indent_789_);
lean_inc(v_pushNewline_816_);
v___x_822_ = lean_apply_1(v_pushNewline_816_, v___x_821_);
v_breakHere_823_ = lean_apply_4(v_toBind_777_, lean_box(0), lean_box(0), v___x_822_, v___f_820_);
v___x_824_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_782_);
lean_dec(v_fla_782_);
if (v___x_824_ == 0)
{
lean_dec(v_activeTags_790_);
lean_dec(v_tail_784_);
lean_dec(v_tail_778_);
lean_dec(v_toBind_777_);
lean_dec_ref(v_inst_766_);
lean_dec_ref(v_inst_765_);
lean_dec(v_w_764_);
return v_breakHere_823_;
}
else
{
lean_object* v___x_825_; lean_object* v___f_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_825_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
lean_inc(v_pushOutput_815_);
lean_inc(v_toBind_777_);
lean_inc(v_endTags_817_);
lean_inc_ref(v_inst_766_);
lean_inc_ref(v_inst_765_);
lean_inc(v_w_764_);
v___f_826_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_826_, 0, v_breakHere_823_);
lean_closure_set(v___f_826_, 1, v_w_764_);
lean_closure_set(v___f_826_, 2, v_inst_765_);
lean_closure_set(v___f_826_, 3, v_inst_766_);
lean_closure_set(v___f_826_, 4, v_endTags_817_);
lean_closure_set(v___f_826_, 5, v_activeTags_790_);
lean_closure_set(v___f_826_, 6, v_toBind_777_);
lean_closure_set(v___f_826_, 7, v_pushOutput_815_);
lean_closure_set(v___f_826_, 8, v___x_825_);
v___x_827_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_828_ = lean_nat_sub(v_w_764_, v___x_827_);
lean_dec(v_w_764_);
v___x_829_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_783_, v_tail_784_, v_tail_778_, v___x_828_, v_inst_765_, v_inst_766_);
v___x_830_ = lean_apply_4(v_toBind_777_, lean_box(0), lean_box(0), v___x_829_, v___f_826_);
return v___x_830_;
}
}
}
case 2:
{
uint8_t v_force_831_; lean_object* v___f_832_; lean_object* v___f_833_; lean_object* v___f_834_; uint8_t v___y_839_; uint8_t v___x_843_; 
lean_inc_n(v_toBind_777_, 3);
lean_del_object(v___x_792_);
lean_del_object(v___x_786_);
lean_del_object(v___x_780_);
lean_dec(v_tail_778_);
v_force_831_ = lean_ctor_get_uint8(v_f_788_, 0);
lean_dec_ref(v_f_788_);
lean_inc_ref_n(v_inst_766_, 3);
v___f_832_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_832_, 0, v_gs_x27_795_);
lean_closure_set(v___f_832_, 1, v_tail_784_);
lean_closure_set(v___f_832_, 2, v_w_764_);
lean_closure_set(v___f_832_, 3, v_inst_765_);
lean_closure_set(v___f_832_, 4, v_inst_766_);
lean_inc_ref(v___f_832_);
lean_inc(v_activeTags_790_);
v___f_833_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9), 5, 4);
lean_closure_set(v___f_833_, 0, v_inst_766_);
lean_closure_set(v___f_833_, 1, v_activeTags_790_);
lean_closure_set(v___f_833_, 2, v_toBind_777_);
lean_closure_set(v___f_833_, 3, v___f_832_);
lean_inc_ref(v___f_833_);
v___f_834_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_834_, 0, v_indent_789_);
lean_closure_set(v___f_834_, 1, v_inst_766_);
lean_closure_set(v___f_834_, 2, v_toBind_777_);
lean_closure_set(v___f_834_, 3, v___f_833_);
lean_closure_set(v___f_834_, 4, v___f_833_);
v___x_843_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_782_);
lean_dec(v_fla_782_);
if (v___x_843_ == 0)
{
v___y_839_ = v___x_843_;
goto v___jp_838_;
}
else
{
if (v_force_831_ == 0)
{
v___y_839_ = v___x_843_;
goto v___jp_838_;
}
else
{
lean_dec_ref(v___f_832_);
lean_dec(v_activeTags_790_);
goto v___jp_835_;
}
}
v___jp_835_:
{
lean_object* v_currColumn_836_; lean_object* v___x_837_; 
v_currColumn_836_ = lean_ctor_get(v_inst_766_, 2);
lean_inc(v_currColumn_836_);
lean_dec_ref(v_inst_766_);
v___x_837_ = lean_apply_4(v_toBind_777_, lean_box(0), lean_box(0), v_currColumn_836_, v___f_834_);
return v___x_837_;
}
v___jp_838_:
{
if (v___y_839_ == 0)
{
lean_dec_ref(v___f_832_);
lean_dec(v_activeTags_790_);
goto v___jp_835_;
}
else
{
lean_object* v_endTags_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec_ref(v___f_834_);
v_endTags_840_ = lean_ctor_get(v_inst_766_, 4);
lean_inc(v_endTags_840_);
lean_dec_ref(v_inst_766_);
v___x_841_ = lean_apply_1(v_endTags_840_, v_activeTags_790_);
v___x_842_ = lean_apply_4(v_toBind_777_, lean_box(0), lean_box(0), v___x_841_, v___f_832_);
return v___x_842_;
}
}
}
case 3:
{
lean_object* v_a_844_; uint32_t v___x_845_; lean_object* v_p_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
lean_inc(v_toBind_777_);
lean_del_object(v___x_792_);
lean_del_object(v___x_786_);
lean_del_object(v___x_780_);
v_a_844_ = lean_ctor_get(v_f_788_, 0);
lean_inc_ref_n(v_a_844_, 2);
lean_dec_ref(v_f_788_);
v___x_845_ = 10;
v_p_846_ = lean_string_posof(v_a_844_, v___x_845_);
v___x_847_ = lean_string_utf8_byte_size(v_a_844_);
v___x_848_ = lean_nat_dec_eq(v_p_846_, v___x_847_);
if (v___x_848_ == 0)
{
lean_object* v_pushOutput_849_; lean_object* v_pushNewline_850_; lean_object* v___x_851_; lean_object* v___f_852_; lean_object* v___f_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v_pushOutput_849_ = lean_ctor_get(v_inst_766_, 0);
lean_inc(v_pushOutput_849_);
v_pushNewline_850_ = lean_ctor_get(v_inst_766_, 1);
lean_inc(v_pushNewline_850_);
v___x_851_ = lean_box(v_flb_783_);
lean_inc_n(v_toBind_777_, 2);
lean_inc(v_indent_789_);
lean_inc(v_p_846_);
lean_inc_ref(v_a_844_);
v___f_852_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed), 15, 14);
lean_closure_set(v___f_852_, 0, v_a_844_);
lean_closure_set(v___f_852_, 1, v_p_846_);
lean_closure_set(v___f_852_, 2, v___x_847_);
lean_closure_set(v___f_852_, 3, v_indent_789_);
lean_closure_set(v___f_852_, 4, v_activeTags_790_);
lean_closure_set(v___f_852_, 5, v_tail_784_);
lean_closure_set(v___f_852_, 6, v_fla_782_);
lean_closure_set(v___f_852_, 7, v___x_851_);
lean_closure_set(v___f_852_, 8, v_tail_778_);
lean_closure_set(v___f_852_, 9, v_w_764_);
lean_closure_set(v___f_852_, 10, v_inst_765_);
lean_closure_set(v___f_852_, 11, v_inst_766_);
lean_closure_set(v___f_852_, 12, v_toBind_777_);
lean_closure_set(v___f_852_, 13, v_gs_x27_795_);
v___f_853_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_853_, 0, v_indent_789_);
lean_closure_set(v___f_853_, 1, v_pushNewline_850_);
lean_closure_set(v___f_853_, 2, v_toBind_777_);
lean_closure_set(v___f_853_, 3, v___f_852_);
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = lean_string_utf8_extract(v_a_844_, v___x_854_, v_p_846_);
lean_dec(v_p_846_);
lean_dec_ref(v_a_844_);
v___x_856_ = lean_apply_1(v_pushOutput_849_, v___x_855_);
v___x_857_ = lean_apply_4(v_toBind_777_, lean_box(0), lean_box(0), v___x_856_, v___f_853_);
return v___x_857_;
}
else
{
lean_object* v_pushOutput_858_; lean_object* v_endTags_859_; lean_object* v___f_860_; lean_object* v___f_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec(v_p_846_);
lean_dec(v_indent_789_);
lean_dec(v_fla_782_);
lean_dec(v_tail_778_);
v_pushOutput_858_ = lean_ctor_get(v_inst_766_, 0);
lean_inc(v_pushOutput_858_);
v_endTags_859_ = lean_ctor_get(v_inst_766_, 4);
lean_inc(v_endTags_859_);
v___f_860_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_860_, 0, v_gs_x27_795_);
lean_closure_set(v___f_860_, 1, v_tail_784_);
lean_closure_set(v___f_860_, 2, v_w_764_);
lean_closure_set(v___f_860_, 3, v_inst_765_);
lean_closure_set(v___f_860_, 4, v_inst_766_);
lean_inc(v_toBind_777_);
v___f_861_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_861_, 0, v_endTags_859_);
lean_closure_set(v___f_861_, 1, v_activeTags_790_);
lean_closure_set(v___f_861_, 2, v_toBind_777_);
lean_closure_set(v___f_861_, 3, v___f_860_);
v___x_862_ = lean_apply_1(v_pushOutput_858_, v_a_844_);
v___x_863_ = lean_apply_4(v_toBind_777_, lean_box(0), lean_box(0), v___x_862_, v___f_861_);
return v___x_863_;
}
}
case 4:
{
lean_object* v_indent_864_; lean_object* v_f_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
lean_dec_ref(v_gs_x27_795_);
lean_del_object(v___x_780_);
v_indent_864_ = lean_ctor_get(v_f_788_, 0);
lean_inc(v_indent_864_);
v_f_865_ = lean_ctor_get(v_f_788_, 1);
lean_inc(v_f_865_);
lean_dec_ref(v_f_788_);
v___x_866_ = lean_int_add(v_indent_789_, v_indent_864_);
lean_dec(v_indent_864_);
lean_dec(v_indent_789_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 1, v___x_866_);
lean_ctor_set(v___x_792_, 0, v_f_865_);
v___x_868_ = v___x_792_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_f_865_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_874_, 2, v_activeTags_790_);
v___x_868_ = v_reuseFailAlloc_874_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_870_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_868_);
v___x_870_ = v___x_786_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_tail_784_);
v___x_870_ = v_reuseFailAlloc_873_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_871_; 
v___x_871_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_782_, v_flb_783_, v_tail_778_, v___x_870_);
v_x_767_ = v___x_871_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_875_; lean_object* v_a_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
lean_dec_ref(v_gs_x27_795_);
v_a_875_ = lean_ctor_get(v_f_788_, 0);
lean_inc(v_a_875_);
v_a_876_ = lean_ctor_get(v_f_788_, 1);
lean_inc(v_a_876_);
lean_dec_ref(v_f_788_);
v___x_877_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_789_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 2, v___x_877_);
lean_ctor_set(v___x_792_, 0, v_a_875_);
v___x_879_ = v___x_792_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_875_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_indent_789_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v___x_877_);
v___x_879_ = v_reuseFailAlloc_889_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_880_, 0, v_a_876_);
lean_ctor_set(v___x_880_, 1, v_indent_789_);
lean_ctor_set(v___x_880_, 2, v_activeTags_790_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_880_);
v___x_882_ = v___x_786_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_tail_784_);
v___x_882_ = v_reuseFailAlloc_888_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; 
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 1, v___x_882_);
lean_ctor_set(v___x_780_, 0, v___x_879_);
v___x_884_ = v___x_780_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_882_);
v___x_884_ = v_reuseFailAlloc_887_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_885_; 
v___x_885_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_782_, v_flb_783_, v_tail_778_, v___x_884_);
v_x_767_ = v___x_885_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_890_; uint8_t v_behavior_891_; uint8_t v___x_892_; 
lean_dec_ref(v_gs_x27_795_);
lean_del_object(v___x_780_);
v_a_890_ = lean_ctor_get(v_f_788_, 0);
lean_inc(v_a_890_);
v_behavior_891_ = lean_ctor_get_uint8(v_f_788_, sizeof(void*)*1);
lean_dec_ref(v_f_788_);
v___x_892_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_782_);
if (v___x_892_ == 0)
{
lean_object* v___x_894_; 
lean_inc(v_toBind_777_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v_a_890_);
v___x_894_ = v___x_792_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_890_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_indent_789_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_activeTags_790_);
v___x_894_ = v_reuseFailAlloc_903_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = lean_box(0);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 1, v___x_895_);
lean_ctor_set(v___x_786_, 0, v___x_894_);
v___x_897_ = v___x_786_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v___x_895_);
v___x_897_ = v_reuseFailAlloc_902_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_898_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_782_, v_flb_783_, v_tail_778_, v_tail_784_);
lean_inc_ref(v_inst_766_);
lean_inc_ref(v_inst_765_);
lean_inc(v_w_764_);
v___x_899_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_behavior_891_, v___x_897_, v___x_898_, v_w_764_, v_inst_765_, v_inst_766_);
v___x_900_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_900_, 0, v_w_764_);
lean_closure_set(v___x_900_, 1, v_inst_765_);
lean_closure_set(v___x_900_, 2, v_inst_766_);
v___x_901_ = lean_apply_4(v_toBind_777_, lean_box(0), lean_box(0), v___x_899_, v___x_900_);
return v___x_901_;
}
}
}
else
{
lean_object* v___x_905_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v_a_890_);
v___x_905_ = v___x_792_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_890_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_indent_789_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v_activeTags_790_);
v___x_905_ = v_reuseFailAlloc_911_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_907_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_905_);
v___x_907_ = v___x_786_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_tail_784_);
v___x_907_ = v_reuseFailAlloc_910_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; 
v___x_908_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_782_, v_flb_783_, v_tail_778_, v___x_907_);
v_x_767_ = v___x_908_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_912_; lean_object* v_a_913_; lean_object* v_startTag_914_; lean_object* v___f_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
lean_inc(v_toBind_777_);
lean_del_object(v___x_792_);
lean_del_object(v___x_786_);
lean_dec(v_fla_782_);
lean_del_object(v___x_780_);
lean_dec(v_tail_778_);
v_a_912_ = lean_ctor_get(v_f_788_, 0);
lean_inc(v_a_912_);
v_a_913_ = lean_ctor_get(v_f_788_, 1);
lean_inc(v_a_913_);
lean_dec_ref(v_f_788_);
v_startTag_914_ = lean_ctor_get(v_inst_766_, 3);
lean_inc(v_startTag_914_);
v___f_915_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed), 9, 8);
lean_closure_set(v___f_915_, 0, v_activeTags_790_);
lean_closure_set(v___f_915_, 1, v_a_913_);
lean_closure_set(v___f_915_, 2, v_indent_789_);
lean_closure_set(v___f_915_, 3, v_tail_784_);
lean_closure_set(v___f_915_, 4, v_gs_x27_795_);
lean_closure_set(v___f_915_, 5, v_w_764_);
lean_closure_set(v___f_915_, 6, v_inst_765_);
lean_closure_set(v___f_915_, 7, v_inst_766_);
v___x_916_ = lean_apply_1(v_startTag_914_, v_a_912_);
v___x_917_ = lean_apply_4(v_toBind_777_, lean_box(0), lean_box(0), v___x_916_, v___f_915_);
return v___x_917_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4(lean_object* v_w_923_, lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_____x_926_, lean_object* v_____r_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_923_, v_inst_924_, v_inst_925_, v_____x_926_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be(lean_object* v_m_929_, lean_object* v_w_930_, lean_object* v_inst_931_, lean_object* v_inst_932_, lean_object* v_x_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_930_, v_inst_931_, v_inst_932_, v_x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___redArg(lean_object* v_f_935_, lean_object* v_w_936_, lean_object* v_indent_937_, lean_object* v_inst_938_, lean_object* v_inst_939_){
_start:
{
lean_object* v___x_940_; uint8_t v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_940_ = lean_box(1);
v___x_941_ = 0;
v___x_942_ = lean_nat_to_int(v_indent_937_);
v___x_943_ = lean_unsigned_to_nat(0u);
v___x_944_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_944_, 0, v_f_935_);
lean_ctor_set(v___x_944_, 1, v___x_942_);
lean_ctor_set(v___x_944_, 2, v___x_943_);
v___x_945_ = lean_box(0);
v___x_946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_947_, 0, v___x_940_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*2, v___x_941_);
v___x_948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set(v___x_948_, 1, v___x_945_);
v___x_949_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_936_, v_inst_938_, v_inst_939_, v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM(lean_object* v_m_950_, lean_object* v_f_951_, lean_object* v_w_952_, lean_object* v_indent_953_, lean_object* v_inst_954_, lean_object* v_inst_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Std_Format_prettyM___redArg(v_f_951_, v_w_952_, v_indent_953_, v_inst_954_, v_inst_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_bracket(lean_object* v_l_957_, lean_object* v_f_958_, lean_object* v_r_959_){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; lean_object* v___x_968_; 
v___x_960_ = lean_string_length(v_l_957_);
v___x_961_ = lean_nat_to_int(v___x_960_);
v___x_962_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_962_, 0, v_l_957_);
v___x_963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v_f_958_);
v___x_964_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_964_, 0, v_r_959_);
v___x_965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_961_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = 0;
v___x_968_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set_uint8(v___x_968_, sizeof(void*)*1, v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l_Std_Format_paren___closed__2(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l_Std_Format_paren___closed__0));
v___x_972_ = lean_string_length(v___x_971_);
return v___x_972_;
}
}
static lean_object* _init_l_Std_Format_paren___closed__3(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_obj_once(&l_Std_Format_paren___closed__2, &l_Std_Format_paren___closed__2_once, _init_l_Std_Format_paren___closed__2);
v___x_974_ = lean_nat_to_int(v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_paren(lean_object* v_f_979_){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; lean_object* v___x_987_; 
v___x_980_ = lean_obj_once(&l_Std_Format_paren___closed__3, &l_Std_Format_paren___closed__3_once, _init_l_Std_Format_paren___closed__3);
v___x_981_ = ((lean_object*)(l_Std_Format_paren___closed__4));
v___x_982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v_f_979_);
v___x_983_ = ((lean_object*)(l_Std_Format_paren___closed__5));
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_980_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = 0;
v___x_987_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*1, v___x_986_);
return v___x_987_;
}
}
static lean_object* _init_l_Std_Format_sbracket___closed__2(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_Std_Format_sbracket___closed__0));
v___x_991_ = lean_string_length(v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l_Std_Format_sbracket___closed__3(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = lean_obj_once(&l_Std_Format_sbracket___closed__2, &l_Std_Format_sbracket___closed__2_once, _init_l_Std_Format_sbracket___closed__2);
v___x_993_ = lean_nat_to_int(v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_sbracket(lean_object* v_f_998_){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; lean_object* v___x_1006_; 
v___x_999_ = lean_obj_once(&l_Std_Format_sbracket___closed__3, &l_Std_Format_sbracket___closed__3_once, _init_l_Std_Format_sbracket___closed__3);
v___x_1000_ = ((lean_object*)(l_Std_Format_sbracket___closed__4));
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v_f_998_);
v___x_1002_ = ((lean_object*)(l_Std_Format_sbracket___closed__5));
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_999_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = 0;
v___x_1006_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1006_, 0, v___x_1004_);
lean_ctor_set_uint8(v___x_1006_, sizeof(void*)*1, v___x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_bracketFill(lean_object* v_l_1007_, lean_object* v_f_1008_, lean_object* v_r_1009_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1010_ = lean_string_length(v_l_1007_);
v___x_1011_ = lean_nat_to_int(v___x_1010_);
v___x_1012_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1012_, 0, v_l_1007_);
v___x_1013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v_f_1008_);
v___x_1014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1014_, 0, v_r_1009_);
v___x_1015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1011_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = l_Std_Format_fill(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l_Std_Format_defIndent(void){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_unsigned_to_nat(2u);
return v___x_1018_;
}
}
static uint8_t _init_l_Std_Format_defUnicode(void){
_start:
{
uint8_t v___x_1019_; 
v___x_1019_ = 1;
return v___x_1019_;
}
}
static lean_object* _init_l_Std_Format_defWidth(void){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_unsigned_to_nat(120u);
return v___x_1020_;
}
}
static lean_object* _init_l_Std_Format_nestD___closed__0(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_unsigned_to_nat(2u);
v___x_1022_ = lean_nat_to_int(v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nestD(lean_object* v_f_1023_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_obj_once(&l_Std_Format_nestD___closed__0, &l_Std_Format_nestD___closed__0_once, _init_l_Std_Format_nestD___closed__0);
v___x_1025_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v_f_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_indentD(lean_object* v_f_1026_){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = lean_box(1);
v___x_1028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v_f_1026_);
v___x_1029_ = l_Std_Format_nestD(v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(lean_object* v_s_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_out_1032_; lean_object* v_column_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1045_; 
v_out_1032_ = lean_ctor_get(v___y_1031_, 0);
v_column_1033_ = lean_ctor_get(v___y_1031_, 1);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___y_1031_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1035_ = v___y_1031_;
v_isShared_1036_ = v_isSharedCheck_1045_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_column_1033_);
lean_inc(v_out_1032_);
lean_dec(v___y_1031_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1045_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1037_ = lean_box(0);
v___x_1038_ = lean_string_append(v_out_1032_, v_s_1030_);
v___x_1039_ = lean_string_length(v_s_1030_);
v___x_1040_ = lean_nat_add(v_column_1033_, v___x_1039_);
lean_dec(v___x_1039_);
lean_dec(v_column_1033_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 1, v___x_1040_);
lean_ctor_set(v___x_1035_, 0, v___x_1038_);
v___x_1042_ = v___x_1035_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1037_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
return v___x_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0___boxed(lean_object* v_s_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(v_s_1046_, v___y_1047_);
lean_dec_ref(v_s_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1(lean_object* v_indent_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_out_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1065_; 
v_out_1052_ = lean_ctor_get(v___y_1051_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___y_1051_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; 
v_unused_1066_ = lean_ctor_get(v___y_1051_, 1);
lean_dec(v_unused_1066_);
v___x_1054_ = v___y_1051_;
v_isShared_1055_ = v_isSharedCheck_1065_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_out_1052_);
lean_dec(v___y_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1065_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; uint32_t v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1056_ = lean_box(0);
v___x_1057_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1058_ = 32;
lean_inc(v_indent_1050_);
v___x_1059_ = lean_string_pushn(v___x_1057_, v___x_1058_, v_indent_1050_);
v___x_1060_ = lean_string_append(v_out_1052_, v___x_1059_);
lean_dec_ref(v___x_1059_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v_indent_1050_);
lean_ctor_set(v___x_1054_, 0, v___x_1060_);
v___x_1062_ = v___x_1054_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_indent_1050_);
v___x_1062_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1056_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
return v___x_1063_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__2(lean_object* v_____do__lift_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_column_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
v_column_1069_ = lean_ctor_get(v_____do__lift_1067_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_____do__lift_1067_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v_____do__lift_1067_, 0);
lean_dec(v_unused_1077_);
v___x_1071_ = v_____do__lift_1067_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_column_1069_);
lean_dec(v_____do__lift_1067_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v___y_1068_);
lean_ctor_set(v___x_1071_, 0, v_column_1069_);
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_column_1069_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___y_1068_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(lean_object* v_x_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_box(0);
v___x_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v___y_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3___boxed(lean_object* v_x_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(v_x_1082_, v___y_1083_);
lean_dec(v_x_1082_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(uint8_t v_flb_1120_, lean_object* v_items_1121_, lean_object* v_gs_1122_, lean_object* v_w_1123_, lean_object* v___y_1124_){
_start:
{
uint8_t v___y_1126_; lean_object* v_column_1131_; uint8_t v___x_1132_; uint8_t v___x_1133_; lean_object* v___x_1134_; lean_object* v_g_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v_r_1139_; lean_object* v___y_1141_; uint8_t v_foundLine_1146_; lean_object* v_space_1147_; uint8_t v___y_1149_; uint8_t v___x_1163_; 
v_column_1131_ = lean_ctor_get(v___y_1124_, 1);
v___x_1132_ = 0;
v___x_1133_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_1120_, v___x_1132_);
v___x_1134_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1134_, 0, v___x_1133_);
lean_inc(v_items_1121_);
v_g_1135_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_1135_, 0, v___x_1134_);
lean_ctor_set(v_g_1135_, 1, v_items_1121_);
lean_ctor_set_uint8(v_g_1135_, sizeof(void*)*2, v_flb_1120_);
v___x_1136_ = lean_box(0);
v___x_1137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1137_, 0, v_g_1135_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = lean_nat_sub(v_w_1123_, v_column_1131_);
lean_inc(v___x_1138_);
lean_inc(v_column_1131_);
v_r_1139_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_1137_, v_column_1131_, v___x_1138_);
v_foundLine_1146_ = lean_ctor_get_uint8(v_r_1139_, sizeof(void*)*1);
v_space_1147_ = lean_ctor_get(v_r_1139_, 0);
lean_inc(v_space_1147_);
v___x_1163_ = lean_nat_dec_lt(v___x_1138_, v_space_1147_);
if (v___x_1163_ == 0)
{
v___y_1149_ = v_foundLine_1146_;
goto v___jp_1148_;
}
else
{
v___y_1149_ = v___x_1163_;
goto v___jp_1148_;
}
v___jp_1125_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1127_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1127_, 0, v___y_1126_);
v___x_1128_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v_items_1121_);
lean_ctor_set_uint8(v___x_1128_, sizeof(void*)*2, v_flb_1120_);
v___x_1129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v_gs_1122_);
v___x_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
lean_ctor_set(v___x_1130_, 1, v___y_1124_);
return v___x_1130_;
}
v___jp_1140_:
{
uint8_t v_foundFlattenedHardLine_1142_; 
v_foundFlattenedHardLine_1142_ = lean_ctor_get_uint8(v_r_1139_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_1139_);
if (v_foundFlattenedHardLine_1142_ == 0)
{
lean_object* v_space_1143_; uint8_t v___x_1144_; 
v_space_1143_ = lean_ctor_get(v___y_1141_, 0);
lean_inc(v_space_1143_);
lean_dec_ref(v___y_1141_);
v___x_1144_ = lean_nat_dec_le(v_space_1143_, v___x_1138_);
lean_dec(v___x_1138_);
lean_dec(v_space_1143_);
v___y_1126_ = v___x_1144_;
goto v___jp_1125_;
}
else
{
uint8_t v___x_1145_; 
lean_dec_ref(v___y_1141_);
lean_dec(v___x_1138_);
v___x_1145_ = 0;
v___y_1126_ = v___x_1145_;
goto v___jp_1125_;
}
}
v___jp_1148_:
{
if (v___y_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v_r_u2082_1151_; uint8_t v_foundLine_1152_; uint8_t v_foundFlattenedHardLine_1153_; lean_object* v_space_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1162_; 
v___x_1150_ = lean_nat_sub(v___x_1138_, v_space_1147_);
lean_inc(v_column_1131_);
lean_inc(v_gs_1122_);
v_r_u2082_1151_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_1122_, v_column_1131_, v___x_1150_);
v_foundLine_1152_ = lean_ctor_get_uint8(v_r_u2082_1151_, sizeof(void*)*1);
v_foundFlattenedHardLine_1153_ = lean_ctor_get_uint8(v_r_u2082_1151_, sizeof(void*)*1 + 1);
v_space_1154_ = lean_ctor_get(v_r_u2082_1151_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_r_u2082_1151_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1156_ = v_r_u2082_1151_;
v_isShared_1157_ = v_isSharedCheck_1162_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_space_1154_);
lean_dec(v_r_u2082_1151_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1162_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1158_ = lean_nat_add(v_space_1147_, v_space_1154_);
lean_dec(v_space_1154_);
lean_dec(v_space_1147_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v___x_1158_);
v___x_1160_ = v___x_1156_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*1, v_foundLine_1152_);
lean_ctor_set_uint8(v_reuseFailAlloc_1161_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_1153_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
v___y_1141_ = v___x_1160_;
goto v___jp_1140_;
}
}
}
else
{
lean_dec(v_space_1147_);
lean_inc_ref(v_r_1139_);
v___y_1141_ = v_r_1139_;
goto v___jp_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1___boxed(lean_object* v_flb_1164_, lean_object* v_items_1165_, lean_object* v_gs_1166_, lean_object* v_w_1167_, lean_object* v___y_1168_){
_start:
{
uint8_t v_flb_boxed_1169_; lean_object* v_res_1170_; 
v_flb_boxed_1169_ = lean_unbox(v_flb_1164_);
v_res_1170_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_boxed_1169_, v_items_1165_, v_gs_1166_, v_w_1167_, v___y_1168_);
lean_dec(v_w_1167_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(lean_object* v_msg_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___f_1187_; lean_object* v___f_1188_; lean_object* v___f_1189_; lean_object* v___f_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_4858__overap_1199_; lean_object* v___x_1200_; 
v___f_1187_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0));
v___f_1188_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1));
v___f_1189_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2));
v___f_1190_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3));
v___x_1191_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4));
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v___f_1187_);
v___x_1193_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5));
v___x_1194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1192_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
lean_ctor_set(v___x_1194_, 2, v___f_1188_);
lean_ctor_set(v___x_1194_, 3, v___f_1189_);
lean_ctor_set(v___x_1194_, 4, v___f_1190_);
v___x_1195_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6));
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1194_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = lean_box(0);
v___x_1198_ = l_instInhabitedOfMonad___redArg(v___x_1196_, v___x_1197_);
v___x_4858__overap_1199_ = lean_panic_fn_borrowed(v___x_1198_, v_msg_1185_);
lean_dec(v___x_1198_);
v___x_1200_ = lean_apply_1(v___x_4858__overap_1199_, v___y_1186_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(lean_object* v_w_1201_, lean_object* v_x_1202_, lean_object* v___y_1203_){
_start:
{
if (lean_obj_tag(v_x_1202_) == 0)
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
lean_ctor_set(v___x_1205_, 1, v___y_1203_);
return v___x_1205_;
}
else
{
lean_object* v_head_1206_; lean_object* v_items_1207_; 
v_head_1206_ = lean_ctor_get(v_x_1202_, 0);
v_items_1207_ = lean_ctor_get(v_head_1206_, 1);
lean_inc(v_items_1207_);
if (lean_obj_tag(v_items_1207_) == 0)
{
lean_object* v_tail_1208_; 
v_tail_1208_ = lean_ctor_get(v_x_1202_, 1);
lean_inc(v_tail_1208_);
lean_dec_ref(v_x_1202_);
v_x_1202_ = v_tail_1208_;
goto _start;
}
else
{
lean_object* v_head_1210_; lean_object* v_tail_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1481_; 
lean_inc(v_head_1206_);
v_head_1210_ = lean_ctor_get(v_items_1207_, 0);
lean_inc(v_head_1210_);
v_tail_1211_ = lean_ctor_get(v_x_1202_, 1);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_x_1202_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; 
v_unused_1482_ = lean_ctor_get(v_x_1202_, 0);
lean_dec(v_unused_1482_);
v___x_1213_ = v_x_1202_;
v_isShared_1214_ = v_isSharedCheck_1481_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_tail_1211_);
lean_dec(v_x_1202_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1481_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v_fla_1215_; uint8_t v_flb_1216_; lean_object* v_tail_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1479_; 
v_fla_1215_ = lean_ctor_get(v_head_1206_, 0);
lean_inc(v_fla_1215_);
v_flb_1216_ = lean_ctor_get_uint8(v_head_1206_, sizeof(void*)*2);
lean_dec(v_head_1206_);
v_tail_1217_ = lean_ctor_get(v_items_1207_, 1);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_items_1207_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; 
v_unused_1480_ = lean_ctor_get(v_items_1207_, 0);
lean_dec(v_unused_1480_);
v___x_1219_ = v_items_1207_;
v_isShared_1220_ = v_isSharedCheck_1479_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_tail_1217_);
lean_dec(v_items_1207_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1479_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v_f_1221_; lean_object* v_indent_1222_; lean_object* v_activeTags_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1478_; 
v_f_1221_ = lean_ctor_get(v_head_1210_, 0);
v_indent_1222_ = lean_ctor_get(v_head_1210_, 1);
v_activeTags_1223_ = lean_ctor_get(v_head_1210_, 2);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_head_1210_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1225_ = v_head_1210_;
v_isShared_1226_ = v_isSharedCheck_1478_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_activeTags_1223_);
lean_inc(v_indent_1222_);
lean_inc(v_f_1221_);
lean_dec(v_head_1210_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1478_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
uint8_t v___y_1260_; 
switch(lean_obj_tag(v_f_1221_))
{
case 0:
{
lean_object* v___x_1263_; 
lean_del_object(v___x_1225_);
lean_dec(v_activeTags_1223_);
lean_dec(v_indent_1222_);
lean_del_object(v___x_1219_);
lean_del_object(v___x_1213_);
v___x_1263_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1215_, v_flb_1216_, v_tail_1211_, v_tail_1217_);
v_x_1202_ = v___x_1263_;
goto _start;
}
case 1:
{
lean_del_object(v___x_1225_);
lean_dec(v_activeTags_1223_);
lean_del_object(v___x_1219_);
lean_del_object(v___x_1213_);
if (v_flb_1216_ == 0)
{
uint8_t v___x_1265_; 
v___x_1265_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1215_);
if (v___x_1265_ == 0)
{
lean_object* v_out_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1280_; 
v_out_1266_ = lean_ctor_get(v___y_1203_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___y_1203_);
if (v_isSharedCheck_1280_ == 0)
{
lean_object* v_unused_1281_; 
v_unused_1281_ = lean_ctor_get(v___y_1203_, 1);
lean_dec(v_unused_1281_);
v___x_1268_ = v___y_1203_;
v_isShared_1269_ = v_isSharedCheck_1280_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_out_1266_);
lean_dec(v___y_1203_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1280_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; uint32_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1270_ = l_Int_toNat(v_indent_1222_);
lean_dec(v_indent_1222_);
v___x_1271_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1272_ = 32;
lean_inc(v___x_1270_);
v___x_1273_ = lean_string_pushn(v___x_1271_, v___x_1272_, v___x_1270_);
v___x_1274_ = lean_string_append(v_out_1266_, v___x_1273_);
lean_dec_ref(v___x_1273_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v___x_1270_);
lean_ctor_set(v___x_1268_, 0, v___x_1274_);
v___x_1276_ = v___x_1268_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v___x_1270_);
v___x_1276_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1277_; 
v___x_1277_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1215_, v_flb_1216_, v_tail_1211_, v_tail_1217_);
v_x_1202_ = v___x_1277_;
v___y_1203_ = v___x_1276_;
goto _start;
}
}
}
else
{
lean_object* v_out_1282_; lean_object* v_column_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1296_; 
lean_dec(v_indent_1222_);
v_out_1282_ = lean_ctor_get(v___y_1203_, 0);
v_column_1283_ = lean_ctor_get(v___y_1203_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___y_1203_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1285_ = v___y_1203_;
v_isShared_1286_ = v_isSharedCheck_1296_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_column_1283_);
lean_inc(v_out_1282_);
lean_dec(v___y_1203_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1296_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1287_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_1288_ = lean_string_append(v_out_1282_, v___x_1287_);
v___x_1289_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_1290_ = lean_nat_add(v_column_1283_, v___x_1289_);
lean_dec(v_column_1283_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1290_);
lean_ctor_set(v___x_1285_, 0, v___x_1288_);
v___x_1292_ = v___x_1285_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1293_; 
v___x_1293_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1215_, v_flb_1216_, v_tail_1211_, v_tail_1217_);
v_x_1202_ = v___x_1293_;
v___y_1203_ = v___x_1292_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = l_Int_toNat(v_indent_1222_);
lean_dec(v_indent_1222_);
v___x_1298_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1215_);
lean_dec(v_fla_1215_);
if (v___x_1298_ == 0)
{
lean_object* v_out_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1314_; 
v_out_1299_ = lean_ctor_get(v___y_1203_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___y_1203_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v___y_1203_, 1);
lean_dec(v_unused_1315_);
v___x_1301_ = v___y_1203_;
v_isShared_1302_ = v_isSharedCheck_1314_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_out_1299_);
lean_dec(v___y_1203_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1314_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; uint32_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1303_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1304_ = 32;
lean_inc(v___x_1297_);
v___x_1305_ = lean_string_pushn(v___x_1303_, v___x_1304_, v___x_1297_);
v___x_1306_ = lean_string_append(v_out_1299_, v___x_1305_);
lean_dec_ref(v___x_1305_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 1, v___x_1297_);
lean_ctor_set(v___x_1301_, 0, v___x_1306_);
v___x_1308_ = v___x_1301_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v___x_1297_);
v___x_1308_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1309_; lean_object* v_fst_1310_; lean_object* v_snd_1311_; 
v___x_1309_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1216_, v_tail_1217_, v_tail_1211_, v_w_1201_, v___x_1308_);
v_fst_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_fst_1310_);
v_snd_1311_ = lean_ctor_get(v___x_1309_, 1);
lean_inc(v_snd_1311_);
lean_dec_ref(v___x_1309_);
v_x_1202_ = v_fst_1310_;
v___y_1203_ = v_snd_1311_;
goto _start;
}
}
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v_fst_1320_; 
v___x_1316_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_1317_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_1318_ = lean_nat_sub(v_w_1201_, v___x_1317_);
lean_inc(v_tail_1211_);
lean_inc(v_tail_1217_);
v___x_1319_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1216_, v_tail_1217_, v_tail_1211_, v___x_1318_, v___y_1203_);
lean_dec(v___x_1318_);
v_fst_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_fst_1320_);
if (lean_obj_tag(v_fst_1320_) == 1)
{
lean_object* v_head_1321_; lean_object* v_snd_1322_; lean_object* v_fla_1323_; uint8_t v___x_1324_; 
v_head_1321_ = lean_ctor_get(v_fst_1320_, 0);
v_snd_1322_ = lean_ctor_get(v___x_1319_, 1);
lean_inc(v_snd_1322_);
lean_dec_ref(v___x_1319_);
v_fla_1323_ = lean_ctor_get(v_head_1321_, 0);
v___x_1324_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1323_);
if (v___x_1324_ == 0)
{
lean_object* v_out_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref(v_fst_1320_);
v_out_1325_ = lean_ctor_get(v_snd_1322_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_snd_1322_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; 
v_unused_1341_ = lean_ctor_get(v_snd_1322_, 1);
lean_dec(v_unused_1341_);
v___x_1327_ = v_snd_1322_;
v_isShared_1328_ = v_isSharedCheck_1340_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_out_1325_);
lean_dec(v_snd_1322_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1340_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; uint32_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1329_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1330_ = 32;
lean_inc(v___x_1297_);
v___x_1331_ = lean_string_pushn(v___x_1329_, v___x_1330_, v___x_1297_);
v___x_1332_ = lean_string_append(v_out_1325_, v___x_1331_);
lean_dec_ref(v___x_1331_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v___x_1297_);
lean_ctor_set(v___x_1327_, 0, v___x_1332_);
v___x_1334_ = v___x_1327_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v___x_1297_);
v___x_1334_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1335_; lean_object* v_fst_1336_; lean_object* v_snd_1337_; 
v___x_1335_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1216_, v_tail_1217_, v_tail_1211_, v_w_1201_, v___x_1334_);
v_fst_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_fst_1336_);
v_snd_1337_ = lean_ctor_get(v___x_1335_, 1);
lean_inc(v_snd_1337_);
lean_dec_ref(v___x_1335_);
v_x_1202_ = v_fst_1336_;
v___y_1203_ = v_snd_1337_;
goto _start;
}
}
}
else
{
lean_object* v_out_1342_; lean_object* v_column_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1353_; 
lean_dec(v___x_1297_);
lean_dec(v_tail_1217_);
lean_dec(v_tail_1211_);
v_out_1342_ = lean_ctor_get(v_snd_1322_, 0);
v_column_1343_ = lean_ctor_get(v_snd_1322_, 1);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_snd_1322_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1345_ = v_snd_1322_;
v_isShared_1346_ = v_isSharedCheck_1353_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_column_1343_);
lean_inc(v_out_1342_);
lean_dec(v_snd_1322_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1353_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1347_ = lean_string_append(v_out_1342_, v___x_1316_);
v___x_1348_ = lean_nat_add(v_column_1343_, v___x_1317_);
lean_dec(v_column_1343_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 1, v___x_1348_);
lean_ctor_set(v___x_1345_, 0, v___x_1347_);
v___x_1350_ = v___x_1345_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
v_x_1202_ = v_fst_1320_;
v___y_1203_ = v___x_1350_;
goto _start;
}
}
}
}
else
{
lean_object* v_snd_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec(v_fst_1320_);
lean_dec(v___x_1297_);
lean_dec(v_tail_1217_);
lean_dec(v_tail_1211_);
v_snd_1354_ = lean_ctor_get(v___x_1319_, 1);
lean_inc(v_snd_1354_);
lean_dec_ref(v___x_1319_);
v___x_1355_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0));
v___x_1356_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(v___x_1355_, v_snd_1354_);
return v___x_1356_;
}
}
}
}
case 2:
{
uint8_t v_force_1357_; uint8_t v___x_1358_; 
lean_del_object(v___x_1225_);
lean_dec(v_activeTags_1223_);
lean_del_object(v___x_1219_);
lean_del_object(v___x_1213_);
v_force_1357_ = lean_ctor_get_uint8(v_f_1221_, 0);
lean_dec_ref(v_f_1221_);
v___x_1358_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1215_);
if (v___x_1358_ == 0)
{
v___y_1260_ = v___x_1358_;
goto v___jp_1259_;
}
else
{
if (v_force_1357_ == 0)
{
v___y_1260_ = v___x_1358_;
goto v___jp_1259_;
}
else
{
goto v___jp_1227_;
}
}
}
case 3:
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1417_; 
lean_del_object(v___x_1213_);
v_a_1359_ = lean_ctor_get(v_f_1221_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_f_1221_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1361_ = v_f_1221_;
v_isShared_1362_ = v_isSharedCheck_1417_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v_f_1221_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1417_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
uint32_t v___x_1363_; lean_object* v_p_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1363_ = 10;
lean_inc_ref(v_a_1359_);
v_p_1364_ = lean_string_posof(v_a_1359_, v___x_1363_);
v___x_1365_ = lean_string_utf8_byte_size(v_a_1359_);
v___x_1366_ = lean_nat_dec_eq(v_p_1364_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v_out_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1401_; 
v_out_1367_ = lean_ctor_get(v___y_1203_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___y_1203_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; 
v_unused_1402_ = lean_ctor_get(v___y_1203_, 1);
lean_dec(v_unused_1402_);
v___x_1369_ = v___y_1203_;
v_isShared_1370_ = v_isSharedCheck_1401_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_out_1367_);
lean_dec(v___y_1203_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1401_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; uint32_t v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1371_ = lean_unsigned_to_nat(0u);
v___x_1372_ = lean_string_utf8_extract(v_a_1359_, v___x_1371_, v_p_1364_);
v___x_1373_ = lean_string_append(v_out_1367_, v___x_1372_);
lean_dec_ref(v___x_1372_);
v___x_1374_ = l_Int_toNat(v_indent_1222_);
v___x_1375_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1376_ = 32;
lean_inc(v___x_1374_);
v___x_1377_ = lean_string_pushn(v___x_1375_, v___x_1376_, v___x_1374_);
v___x_1378_ = lean_string_append(v___x_1373_, v___x_1377_);
lean_dec_ref(v___x_1377_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v___x_1374_);
lean_ctor_set(v___x_1369_, 0, v___x_1378_);
v___x_1380_ = v___x_1369_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___x_1374_);
v___x_1380_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1381_ = lean_string_utf8_next(v_a_1359_, v_p_1364_);
lean_dec(v_p_1364_);
v___x_1382_ = lean_string_utf8_extract(v_a_1359_, v___x_1381_, v___x_1365_);
lean_dec(v___x_1381_);
lean_dec_ref(v_a_1359_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1382_);
v___x_1384_ = v___x_1361_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1386_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1384_);
v___x_1386_ = v___x_1225_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_indent_1222_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v_activeTags_1223_);
v___x_1386_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v_is_1388_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1386_);
v_is_1388_ = v___x_1219_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_tail_1217_);
v_is_1388_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1389_ = lean_box(1);
v___x_1390_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_1215_, v___x_1389_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v_fst_1392_; lean_object* v_snd_1393_; 
lean_dec(v_fla_1215_);
v___x_1391_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1216_, v_is_1388_, v_tail_1211_, v_w_1201_, v___x_1380_);
v_fst_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_fst_1392_);
v_snd_1393_ = lean_ctor_get(v___x_1391_, 1);
lean_inc(v_snd_1393_);
lean_dec_ref(v___x_1391_);
v_x_1202_ = v_fst_1392_;
v___y_1203_ = v_snd_1393_;
goto _start;
}
else
{
lean_object* v___x_1395_; 
v___x_1395_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1215_, v_flb_1216_, v_tail_1211_, v_is_1388_);
v_x_1202_ = v___x_1395_;
v___y_1203_ = v___x_1380_;
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
lean_object* v_out_1403_; lean_object* v_column_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1416_; 
lean_dec(v_p_1364_);
lean_del_object(v___x_1361_);
lean_del_object(v___x_1225_);
lean_dec(v_activeTags_1223_);
lean_dec(v_indent_1222_);
lean_del_object(v___x_1219_);
v_out_1403_ = lean_ctor_get(v___y_1203_, 0);
v_column_1404_ = lean_ctor_get(v___y_1203_, 1);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___y_1203_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1406_ = v___y_1203_;
v_isShared_1407_ = v_isSharedCheck_1416_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_column_1404_);
lean_inc(v_out_1403_);
lean_dec(v___y_1203_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1416_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1408_ = lean_string_append(v_out_1403_, v_a_1359_);
v___x_1409_ = lean_string_length(v_a_1359_);
lean_dec_ref(v_a_1359_);
v___x_1410_ = lean_nat_add(v_column_1404_, v___x_1409_);
lean_dec(v___x_1409_);
lean_dec(v_column_1404_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v___x_1410_);
lean_ctor_set(v___x_1406_, 0, v___x_1408_);
v___x_1412_ = v___x_1406_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1413_; 
v___x_1413_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1215_, v_flb_1216_, v_tail_1211_, v_tail_1217_);
v_x_1202_ = v___x_1413_;
v___y_1203_ = v___x_1412_;
goto _start;
}
}
}
}
}
case 4:
{
lean_object* v_indent_1418_; lean_object* v_f_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
lean_del_object(v___x_1213_);
v_indent_1418_ = lean_ctor_get(v_f_1221_, 0);
lean_inc(v_indent_1418_);
v_f_1419_ = lean_ctor_get(v_f_1221_, 1);
lean_inc(v_f_1419_);
lean_dec_ref(v_f_1221_);
v___x_1420_ = lean_int_add(v_indent_1222_, v_indent_1418_);
lean_dec(v_indent_1418_);
lean_dec(v_indent_1222_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 1, v___x_1420_);
lean_ctor_set(v___x_1225_, 0, v_f_1419_);
v___x_1422_ = v___x_1225_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_f_1419_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_activeTags_1223_);
v___x_1422_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1424_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1422_);
v___x_1424_ = v___x_1219_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_tail_1217_);
v___x_1424_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; 
v___x_1425_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1215_, v_flb_1216_, v_tail_1211_, v___x_1424_);
v_x_1202_ = v___x_1425_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_1429_; lean_object* v_a_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v_a_1429_ = lean_ctor_get(v_f_1221_, 0);
lean_inc(v_a_1429_);
v_a_1430_ = lean_ctor_get(v_f_1221_, 1);
lean_inc(v_a_1430_);
lean_dec_ref(v_f_1221_);
v___x_1431_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_1222_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 2, v___x_1431_);
lean_ctor_set(v___x_1225_, 0, v_a_1429_);
v___x_1433_ = v___x_1225_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1429_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_indent_1222_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1434_, 0, v_a_1430_);
lean_ctor_set(v___x_1434_, 1, v_indent_1222_);
lean_ctor_set(v___x_1434_, 2, v_activeTags_1223_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1434_);
v___x_1436_ = v___x_1219_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_tail_1217_);
v___x_1436_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1438_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 1, v___x_1436_);
lean_ctor_set(v___x_1213_, 0, v___x_1433_);
v___x_1438_ = v___x_1213_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1439_; 
v___x_1439_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1215_, v_flb_1216_, v_tail_1211_, v___x_1438_);
v_x_1202_ = v___x_1439_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_1444_; uint8_t v_behavior_1445_; uint8_t v___x_1446_; 
lean_del_object(v___x_1213_);
v_a_1444_ = lean_ctor_get(v_f_1221_, 0);
lean_inc(v_a_1444_);
v_behavior_1445_ = lean_ctor_get_uint8(v_f_1221_, sizeof(void*)*1);
lean_dec_ref(v_f_1221_);
v___x_1446_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1215_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1448_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v_a_1444_);
v___x_1448_ = v___x_1225_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1444_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_indent_1222_);
lean_ctor_set(v_reuseFailAlloc_1458_, 2, v_activeTags_1223_);
v___x_1448_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = lean_box(0);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 1, v___x_1449_);
lean_ctor_set(v___x_1219_, 0, v___x_1448_);
v___x_1451_ = v___x_1219_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v_fst_1454_; lean_object* v_snd_1455_; 
v___x_1452_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1215_, v_flb_1216_, v_tail_1211_, v_tail_1217_);
v___x_1453_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_behavior_1445_, v___x_1451_, v___x_1452_, v_w_1201_, v___y_1203_);
v_fst_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_fst_1454_);
v_snd_1455_ = lean_ctor_get(v___x_1453_, 1);
lean_inc(v_snd_1455_);
lean_dec_ref(v___x_1453_);
v_x_1202_ = v_fst_1454_;
v___y_1203_ = v_snd_1455_;
goto _start;
}
}
}
else
{
lean_object* v___x_1460_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v_a_1444_);
v___x_1460_ = v___x_1225_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1444_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_indent_1222_);
lean_ctor_set(v_reuseFailAlloc_1466_, 2, v_activeTags_1223_);
v___x_1460_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1462_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1460_);
v___x_1462_ = v___x_1219_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_tail_1217_);
v___x_1462_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; 
v___x_1463_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1215_, v_flb_1216_, v_tail_1211_, v___x_1462_);
v_x_1202_ = v___x_1463_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
lean_del_object(v___x_1213_);
v_a_1467_ = lean_ctor_get(v_f_1221_, 1);
lean_inc(v_a_1467_);
lean_dec_ref(v_f_1221_);
v___x_1468_ = lean_unsigned_to_nat(1u);
v___x_1469_ = lean_nat_add(v_activeTags_1223_, v___x_1468_);
lean_dec(v_activeTags_1223_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 2, v___x_1469_);
lean_ctor_set(v___x_1225_, 0, v_a_1467_);
v___x_1471_ = v___x_1225_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1467_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_indent_1222_);
lean_ctor_set(v_reuseFailAlloc_1477_, 2, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1473_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1471_);
v___x_1473_ = v___x_1219_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_tail_1217_);
v___x_1473_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
lean_object* v___x_1474_; 
v___x_1474_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1215_, v_flb_1216_, v_tail_1211_, v___x_1473_);
v_x_1202_ = v___x_1474_;
goto _start;
}
}
}
}
v___jp_1227_:
{
lean_object* v_out_1228_; lean_object* v_column_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1258_; 
v_out_1228_ = lean_ctor_get(v___y_1203_, 0);
v_column_1229_ = lean_ctor_get(v___y_1203_, 1);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___y_1203_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1231_ = v___y_1203_;
v_isShared_1232_ = v_isSharedCheck_1258_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_column_1229_);
lean_inc(v_out_1228_);
lean_dec(v___y_1203_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1258_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
lean_inc(v_column_1229_);
v___x_1233_ = lean_nat_to_int(v_column_1229_);
v___x_1234_ = lean_int_dec_lt(v___x_1233_, v_indent_1222_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; uint32_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
lean_dec(v___x_1233_);
lean_dec(v_column_1229_);
v___x_1235_ = l_Int_toNat(v_indent_1222_);
lean_dec(v_indent_1222_);
v___x_1236_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1237_ = 32;
lean_inc(v___x_1235_);
v___x_1238_ = lean_string_pushn(v___x_1236_, v___x_1237_, v___x_1235_);
v___x_1239_ = lean_string_append(v_out_1228_, v___x_1238_);
lean_dec_ref(v___x_1238_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1235_);
lean_ctor_set(v___x_1231_, 0, v___x_1239_);
v___x_1241_ = v___x_1231_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v___x_1235_);
v___x_1241_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1242_; 
v___x_1242_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1215_, v_flb_1216_, v_tail_1211_, v_tail_1217_);
v_x_1202_ = v___x_1242_;
v___y_1203_ = v___x_1241_;
goto _start;
}
}
else
{
lean_object* v___x_1245_; uint32_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1245_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_1246_ = 32;
v___x_1247_ = lean_int_sub(v_indent_1222_, v___x_1233_);
lean_dec(v___x_1233_);
lean_dec(v_indent_1222_);
v___x_1248_ = l_Int_toNat(v___x_1247_);
lean_dec(v___x_1247_);
v___x_1249_ = lean_string_pushn(v___x_1245_, v___x_1246_, v___x_1248_);
v___x_1250_ = lean_string_append(v_out_1228_, v___x_1249_);
v___x_1251_ = lean_string_length(v___x_1249_);
lean_dec_ref(v___x_1249_);
v___x_1252_ = lean_nat_add(v_column_1229_, v___x_1251_);
lean_dec(v___x_1251_);
lean_dec(v_column_1229_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1252_);
lean_ctor_set(v___x_1231_, 0, v___x_1250_);
v___x_1254_ = v___x_1231_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1255_; 
v___x_1255_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1215_, v_flb_1216_, v_tail_1211_, v_tail_1217_);
v_x_1202_ = v___x_1255_;
v___y_1203_ = v___x_1254_;
goto _start;
}
}
}
}
v___jp_1259_:
{
if (v___y_1260_ == 0)
{
goto v___jp_1227_;
}
else
{
lean_object* v___x_1261_; 
lean_dec(v_indent_1222_);
v___x_1261_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1215_, v_flb_1216_, v_tail_1211_, v_tail_1217_);
v_x_1202_ = v___x_1261_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0___boxed(lean_object* v_w_1483_, lean_object* v_x_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_1483_, v_x_1484_, v___y_1485_);
lean_dec(v_w_1483_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(lean_object* v_f_1487_, lean_object* v_w_1488_, lean_object* v_indent_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___x_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1491_ = lean_box(1);
v___x_1492_ = 0;
v___x_1493_ = lean_nat_to_int(v_indent_1489_);
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1495_, 0, v_f_1487_);
lean_ctor_set(v___x_1495_, 1, v___x_1493_);
lean_ctor_set(v___x_1495_, 2, v___x_1494_);
v___x_1496_ = lean_box(0);
v___x_1497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1495_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
v___x_1498_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1498_, 0, v___x_1491_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
lean_ctor_set_uint8(v___x_1498_, sizeof(void*)*2, v___x_1492_);
v___x_1499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
lean_ctor_set(v___x_1499_, 1, v___x_1496_);
v___x_1500_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_1488_, v___x_1499_, v___y_1490_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0___boxed(lean_object* v_f_1501_, lean_object* v_w_1502_, lean_object* v_indent_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(v_f_1501_, v_w_1502_, v_indent_1503_, v___y_1504_);
lean_dec(v_w_1502_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty(lean_object* v_f_1506_, lean_object* v_width_1507_, lean_object* v_indent_1508_, lean_object* v_column_1509_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v_snd_1513_; lean_object* v_out_1514_; 
v___x_1510_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
lean_ctor_set(v___x_1511_, 1, v_column_1509_);
v___x_1512_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(v_f_1506_, v_width_1507_, v_indent_1508_, v___x_1511_);
v_snd_1513_ = lean_ctor_get(v___x_1512_, 1);
lean_inc(v_snd_1513_);
lean_dec_ref(v___x_1512_);
v_out_1514_ = lean_ctor_get(v_snd_1513_, 0);
lean_inc_ref(v_out_1514_);
lean_dec(v_snd_1513_);
return v_out_1514_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty___boxed(lean_object* v_f_1515_, lean_object* v_width_1516_, lean_object* v_indent_1517_, lean_object* v_column_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Std_Format_pretty(v_f_1515_, v_width_1516_, v_indent_1517_, v_column_1518_);
lean_dec(v_width_1516_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0(lean_object* v_f_1520_){
_start:
{
lean_inc(v_f_1520_);
return v_f_1520_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object* v_f_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Std_instToFormatFormat___lam__0(v_f_1521_);
lean_dec(v_f_1521_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatString___lam__0(lean_object* v_s_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1526_, 0, v_s_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg___lam__0(lean_object* v_x_1529_, lean_object* v_inst_1530_, lean_object* v_x1_1531_, lean_object* v_x2_1532_){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1533_, 0, v_x1_1531_);
lean_ctor_set(v___x_1533_, 1, v_x_1529_);
v___x_1534_ = lean_apply_1(v_inst_1530_, v_x2_1532_);
v___x_1535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg(lean_object* v_inst_1536_, lean_object* v_x_1537_, lean_object* v_x_1538_){
_start:
{
if (lean_obj_tag(v_x_1537_) == 0)
{
lean_object* v___x_1539_; 
lean_dec(v_x_1538_);
lean_dec_ref(v_inst_1536_);
v___x_1539_ = lean_box(0);
return v___x_1539_;
}
else
{
lean_object* v_tail_1540_; 
v_tail_1540_ = lean_ctor_get(v_x_1537_, 1);
if (lean_obj_tag(v_tail_1540_) == 0)
{
lean_object* v_head_1541_; lean_object* v___x_1542_; 
lean_dec(v_x_1538_);
v_head_1541_ = lean_ctor_get(v_x_1537_, 0);
lean_inc(v_head_1541_);
lean_dec_ref(v_x_1537_);
v___x_1542_ = lean_apply_1(v_inst_1536_, v_head_1541_);
return v___x_1542_;
}
else
{
lean_object* v_head_1543_; lean_object* v___f_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_inc(v_tail_1540_);
v_head_1543_ = lean_ctor_get(v_x_1537_, 0);
lean_inc(v_head_1543_);
lean_dec_ref(v_x_1537_);
lean_inc_ref(v_inst_1536_);
v___f_1544_ = lean_alloc_closure((void*)(l_Std_Format_joinSep___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1544_, 0, v_x_1538_);
lean_closure_set(v___f_1544_, 1, v_inst_1536_);
v___x_1545_ = lean_apply_1(v_inst_1536_, v_head_1543_);
v___x_1546_ = l_List_foldl___redArg(v___f_1544_, v___x_1545_, v_tail_1540_);
return v___x_1546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep(lean_object* v_00_u03b1_1547_, lean_object* v_inst_1548_, lean_object* v_x_1549_, lean_object* v_x_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Std_Format_joinSep___redArg(v_inst_1548_, v_x_1549_, v_x_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg___lam__0(lean_object* v_pre_1552_, lean_object* v_inst_1553_, lean_object* v_x1_1554_, lean_object* v_x2_1555_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1556_, 0, v_x1_1554_);
lean_ctor_set(v___x_1556_, 1, v_pre_1552_);
v___x_1557_ = lean_apply_1(v_inst_1553_, v_x2_1555_);
v___x_1558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg(lean_object* v_inst_1559_, lean_object* v_pre_1560_, lean_object* v_x_1561_){
_start:
{
if (lean_obj_tag(v_x_1561_) == 0)
{
lean_object* v___x_1562_; 
lean_dec(v_pre_1560_);
lean_dec_ref(v_inst_1559_);
v___x_1562_ = lean_box(0);
return v___x_1562_;
}
else
{
lean_object* v_head_1563_; lean_object* v_tail_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1574_; 
v_head_1563_ = lean_ctor_get(v_x_1561_, 0);
v_tail_1564_ = lean_ctor_get(v_x_1561_, 1);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_x_1561_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1566_ = v_x_1561_;
v_isShared_1567_ = v_isSharedCheck_1574_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_tail_1564_);
lean_inc(v_head_1563_);
lean_dec(v_x_1561_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1574_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___f_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
lean_inc_ref(v_inst_1559_);
lean_inc(v_pre_1560_);
v___f_1568_ = lean_alloc_closure((void*)(l_Std_Format_prefixJoin___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1568_, 0, v_pre_1560_);
lean_closure_set(v___f_1568_, 1, v_inst_1559_);
v___x_1569_ = lean_apply_1(v_inst_1559_, v_head_1563_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set_tag(v___x_1566_, 5);
lean_ctor_set(v___x_1566_, 1, v___x_1569_);
lean_ctor_set(v___x_1566_, 0, v_pre_1560_);
v___x_1571_ = v___x_1566_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_pre_1560_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_List_foldl___redArg(v___f_1568_, v___x_1571_, v_tail_1564_);
return v___x_1572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin(lean_object* v_00_u03b1_1575_, lean_object* v_inst_1576_, lean_object* v_pre_1577_, lean_object* v_x_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Std_Format_prefixJoin___redArg(v_inst_1576_, v_pre_1577_, v_x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg___lam__0(lean_object* v_inst_1580_, lean_object* v_x_1581_, lean_object* v_x1_1582_, lean_object* v_x2_1583_){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = lean_apply_1(v_inst_1580_, v_x2_1583_);
v___x_1585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1585_, 0, v_x1_1582_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
lean_ctor_set(v___x_1586_, 1, v_x_1581_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg(lean_object* v_inst_1587_, lean_object* v_x_1588_, lean_object* v_x_1589_){
_start:
{
if (lean_obj_tag(v_x_1588_) == 0)
{
lean_object* v___x_1590_; 
lean_dec(v_x_1589_);
lean_dec_ref(v_inst_1587_);
v___x_1590_ = lean_box(0);
return v___x_1590_;
}
else
{
lean_object* v_head_1591_; lean_object* v_tail_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1602_; 
v_head_1591_ = lean_ctor_get(v_x_1588_, 0);
v_tail_1592_ = lean_ctor_get(v_x_1588_, 1);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_x_1588_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1594_ = v_x_1588_;
v_isShared_1595_ = v_isSharedCheck_1602_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_tail_1592_);
lean_inc(v_head_1591_);
lean_dec(v_x_1588_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1602_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___f_1596_; lean_object* v___x_1597_; lean_object* v___x_1599_; 
lean_inc(v_x_1589_);
lean_inc_ref(v_inst_1587_);
v___f_1596_ = lean_alloc_closure((void*)(l_Std_Format_joinSuffix___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1596_, 0, v_inst_1587_);
lean_closure_set(v___f_1596_, 1, v_x_1589_);
v___x_1597_ = lean_apply_1(v_inst_1587_, v_head_1591_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set_tag(v___x_1594_, 5);
lean_ctor_set(v___x_1594_, 1, v_x_1589_);
lean_ctor_set(v___x_1594_, 0, v___x_1597_);
v___x_1599_ = v___x_1594_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_x_1589_);
v___x_1599_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_List_foldl___redArg(v___f_1596_, v___x_1599_, v_tail_1592_);
return v___x_1600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix(lean_object* v_00_u03b1_1603_, lean_object* v_inst_1604_, lean_object* v_x_1605_, lean_object* v_x_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Std_Format_joinSuffix___redArg(v_inst_1604_, v_x_1605_, v_x_1606_);
return v___x_1607_;
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
