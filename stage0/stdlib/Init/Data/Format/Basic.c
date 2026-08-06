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
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_Format_FlattenBehavior_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Std_Format_FlattenBehavior_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim___redArg(lean_object* v_allOrNone_22_){
_start:
{
lean_inc(v_allOrNone_22_);
return v_allOrNone_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim___redArg___boxed(lean_object* v_allOrNone_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Format_FlattenBehavior_allOrNone_elim___redArg(v_allOrNone_23_);
lean_dec(v_allOrNone_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_allOrNone_28_){
_start:
{
lean_inc(v_allOrNone_28_);
return v_allOrNone_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_allOrNone_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Std_Format_FlattenBehavior_allOrNone_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_allOrNone_32_);
lean_dec(v_allOrNone_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim___redArg(lean_object* v_fill_35_){
_start:
{
lean_inc(v_fill_35_);
return v_fill_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim___redArg___boxed(lean_object* v_fill_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Format_FlattenBehavior_fill_elim___redArg(v_fill_36_);
lean_dec(v_fill_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_fill_41_){
_start:
{
lean_inc(v_fill_41_);
return v_fill_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_fill_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Std_Format_FlattenBehavior_fill_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_fill_45_);
lean_dec(v_fill_45_);
return v_res_47_;
}
}
static uint8_t _init_l_Std_Format_instInhabitedFlattenBehavior_default(void){
_start:
{
uint8_t v___x_48_; 
v___x_48_ = 0;
return v___x_48_;
}
}
static uint8_t _init_l_Std_Format_instInhabitedFlattenBehavior(void){
_start:
{
uint8_t v___x_49_; 
v___x_49_ = 0;
return v___x_49_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_instBEqFlattenBehavior_beq(uint8_t v_x_50_, uint8_t v_y_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_52_ = l_Std_Format_FlattenBehavior_ctorIdx(v_x_50_);
v___x_53_ = l_Std_Format_FlattenBehavior_ctorIdx(v_y_51_);
v___x_54_ = lean_nat_dec_eq(v___x_52_, v___x_53_);
lean_dec(v___x_53_);
lean_dec(v___x_52_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_instBEqFlattenBehavior_beq___boxed(lean_object* v_x_55_, lean_object* v_y_56_){
_start:
{
uint8_t v_x_17__boxed_57_; uint8_t v_y_18__boxed_58_; uint8_t v_res_59_; lean_object* v_r_60_; 
v_x_17__boxed_57_ = lean_unbox(v_x_55_);
v_y_18__boxed_58_ = lean_unbox(v_y_56_);
v_res_59_ = l_Std_Format_instBEqFlattenBehavior_beq(v_x_17__boxed_57_, v_y_18__boxed_58_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorIdx(lean_object* v_x_63_){
_start:
{
switch(lean_obj_tag(v_x_63_))
{
case 0:
{
lean_object* v___x_64_; 
v___x_64_ = lean_unsigned_to_nat(0u);
return v___x_64_;
}
case 1:
{
lean_object* v___x_65_; 
v___x_65_ = lean_unsigned_to_nat(1u);
return v___x_65_;
}
case 2:
{
lean_object* v___x_66_; 
v___x_66_ = lean_unsigned_to_nat(2u);
return v___x_66_;
}
case 3:
{
lean_object* v___x_67_; 
v___x_67_ = lean_unsigned_to_nat(3u);
return v___x_67_;
}
case 4:
{
lean_object* v___x_68_; 
v___x_68_ = lean_unsigned_to_nat(4u);
return v___x_68_;
}
case 5:
{
lean_object* v___x_69_; 
v___x_69_ = lean_unsigned_to_nat(5u);
return v___x_69_;
}
case 6:
{
lean_object* v___x_70_; 
v___x_70_ = lean_unsigned_to_nat(6u);
return v___x_70_;
}
default: 
{
lean_object* v___x_71_; 
v___x_71_ = lean_unsigned_to_nat(7u);
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorIdx___boxed(lean_object* v_x_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Std_Format_ctorIdx(v_x_72_);
lean_dec(v_x_72_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorElim___redArg(lean_object* v_t_74_, lean_object* v_k_75_){
_start:
{
switch(lean_obj_tag(v_t_74_))
{
case 2:
{
uint8_t v_force_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_force_76_ = lean_ctor_get_uint8(v_t_74_, 0);
lean_dec_ref_known(v_t_74_, 0);
v___x_77_ = lean_box(v_force_76_);
v___x_78_ = lean_apply_1(v_k_75_, v___x_77_);
return v___x_78_;
}
case 3:
{
lean_object* v_a_79_; lean_object* v___x_80_; 
v_a_79_ = lean_ctor_get(v_t_74_, 0);
lean_inc_ref(v_a_79_);
lean_dec_ref_known(v_t_74_, 1);
v___x_80_ = lean_apply_1(v_k_75_, v_a_79_);
return v___x_80_;
}
case 4:
{
lean_object* v_indent_81_; lean_object* v_f_82_; lean_object* v___x_83_; 
v_indent_81_ = lean_ctor_get(v_t_74_, 0);
lean_inc(v_indent_81_);
v_f_82_ = lean_ctor_get(v_t_74_, 1);
lean_inc(v_f_82_);
lean_dec_ref_known(v_t_74_, 2);
v___x_83_ = lean_apply_2(v_k_75_, v_indent_81_, v_f_82_);
return v___x_83_;
}
case 5:
{
lean_object* v_a_84_; lean_object* v_a_85_; lean_object* v___x_86_; 
v_a_84_ = lean_ctor_get(v_t_74_, 0);
lean_inc(v_a_84_);
v_a_85_ = lean_ctor_get(v_t_74_, 1);
lean_inc(v_a_85_);
lean_dec_ref_known(v_t_74_, 2);
v___x_86_ = lean_apply_2(v_k_75_, v_a_84_, v_a_85_);
return v___x_86_;
}
case 6:
{
lean_object* v_a_87_; uint8_t v_behavior_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v_a_87_ = lean_ctor_get(v_t_74_, 0);
lean_inc(v_a_87_);
v_behavior_88_ = lean_ctor_get_uint8(v_t_74_, sizeof(void*)*1);
lean_dec_ref_known(v_t_74_, 1);
v___x_89_ = lean_box(v_behavior_88_);
v___x_90_ = lean_apply_2(v_k_75_, v_a_87_, v___x_89_);
return v___x_90_;
}
case 7:
{
lean_object* v_a_91_; lean_object* v_a_92_; lean_object* v___x_93_; 
v_a_91_ = lean_ctor_get(v_t_74_, 0);
lean_inc(v_a_91_);
v_a_92_ = lean_ctor_get(v_t_74_, 1);
lean_inc(v_a_92_);
lean_dec_ref_known(v_t_74_, 2);
v___x_93_ = lean_apply_2(v_k_75_, v_a_91_, v_a_92_);
return v___x_93_;
}
default: 
{
lean_dec(v_t_74_);
return v_k_75_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorElim(lean_object* v_motive_94_, lean_object* v_ctorIdx_95_, lean_object* v_t_96_, lean_object* v_h_97_, lean_object* v_k_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Std_Format_ctorElim___redArg(v_t_96_, v_k_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorElim___boxed(lean_object* v_motive_100_, lean_object* v_ctorIdx_101_, lean_object* v_t_102_, lean_object* v_h_103_, lean_object* v_k_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_Format_ctorElim(v_motive_100_, v_ctorIdx_101_, v_t_102_, v_h_103_, v_k_104_);
lean_dec(v_ctorIdx_101_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nil_elim___redArg(lean_object* v_t_106_, lean_object* v_nil_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Std_Format_ctorElim___redArg(v_t_106_, v_nil_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nil_elim(lean_object* v_motive_109_, lean_object* v_t_110_, lean_object* v_h_111_, lean_object* v_nil_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Std_Format_ctorElim___redArg(v_t_110_, v_nil_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_line_elim___redArg(lean_object* v_t_114_, lean_object* v_line_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Std_Format_ctorElim___redArg(v_t_114_, v_line_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_line_elim(lean_object* v_motive_117_, lean_object* v_t_118_, lean_object* v_h_119_, lean_object* v_line_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Std_Format_ctorElim___redArg(v_t_118_, v_line_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_align_elim___redArg(lean_object* v_t_122_, lean_object* v_align_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Std_Format_ctorElim___redArg(v_t_122_, v_align_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_align_elim(lean_object* v_motive_125_, lean_object* v_t_126_, lean_object* v_h_127_, lean_object* v_align_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Std_Format_ctorElim___redArg(v_t_126_, v_align_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_text_elim___redArg(lean_object* v_t_130_, lean_object* v_text_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Std_Format_ctorElim___redArg(v_t_130_, v_text_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_text_elim(lean_object* v_motive_133_, lean_object* v_t_134_, lean_object* v_h_135_, lean_object* v_text_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Std_Format_ctorElim___redArg(v_t_134_, v_text_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nest_elim___redArg(lean_object* v_t_138_, lean_object* v_nest_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Std_Format_ctorElim___redArg(v_t_138_, v_nest_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nest_elim(lean_object* v_motive_141_, lean_object* v_t_142_, lean_object* v_h_143_, lean_object* v_nest_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Std_Format_ctorElim___redArg(v_t_142_, v_nest_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_append_elim___redArg(lean_object* v_t_146_, lean_object* v_append_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Std_Format_ctorElim___redArg(v_t_146_, v_append_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_append_elim(lean_object* v_motive_149_, lean_object* v_t_150_, lean_object* v_h_151_, lean_object* v_append_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Std_Format_ctorElim___redArg(v_t_150_, v_append_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_group_elim___redArg(lean_object* v_t_154_, lean_object* v_group_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_Format_ctorElim___redArg(v_t_154_, v_group_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_group_elim(lean_object* v_motive_157_, lean_object* v_t_158_, lean_object* v_h_159_, lean_object* v_group_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Std_Format_ctorElim___redArg(v_t_158_, v_group_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_tag_elim___redArg(lean_object* v_t_162_, lean_object* v_tag_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_Format_ctorElim___redArg(v_t_162_, v_tag_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_tag_elim(lean_object* v_motive_165_, lean_object* v_t_166_, lean_object* v_h_167_, lean_object* v_tag_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Std_Format_ctorElim___redArg(v_t_166_, v_tag_168_);
return v___x_169_;
}
}
static lean_object* _init_l_Std_instInhabitedFormat_default(void){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_box(0);
return v___x_170_;
}
}
static lean_object* _init_l_Std_instInhabitedFormat(void){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_box(0);
return v___x_171_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_isEmpty(lean_object* v_x_173_){
_start:
{
switch(lean_obj_tag(v_x_173_))
{
case 1:
{
uint8_t v___x_174_; 
v___x_174_ = 0;
return v___x_174_;
}
case 3:
{
lean_object* v_a_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v_a_175_ = lean_ctor_get(v_x_173_, 0);
v___x_176_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_177_ = lean_string_dec_eq(v_a_175_, v___x_176_);
return v___x_177_;
}
case 4:
{
lean_object* v_f_178_; 
v_f_178_ = lean_ctor_get(v_x_173_, 1);
v_x_173_ = v_f_178_;
goto _start;
}
case 5:
{
lean_object* v_a_180_; lean_object* v_a_181_; uint8_t v___x_182_; 
v_a_180_ = lean_ctor_get(v_x_173_, 0);
v_a_181_ = lean_ctor_get(v_x_173_, 1);
v___x_182_ = l_Std_Format_isEmpty(v_a_180_);
if (v___x_182_ == 0)
{
return v___x_182_;
}
else
{
v_x_173_ = v_a_181_;
goto _start;
}
}
case 6:
{
lean_object* v_a_184_; 
v_a_184_ = lean_ctor_get(v_x_173_, 0);
v_x_173_ = v_a_184_;
goto _start;
}
case 7:
{
lean_object* v_a_186_; 
v_a_186_ = lean_ctor_get(v_x_173_, 1);
v_x_173_ = v_a_186_;
goto _start;
}
default: 
{
uint8_t v___x_188_; 
v___x_188_ = 1;
return v___x_188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_isEmpty___boxed(lean_object* v_x_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_Std_Format_isEmpty(v_x_189_);
lean_dec(v_x_189_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_fill(lean_object* v_f_192_){
_start:
{
uint8_t v___x_193_; lean_object* v___x_194_; 
v___x_193_ = 1;
v___x_194_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_194_, 0, v_f_192_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*1, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_instAppend___lam__0(lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_197_, 0, v_a_195_);
lean_ctor_set(v___x_197_, 1, v_a_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_instCoeString___lam__0(lean_object* v_a_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_201_, 0, v_a_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_join_spec__0(lean_object* v_x_204_, lean_object* v_x_205_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
return v_x_204_;
}
else
{
lean_object* v_head_206_; lean_object* v_tail_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_215_; 
v_head_206_ = lean_ctor_get(v_x_205_, 0);
v_tail_207_ = lean_ctor_get(v_x_205_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_x_205_);
if (v_isSharedCheck_215_ == 0)
{
v___x_209_ = v_x_205_;
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_tail_207_);
lean_inc(v_head_206_);
lean_dec(v_x_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set_tag(v___x_209_, 5);
lean_ctor_set(v___x_209_, 1, v_head_206_);
lean_ctor_set(v___x_209_, 0, v_x_204_);
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_x_204_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_head_206_);
v___x_212_ = v_reuseFailAlloc_214_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
v_x_204_ = v___x_212_;
v_x_205_ = v_tail_207_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_join(lean_object* v_xs_218_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_Std_Format_join___closed__0));
v___x_220_ = l_List_foldl___at___00Std_Format_join_spec__0(v___x_219_, v_xs_218_);
return v___x_220_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_isNil(lean_object* v_x_221_){
_start:
{
if (lean_obj_tag(v_x_221_) == 0)
{
uint8_t v___x_222_; 
v___x_222_ = 1;
return v___x_222_;
}
else
{
uint8_t v___x_223_; 
v___x_223_ = 0;
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_isNil___boxed(lean_object* v_x_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l_Std_Format_isNil(v_x_224_);
lean_dec(v_x_224_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_merge(lean_object* v_w_232_, lean_object* v_r_u2081_233_, lean_object* v_r_u2082_234_){
_start:
{
uint8_t v_foundLine_235_; lean_object* v_space_236_; uint8_t v___y_238_; uint8_t v___x_252_; 
v_foundLine_235_ = lean_ctor_get_uint8(v_r_u2081_233_, sizeof(void*)*1);
v_space_236_ = lean_ctor_get(v_r_u2081_233_, 0);
v___x_252_ = lean_nat_dec_lt(v_w_232_, v_space_236_);
if (v___x_252_ == 0)
{
v___y_238_ = v_foundLine_235_;
goto v___jp_237_;
}
else
{
v___y_238_ = v___x_252_;
goto v___jp_237_;
}
v___jp_237_:
{
if (v___y_238_ == 0)
{
lean_object* v___x_239_; lean_object* v_r_u2082_240_; uint8_t v_foundLine_241_; uint8_t v_foundFlattenedHardLine_242_; lean_object* v_space_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_251_; 
v___x_239_ = lean_nat_sub(v_w_232_, v_space_236_);
v_r_u2082_240_ = lean_apply_1(v_r_u2082_234_, v___x_239_);
v_foundLine_241_ = lean_ctor_get_uint8(v_r_u2082_240_, sizeof(void*)*1);
v_foundFlattenedHardLine_242_ = lean_ctor_get_uint8(v_r_u2082_240_, sizeof(void*)*1 + 1);
v_space_243_ = lean_ctor_get(v_r_u2082_240_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v_r_u2082_240_);
if (v_isSharedCheck_251_ == 0)
{
v___x_245_ = v_r_u2082_240_;
v_isShared_246_ = v_isSharedCheck_251_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_space_243_);
lean_dec(v_r_u2082_240_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_251_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = lean_nat_add(v_space_236_, v_space_243_);
lean_dec(v_space_243_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_247_);
v___x_249_ = v___x_245_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
lean_ctor_set_uint8(v_reuseFailAlloc_250_, sizeof(void*)*1, v_foundLine_241_);
lean_ctor_set_uint8(v_reuseFailAlloc_250_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_242_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
else
{
lean_dec_ref(v_r_u2082_234_);
lean_inc_ref(v_r_u2081_233_);
return v_r_u2081_233_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_merge___boxed(lean_object* v_w_253_, lean_object* v_r_u2081_254_, lean_object* v_r_u2082_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Init_Data_Format_Basic_0__Std_Format_merge(v_w_253_, v_r_u2081_254_, v_r_u2082_255_);
lean_dec_ref(v_r_u2081_254_);
lean_dec(v_w_253_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_spec__0(lean_object* v_a_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lean_nat_to_int(v_a_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(lean_object* v_x_262_, uint8_t v_x_263_, lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
uint8_t v___y_267_; 
switch(lean_obj_tag(v_x_262_))
{
case 0:
{
lean_object* v___x_276_; 
lean_dec(v_x_265_);
lean_dec(v_x_264_);
v___x_276_ = ((lean_object*)(l_Std_Format_instInhabitedSpaceResult_default___closed__0));
return v___x_276_;
}
case 1:
{
lean_dec(v_x_265_);
lean_dec(v_x_264_);
if (v_x_263_ == 0)
{
uint8_t v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = 1;
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*1, v___x_277_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*1 + 1, v_x_263_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; 
v___x_280_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0));
return v___x_280_;
}
}
case 2:
{
if (v_x_263_ == 0)
{
lean_dec_ref_known(v_x_262_, 0);
v___y_267_ = v_x_263_;
goto v___jp_266_;
}
else
{
uint8_t v_force_281_; 
v_force_281_ = lean_ctor_get_uint8(v_x_262_, 0);
lean_dec_ref_known(v_x_262_, 0);
if (v_force_281_ == 0)
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec(v_x_265_);
lean_dec(v_x_264_);
v___x_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*1, v_force_281_);
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*1 + 1, v_force_281_);
return v___x_283_;
}
else
{
uint8_t v___x_284_; 
v___x_284_ = 0;
v___y_267_ = v___x_284_;
goto v___jp_266_;
}
}
}
case 3:
{
lean_object* v_a_285_; uint32_t v___x_286_; lean_object* v_p_287_; lean_object* v_off_288_; uint8_t v___y_290_; lean_object* v___x_293_; uint8_t v___x_294_; 
lean_dec(v_x_265_);
lean_dec(v_x_264_);
v_a_285_ = lean_ctor_get(v_x_262_, 0);
lean_inc_ref_n(v_a_285_, 3);
lean_dec_ref_known(v_x_262_, 1);
v___x_286_ = 10;
v_p_287_ = lean_string_posof(v_a_285_, v___x_286_);
lean_inc(v_p_287_);
v_off_288_ = lean_string_offsetofpos(v_a_285_, v_p_287_);
v___x_293_ = lean_string_utf8_byte_size(v_a_285_);
lean_dec_ref(v_a_285_);
v___x_294_ = lean_nat_dec_eq(v_p_287_, v___x_293_);
lean_dec(v_p_287_);
if (v___x_294_ == 0)
{
uint8_t v___x_295_; 
v___x_295_ = 1;
v___y_290_ = v___x_295_;
goto v___jp_289_;
}
else
{
uint8_t v___x_296_; 
v___x_296_ = 0;
v___y_290_ = v___x_296_;
goto v___jp_289_;
}
v___jp_289_:
{
if (v_x_263_ == 0)
{
lean_object* v___x_291_; 
v___x_291_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_291_, 0, v_off_288_);
lean_ctor_set_uint8(v___x_291_, sizeof(void*)*1, v___y_290_);
lean_ctor_set_uint8(v___x_291_, sizeof(void*)*1 + 1, v_x_263_);
return v___x_291_;
}
else
{
lean_object* v___x_292_; 
v___x_292_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_292_, 0, v_off_288_);
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*1, v___y_290_);
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*1 + 1, v___y_290_);
return v___x_292_;
}
}
}
case 4:
{
lean_object* v_indent_297_; lean_object* v_f_298_; lean_object* v___x_299_; 
v_indent_297_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_indent_297_);
v_f_298_ = lean_ctor_get(v_x_262_, 1);
lean_inc(v_f_298_);
lean_dec_ref_known(v_x_262_, 2);
v___x_299_ = lean_int_sub(v_x_264_, v_indent_297_);
lean_dec(v_indent_297_);
lean_dec(v_x_264_);
v_x_262_ = v_f_298_;
v_x_264_ = v___x_299_;
goto _start;
}
case 5:
{
lean_object* v_a_301_; lean_object* v_a_302_; lean_object* v___x_303_; uint8_t v_foundLine_304_; lean_object* v_space_305_; uint8_t v___y_307_; uint8_t v___x_321_; 
v_a_301_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_a_301_);
v_a_302_ = lean_ctor_get(v_x_262_, 1);
lean_inc(v_a_302_);
lean_dec_ref_known(v_x_262_, 2);
lean_inc(v_x_265_);
lean_inc(v_x_264_);
v___x_303_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_a_301_, v_x_263_, v_x_264_, v_x_265_);
v_foundLine_304_ = lean_ctor_get_uint8(v___x_303_, sizeof(void*)*1);
v_space_305_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_space_305_);
v___x_321_ = lean_nat_dec_lt(v_x_265_, v_space_305_);
if (v___x_321_ == 0)
{
v___y_307_ = v_foundLine_304_;
goto v___jp_306_;
}
else
{
v___y_307_ = v___x_321_;
goto v___jp_306_;
}
v___jp_306_:
{
if (v___y_307_ == 0)
{
lean_object* v___x_308_; lean_object* v_r_u2082_309_; uint8_t v_foundLine_310_; uint8_t v_foundFlattenedHardLine_311_; lean_object* v_space_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_320_; 
lean_dec_ref(v___x_303_);
v___x_308_ = lean_nat_sub(v_x_265_, v_space_305_);
lean_dec(v_x_265_);
v_r_u2082_309_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_a_302_, v_x_263_, v_x_264_, v___x_308_);
v_foundLine_310_ = lean_ctor_get_uint8(v_r_u2082_309_, sizeof(void*)*1);
v_foundFlattenedHardLine_311_ = lean_ctor_get_uint8(v_r_u2082_309_, sizeof(void*)*1 + 1);
v_space_312_ = lean_ctor_get(v_r_u2082_309_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v_r_u2082_309_);
if (v_isSharedCheck_320_ == 0)
{
v___x_314_ = v_r_u2082_309_;
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_space_312_);
lean_dec(v_r_u2082_309_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_316_ = lean_nat_add(v_space_305_, v_space_312_);
lean_dec(v_space_312_);
lean_dec(v_space_305_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_316_);
v___x_318_ = v___x_314_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
lean_ctor_set_uint8(v_reuseFailAlloc_319_, sizeof(void*)*1, v_foundLine_310_);
lean_ctor_set_uint8(v_reuseFailAlloc_319_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_311_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_dec(v_space_305_);
lean_dec(v_a_302_);
lean_dec(v_x_265_);
lean_dec(v_x_264_);
return v___x_303_;
}
}
}
case 6:
{
lean_object* v_a_322_; uint8_t v___x_323_; 
v_a_322_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v_x_262_, 1);
v___x_323_ = 1;
v_x_262_ = v_a_322_;
v_x_263_ = v___x_323_;
goto _start;
}
default: 
{
lean_object* v_a_325_; 
v_a_325_ = lean_ctor_get(v_x_262_, 1);
lean_inc(v_a_325_);
lean_dec_ref_known(v_x_262_, 2);
v_x_262_ = v_a_325_;
goto _start;
}
}
v___jp_266_:
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = lean_nat_to_int(v_x_265_);
v___x_269_ = lean_int_dec_lt(v___x_268_, v_x_264_);
if (v___x_269_ == 0)
{
uint8_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v___x_268_);
lean_dec(v_x_264_);
v___x_270_ = 1;
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*1, v___x_270_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*1 + 1, v___y_267_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_int_sub(v_x_264_, v___x_268_);
lean_dec(v___x_268_);
lean_dec(v_x_264_);
v___x_274_ = l_Int_toNat(v___x_273_);
lean_dec(v___x_273_);
v___x_275_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set_uint8(v___x_275_, sizeof(void*)*1, v___y_267_);
lean_ctor_set_uint8(v___x_275_, sizeof(void*)*1 + 1, v___y_267_);
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___boxed(lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
uint8_t v_x_415__boxed_331_; lean_object* v_res_332_; 
v_x_415__boxed_331_ = lean_unbox(v_x_328_);
v_res_332_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_x_327_, v_x_415__boxed_331_, v_x_329_, v_x_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx(lean_object* v_x_333_){
_start:
{
if (lean_obj_tag(v_x_333_) == 0)
{
lean_object* v___x_334_; 
v___x_334_ = lean_unsigned_to_nat(0u);
return v___x_334_;
}
else
{
lean_object* v___x_335_; 
v___x_335_ = lean_unsigned_to_nat(1u);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx___boxed(lean_object* v_x_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Std_Format_FlattenAllowability_ctorIdx(v_x_336_);
lean_dec(v_x_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___redArg(lean_object* v_t_338_, lean_object* v_k_339_){
_start:
{
if (lean_obj_tag(v_t_338_) == 0)
{
uint8_t v_fits_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_fits_340_ = lean_ctor_get_uint8(v_t_338_, 0);
v___x_341_ = lean_box(v_fits_340_);
v___x_342_ = lean_apply_1(v_k_339_, v___x_341_);
return v___x_342_;
}
else
{
return v_k_339_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___redArg___boxed(lean_object* v_t_343_, lean_object* v_k_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_343_, v_k_344_);
lean_dec(v_t_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim(lean_object* v_motive_346_, lean_object* v_ctorIdx_347_, lean_object* v_t_348_, lean_object* v_h_349_, lean_object* v_k_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_348_, v_k_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___boxed(lean_object* v_motive_352_, lean_object* v_ctorIdx_353_, lean_object* v_t_354_, lean_object* v_h_355_, lean_object* v_k_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Std_Format_FlattenAllowability_ctorElim(v_motive_352_, v_ctorIdx_353_, v_t_354_, v_h_355_, v_k_356_);
lean_dec(v_t_354_);
lean_dec(v_ctorIdx_353_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___redArg(lean_object* v_t_358_, lean_object* v_allow_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_358_, v_allow_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___redArg___boxed(lean_object* v_t_361_, lean_object* v_allow_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Std_Format_FlattenAllowability_allow_elim___redArg(v_t_361_, v_allow_362_);
lean_dec(v_t_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim(lean_object* v_motive_364_, lean_object* v_t_365_, lean_object* v_h_366_, lean_object* v_allow_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_365_, v_allow_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___boxed(lean_object* v_motive_369_, lean_object* v_t_370_, lean_object* v_h_371_, lean_object* v_allow_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Std_Format_FlattenAllowability_allow_elim(v_motive_369_, v_t_370_, v_h_371_, v_allow_372_);
lean_dec(v_t_370_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___redArg(lean_object* v_t_374_, lean_object* v_disallow_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_374_, v_disallow_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___redArg___boxed(lean_object* v_t_377_, lean_object* v_disallow_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Std_Format_FlattenAllowability_disallow_elim___redArg(v_t_377_, v_disallow_378_);
lean_dec(v_t_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim(lean_object* v_motive_380_, lean_object* v_t_381_, lean_object* v_h_382_, lean_object* v_disallow_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_381_, v_disallow_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___boxed(lean_object* v_motive_385_, lean_object* v_t_386_, lean_object* v_h_387_, lean_object* v_disallow_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Std_Format_FlattenAllowability_disallow_elim(v_motive_385_, v_t_386_, v_h_387_, v_disallow_388_);
lean_dec(v_t_386_);
return v_res_389_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_instBEqFlattenAllowability_beq(lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
if (lean_obj_tag(v_x_391_) == 0)
{
uint8_t v_fits_392_; 
v_fits_392_ = lean_ctor_get_uint8(v_x_390_, 0);
if (v_fits_392_ == 0)
{
uint8_t v_fits_393_; 
v_fits_393_ = lean_ctor_get_uint8(v_x_391_, 0);
if (v_fits_393_ == 0)
{
uint8_t v___x_394_; 
v___x_394_ = 1;
return v___x_394_;
}
else
{
return v_fits_392_;
}
}
else
{
uint8_t v_fits_395_; 
v_fits_395_ = lean_ctor_get_uint8(v_x_391_, 0);
return v_fits_395_;
}
}
else
{
uint8_t v___x_396_; 
v___x_396_ = 0;
return v___x_396_;
}
}
else
{
if (lean_obj_tag(v_x_391_) == 1)
{
uint8_t v___x_397_; 
v___x_397_ = 1;
return v___x_397_;
}
else
{
uint8_t v___x_398_; 
v___x_398_ = 0;
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_instBEqFlattenAllowability_beq___boxed(lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l_Std_Format_instBEqFlattenAllowability_beq(v_x_399_, v_x_400_);
lean_dec(v_x_400_);
lean_dec(v_x_399_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_FlattenAllowability_shouldFlatten(lean_object* v_x_405_){
_start:
{
if (lean_obj_tag(v_x_405_) == 0)
{
uint8_t v_fits_406_; 
v_fits_406_ = lean_ctor_get_uint8(v_x_405_, 0);
if (v_fits_406_ == 1)
{
return v_fits_406_;
}
else
{
uint8_t v___x_407_; 
v___x_407_ = 0;
return v___x_407_;
}
}
else
{
uint8_t v___x_408_; 
v___x_408_ = 0;
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_shouldFlatten___boxed(lean_object* v_x_409_){
_start:
{
uint8_t v_res_410_; lean_object* v_r_411_; 
v_res_410_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_x_409_);
lean_dec(v_x_409_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
if (lean_obj_tag(v_x_412_) == 0)
{
lean_object* v___x_415_; 
lean_dec(v_x_414_);
lean_dec(v_x_413_);
v___x_415_ = ((lean_object*)(l_Std_Format_instInhabitedSpaceResult_default___closed__0));
return v___x_415_;
}
else
{
lean_object* v_head_416_; lean_object* v_items_417_; 
v_head_416_ = lean_ctor_get(v_x_412_, 0);
lean_inc(v_head_416_);
v_items_417_ = lean_ctor_get(v_head_416_, 1);
lean_inc(v_items_417_);
if (lean_obj_tag(v_items_417_) == 0)
{
lean_object* v_tail_418_; 
lean_dec(v_head_416_);
v_tail_418_ = lean_ctor_get(v_x_412_, 1);
lean_inc(v_tail_418_);
lean_dec_ref_known(v_x_412_, 2);
v_x_412_ = v_tail_418_;
goto _start;
}
else
{
lean_object* v_head_420_; lean_object* v_tail_421_; lean_object* v_fla_422_; uint8_t v_flb_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_465_; 
v_head_420_ = lean_ctor_get(v_items_417_, 0);
lean_inc(v_head_420_);
v_tail_421_ = lean_ctor_get(v_x_412_, 1);
lean_inc(v_tail_421_);
lean_dec_ref_known(v_x_412_, 2);
v_fla_422_ = lean_ctor_get(v_head_416_, 0);
v_flb_423_ = lean_ctor_get_uint8(v_head_416_, sizeof(void*)*2);
v_isSharedCheck_465_ = !lean_is_exclusive(v_head_416_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v_head_416_, 1);
lean_dec(v_unused_466_);
v___x_425_ = v_head_416_;
v_isShared_426_ = v_isSharedCheck_465_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_fla_422_);
lean_dec(v_head_416_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_465_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v_tail_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_463_; 
v_tail_427_ = lean_ctor_get(v_items_417_, 1);
v_isSharedCheck_463_ = !lean_is_exclusive(v_items_417_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; 
v_unused_464_ = lean_ctor_get(v_items_417_, 0);
lean_dec(v_unused_464_);
v___x_429_ = v_items_417_;
v_isShared_430_ = v_isSharedCheck_463_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_tail_427_);
lean_dec(v_items_417_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_463_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_f_431_; lean_object* v_indent_432_; uint8_t v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v_foundLine_439_; lean_object* v_space_440_; lean_object* v___x_442_; 
v_f_431_ = lean_ctor_get(v_head_420_, 0);
lean_inc(v_f_431_);
v_indent_432_ = lean_ctor_get(v_head_420_, 1);
lean_inc(v_indent_432_);
lean_dec(v_head_420_);
v___x_433_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_422_);
lean_inc_n(v_x_414_, 2);
v___x_434_ = lean_nat_to_int(v_x_414_);
lean_inc(v_x_413_);
v___x_435_ = lean_nat_to_int(v_x_413_);
v___x_436_ = lean_int_add(v___x_434_, v___x_435_);
lean_dec(v___x_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_int_sub(v___x_436_, v_indent_432_);
lean_dec(v_indent_432_);
lean_dec(v___x_436_);
v___x_438_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_f_431_, v___x_433_, v___x_437_, v_x_414_);
v_foundLine_439_ = lean_ctor_get_uint8(v___x_438_, sizeof(void*)*1);
v_space_440_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_space_440_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 1, v_tail_427_);
v___x_442_ = v___x_425_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_fla_422_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_tail_427_);
lean_ctor_set_uint8(v_reuseFailAlloc_462_, sizeof(void*)*2, v_flb_423_);
v___x_442_ = v_reuseFailAlloc_462_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_444_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v_tail_421_);
lean_ctor_set(v___x_429_, 0, v___x_442_);
v___x_444_ = v___x_429_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_tail_421_);
v___x_444_ = v_reuseFailAlloc_461_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
uint8_t v___y_446_; uint8_t v___x_460_; 
v___x_460_ = lean_nat_dec_lt(v_x_414_, v_space_440_);
if (v___x_460_ == 0)
{
v___y_446_ = v_foundLine_439_;
goto v___jp_445_;
}
else
{
v___y_446_ = v___x_460_;
goto v___jp_445_;
}
v___jp_445_:
{
if (v___y_446_ == 0)
{
lean_object* v___x_447_; lean_object* v_r_u2082_448_; uint8_t v_foundLine_449_; uint8_t v_foundFlattenedHardLine_450_; lean_object* v_space_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_459_; 
lean_dec_ref(v___x_438_);
v___x_447_ = lean_nat_sub(v_x_414_, v_space_440_);
lean_dec(v_x_414_);
v_r_u2082_448_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_444_, v_x_413_, v___x_447_);
v_foundLine_449_ = lean_ctor_get_uint8(v_r_u2082_448_, sizeof(void*)*1);
v_foundFlattenedHardLine_450_ = lean_ctor_get_uint8(v_r_u2082_448_, sizeof(void*)*1 + 1);
v_space_451_ = lean_ctor_get(v_r_u2082_448_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v_r_u2082_448_);
if (v_isSharedCheck_459_ == 0)
{
v___x_453_ = v_r_u2082_448_;
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_space_451_);
lean_dec(v_r_u2082_448_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_455_ = lean_nat_add(v_space_440_, v_space_451_);
lean_dec(v_space_451_);
lean_dec(v_space_440_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_455_);
v___x_457_ = v___x_453_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
lean_ctor_set_uint8(v_reuseFailAlloc_458_, sizeof(void*)*1, v_foundLine_449_);
lean_ctor_set_uint8(v_reuseFailAlloc_458_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_450_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
else
{
lean_dec_ref(v___x_444_);
lean_dec(v_space_440_);
lean_dec(v_x_414_);
lean_dec(v_x_413_);
return v___x_438_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(uint8_t v_flb_467_, lean_object* v_items_468_, lean_object* v_w_469_, lean_object* v_gs_470_, lean_object* v_toPure_471_, lean_object* v_k_472_){
_start:
{
uint8_t v___y_474_; uint8_t v___x_479_; uint8_t v___x_480_; lean_object* v___x_481_; lean_object* v_g_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v_r_486_; lean_object* v___y_488_; uint8_t v_foundLine_493_; lean_object* v_space_494_; uint8_t v___y_496_; uint8_t v___x_510_; 
v___x_479_ = 0;
v___x_480_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_467_, v___x_479_);
v___x_481_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_481_, 0, v___x_480_);
lean_inc(v_items_468_);
v_g_482_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_482_, 0, v___x_481_);
lean_ctor_set(v_g_482_, 1, v_items_468_);
lean_ctor_set_uint8(v_g_482_, sizeof(void*)*2, v_flb_467_);
v___x_483_ = lean_box(0);
v___x_484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_484_, 0, v_g_482_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = lean_nat_sub(v_w_469_, v_k_472_);
lean_inc(v___x_485_);
lean_inc(v_k_472_);
v_r_486_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_484_, v_k_472_, v___x_485_);
v_foundLine_493_ = lean_ctor_get_uint8(v_r_486_, sizeof(void*)*1);
v_space_494_ = lean_ctor_get(v_r_486_, 0);
lean_inc(v_space_494_);
v___x_510_ = lean_nat_dec_lt(v___x_485_, v_space_494_);
if (v___x_510_ == 0)
{
v___y_496_ = v_foundLine_493_;
goto v___jp_495_;
}
else
{
v___y_496_ = v___x_510_;
goto v___jp_495_;
}
v___jp_473_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_475_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_475_, 0, v___y_474_);
v___x_476_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_476_, 0, v___x_475_);
lean_ctor_set(v___x_476_, 1, v_items_468_);
lean_ctor_set_uint8(v___x_476_, sizeof(void*)*2, v_flb_467_);
v___x_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v_gs_470_);
v___x_478_ = lean_apply_2(v_toPure_471_, lean_box(0), v___x_477_);
return v___x_478_;
}
v___jp_487_:
{
uint8_t v_foundFlattenedHardLine_489_; 
v_foundFlattenedHardLine_489_ = lean_ctor_get_uint8(v_r_486_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_486_);
if (v_foundFlattenedHardLine_489_ == 0)
{
lean_object* v_space_490_; uint8_t v___x_491_; 
v_space_490_ = lean_ctor_get(v___y_488_, 0);
lean_inc(v_space_490_);
lean_dec_ref(v___y_488_);
v___x_491_ = lean_nat_dec_le(v_space_490_, v___x_485_);
lean_dec(v___x_485_);
lean_dec(v_space_490_);
v___y_474_ = v___x_491_;
goto v___jp_473_;
}
else
{
uint8_t v___x_492_; 
lean_dec_ref(v___y_488_);
lean_dec(v___x_485_);
v___x_492_ = 0;
v___y_474_ = v___x_492_;
goto v___jp_473_;
}
}
v___jp_495_:
{
if (v___y_496_ == 0)
{
lean_object* v___x_497_; lean_object* v_r_u2082_498_; uint8_t v_foundLine_499_; uint8_t v_foundFlattenedHardLine_500_; lean_object* v_space_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_509_; 
v___x_497_ = lean_nat_sub(v___x_485_, v_space_494_);
lean_inc(v_gs_470_);
v_r_u2082_498_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_470_, v_k_472_, v___x_497_);
v_foundLine_499_ = lean_ctor_get_uint8(v_r_u2082_498_, sizeof(void*)*1);
v_foundFlattenedHardLine_500_ = lean_ctor_get_uint8(v_r_u2082_498_, sizeof(void*)*1 + 1);
v_space_501_ = lean_ctor_get(v_r_u2082_498_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v_r_u2082_498_);
if (v_isSharedCheck_509_ == 0)
{
v___x_503_ = v_r_u2082_498_;
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_space_501_);
lean_dec(v_r_u2082_498_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = lean_nat_add(v_space_494_, v_space_501_);
lean_dec(v_space_501_);
lean_dec(v_space_494_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_505_);
v___x_507_ = v___x_503_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
lean_ctor_set_uint8(v_reuseFailAlloc_508_, sizeof(void*)*1, v_foundLine_499_);
lean_ctor_set_uint8(v_reuseFailAlloc_508_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_500_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
v___y_488_ = v___x_507_;
goto v___jp_487_;
}
}
}
else
{
lean_dec(v_space_494_);
lean_dec(v_k_472_);
lean_inc_ref(v_r_486_);
v___y_488_ = v_r_486_;
goto v___jp_487_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed(lean_object* v_flb_511_, lean_object* v_items_512_, lean_object* v_w_513_, lean_object* v_gs_514_, lean_object* v_toPure_515_, lean_object* v_k_516_){
_start:
{
uint8_t v_flb_boxed_517_; lean_object* v_res_518_; 
v_flb_boxed_517_ = lean_unbox(v_flb_511_);
v_res_518_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(v_flb_boxed_517_, v_items_512_, v_w_513_, v_gs_514_, v_toPure_515_, v_k_516_);
lean_dec(v_w_513_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(uint8_t v_flb_519_, lean_object* v_items_520_, lean_object* v_gs_521_, lean_object* v_w_522_, lean_object* v_inst_523_, lean_object* v_inst_524_){
_start:
{
lean_object* v_toApplicative_525_; lean_object* v_toBind_526_; lean_object* v_currColumn_527_; lean_object* v_toPure_528_; lean_object* v___x_529_; lean_object* v___f_530_; lean_object* v___x_531_; 
v_toApplicative_525_ = lean_ctor_get(v_inst_523_, 0);
lean_inc_ref(v_toApplicative_525_);
v_toBind_526_ = lean_ctor_get(v_inst_523_, 1);
lean_inc(v_toBind_526_);
lean_dec_ref(v_inst_523_);
v_currColumn_527_ = lean_ctor_get(v_inst_524_, 2);
lean_inc(v_currColumn_527_);
lean_dec_ref(v_inst_524_);
v_toPure_528_ = lean_ctor_get(v_toApplicative_525_, 1);
lean_inc(v_toPure_528_);
lean_dec_ref(v_toApplicative_525_);
v___x_529_ = lean_box(v_flb_519_);
v___f_530_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_530_, 0, v___x_529_);
lean_closure_set(v___f_530_, 1, v_items_520_);
lean_closure_set(v___f_530_, 2, v_w_522_);
lean_closure_set(v___f_530_, 3, v_gs_521_);
lean_closure_set(v___f_530_, 4, v_toPure_528_);
v___x_531_ = lean_apply_4(v_toBind_526_, lean_box(0), lean_box(0), v_currColumn_527_, v___f_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___boxed(lean_object* v_flb_532_, lean_object* v_items_533_, lean_object* v_gs_534_, lean_object* v_w_535_, lean_object* v_inst_536_, lean_object* v_inst_537_){
_start:
{
uint8_t v_flb_boxed_538_; lean_object* v_res_539_; 
v_flb_boxed_538_ = lean_unbox(v_flb_532_);
v_res_539_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_boxed_538_, v_items_533_, v_gs_534_, v_w_535_, v_inst_536_, v_inst_537_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(lean_object* v_m_540_, uint8_t v_flb_541_, lean_object* v_items_542_, lean_object* v_gs_543_, lean_object* v_w_544_, lean_object* v_inst_545_, lean_object* v_inst_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_541_, v_items_542_, v_gs_543_, v_w_544_, v_inst_545_, v_inst_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___boxed(lean_object* v_m_548_, lean_object* v_flb_549_, lean_object* v_items_550_, lean_object* v_gs_551_, lean_object* v_w_552_, lean_object* v_inst_553_, lean_object* v_inst_554_){
_start:
{
uint8_t v_flb_boxed_555_; lean_object* v_res_556_; 
v_flb_boxed_555_ = lean_unbox(v_flb_549_);
v_res_556_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(v_m_548_, v_flb_boxed_555_, v_items_550_, v_gs_551_, v_w_552_, v_inst_553_, v_inst_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(lean_object* v_fla_557_, uint8_t v_flb_558_, lean_object* v_tail_559_, lean_object* v_is_x27_560_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_561_, 0, v_fla_557_);
lean_ctor_set(v___x_561_, 1, v_is_x27_560_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*2, v_flb_558_);
v___x_562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v_tail_559_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed(lean_object* v_fla_563_, lean_object* v_flb_564_, lean_object* v_tail_565_, lean_object* v_is_x27_566_){
_start:
{
uint8_t v_flb_1984__boxed_567_; lean_object* v_res_568_; 
v_flb_1984__boxed_567_ = lean_unbox(v_flb_564_);
v_res_568_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_563_, v_flb_1984__boxed_567_, v_tail_565_, v_is_x27_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3(lean_object* v_endTags_569_, lean_object* v_activeTags_570_, lean_object* v_toBind_571_, lean_object* v___f_572_, lean_object* v_____r_573_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_apply_1(v_endTags_569_, v_activeTags_570_);
v___x_575_ = lean_apply_4(v_toBind_571_, lean_box(0), lean_box(0), v___x_574_, v___f_572_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(lean_object* v_indent_576_, lean_object* v_pushNewline_577_, lean_object* v_toBind_578_, lean_object* v___f_579_, lean_object* v_____r_580_){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = l_Int_toNat(v_indent_576_);
v___x_582_ = lean_apply_1(v_pushNewline_577_, v___x_581_);
v___x_583_ = lean_apply_4(v_toBind_578_, lean_box(0), lean_box(0), v___x_582_, v___f_579_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed(lean_object* v_indent_584_, lean_object* v_pushNewline_585_, lean_object* v_toBind_586_, lean_object* v___f_587_, lean_object* v_____r_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(v_indent_584_, v_pushNewline_585_, v_toBind_586_, v___f_587_, v_____r_588_);
lean_dec(v_indent_584_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(lean_object* v_indent_590_, lean_object* v_inst_591_, lean_object* v_toBind_592_, lean_object* v___f_593_, lean_object* v___f_594_, lean_object* v_k_595_){
_start:
{
lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_596_ = lean_nat_to_int(v_k_595_);
v___x_597_ = lean_int_dec_lt(v___x_596_, v_indent_590_);
if (v___x_597_ == 0)
{
lean_object* v_pushNewline_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec(v___x_596_);
lean_dec(v___f_594_);
v_pushNewline_598_ = lean_ctor_get(v_inst_591_, 1);
lean_inc(v_pushNewline_598_);
lean_dec_ref(v_inst_591_);
v___x_599_ = l_Int_toNat(v_indent_590_);
v___x_600_ = lean_apply_1(v_pushNewline_598_, v___x_599_);
v___x_601_ = lean_apply_4(v_toBind_592_, lean_box(0), lean_box(0), v___x_600_, v___f_593_);
return v___x_601_;
}
else
{
lean_object* v_pushOutput_602_; lean_object* v___x_603_; uint32_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
lean_dec(v___f_593_);
v_pushOutput_602_ = lean_ctor_get(v_inst_591_, 0);
lean_inc(v_pushOutput_602_);
lean_dec_ref(v_inst_591_);
v___x_603_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_604_ = 32;
v___x_605_ = lean_int_sub(v_indent_590_, v___x_596_);
lean_dec(v___x_596_);
v___x_606_ = l_Int_toNat(v___x_605_);
lean_dec(v___x_605_);
v___x_607_ = lean_string_pushn(v___x_603_, v___x_604_, v___x_606_);
v___x_608_ = lean_apply_1(v_pushOutput_602_, v___x_607_);
v___x_609_ = lean_apply_4(v_toBind_592_, lean_box(0), lean_box(0), v___x_608_, v___f_594_);
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed(lean_object* v_indent_610_, lean_object* v_inst_611_, lean_object* v_toBind_612_, lean_object* v___f_613_, lean_object* v___f_614_, lean_object* v_k_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(v_indent_610_, v_inst_611_, v_toBind_612_, v___f_613_, v___f_614_, v_k_615_);
lean_dec(v_indent_610_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9(lean_object* v_inst_617_, lean_object* v_activeTags_618_, lean_object* v_toBind_619_, lean_object* v___f_620_, lean_object* v_____r_621_){
_start:
{
lean_object* v_endTags_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_endTags_622_ = lean_ctor_get(v_inst_617_, 4);
lean_inc(v_endTags_622_);
lean_dec_ref(v_inst_617_);
v___x_623_ = lean_apply_1(v_endTags_622_, v_activeTags_618_);
v___x_624_ = lean_apply_4(v_toBind_619_, lean_box(0), lean_box(0), v___x_623_, v___f_620_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1(lean_object* v_gs_x27_625_, lean_object* v_tail_626_, lean_object* v_w_627_, lean_object* v_inst_628_, lean_object* v_inst_629_, lean_object* v_____r_630_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_apply_1(v_gs_x27_625_, v_tail_626_);
v___x_632_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_627_, v_inst_628_, v_inst_629_, v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(uint8_t v_flb_634_, lean_object* v_tail_635_, lean_object* v_tail_636_, lean_object* v_w_637_, lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_toBind_640_, lean_object* v_____r_641_){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
lean_inc_ref(v_inst_639_);
lean_inc_ref(v_inst_638_);
lean_inc(v_w_637_);
v___x_642_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_634_, v_tail_635_, v_tail_636_, v_w_637_, v_inst_638_, v_inst_639_);
v___x_643_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_643_, 0, v_w_637_);
lean_closure_set(v___x_643_, 1, v_inst_638_);
lean_closure_set(v___x_643_, 2, v_inst_639_);
v___x_644_ = lean_apply_4(v_toBind_640_, lean_box(0), lean_box(0), v___x_642_, v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed(lean_object* v_flb_645_, lean_object* v_tail_646_, lean_object* v_tail_647_, lean_object* v_w_648_, lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_toBind_651_, lean_object* v_____r_652_){
_start:
{
uint8_t v_flb_2076__boxed_653_; lean_object* v_res_654_; 
v_flb_2076__boxed_653_ = lean_unbox(v_flb_645_);
v_res_654_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(v_flb_2076__boxed_653_, v_tail_646_, v_tail_647_, v_w_648_, v_inst_649_, v_inst_650_, v_toBind_651_, v_____r_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(lean_object* v_breakHere_656_, lean_object* v_w_657_, lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_endTags_660_, lean_object* v_activeTags_661_, lean_object* v_toBind_662_, lean_object* v_pushOutput_663_, lean_object* v___x_664_, lean_object* v_____x_665_){
_start:
{
if (lean_obj_tag(v_____x_665_) == 1)
{
lean_object* v_head_666_; lean_object* v_fla_667_; uint8_t v___x_668_; 
v_head_666_ = lean_ctor_get(v_____x_665_, 0);
v_fla_667_ = lean_ctor_get(v_head_666_, 0);
v___x_668_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_667_);
if (v___x_668_ == 0)
{
lean_dec_ref_known(v_____x_665_, 2);
lean_dec_ref(v___x_664_);
lean_dec(v_pushOutput_663_);
lean_dec(v_toBind_662_);
lean_dec(v_activeTags_661_);
lean_dec(v_endTags_660_);
lean_dec_ref(v_inst_659_);
lean_dec_ref(v_inst_658_);
lean_dec(v_w_657_);
lean_inc(v_breakHere_656_);
return v_breakHere_656_;
}
else
{
lean_object* v___f_669_; lean_object* v___f_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___f_669_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4), 5, 4);
lean_closure_set(v___f_669_, 0, v_w_657_);
lean_closure_set(v___f_669_, 1, v_inst_658_);
lean_closure_set(v___f_669_, 2, v_inst_659_);
lean_closure_set(v___f_669_, 3, v_____x_665_);
lean_inc(v_toBind_662_);
v___f_670_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_670_, 0, v_endTags_660_);
lean_closure_set(v___f_670_, 1, v_activeTags_661_);
lean_closure_set(v___f_670_, 2, v_toBind_662_);
lean_closure_set(v___f_670_, 3, v___f_669_);
v___x_671_ = lean_apply_1(v_pushOutput_663_, v___x_664_);
v___x_672_ = lean_apply_4(v_toBind_662_, lean_box(0), lean_box(0), v___x_671_, v___f_670_);
return v___x_672_;
}
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v_____x_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_pushOutput_663_);
lean_dec(v_toBind_662_);
lean_dec(v_activeTags_661_);
lean_dec(v_endTags_660_);
lean_dec_ref(v_inst_659_);
lean_dec(v_w_657_);
v___x_673_ = lean_box(0);
v___x_674_ = l_instInhabitedOfMonad___redArg(v_inst_658_, v___x_673_);
v___x_675_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0));
v___x_676_ = l_panic___redArg(v___x_674_, v___x_675_);
lean_dec(v___x_674_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed(lean_object* v_breakHere_677_, lean_object* v_w_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_endTags_681_, lean_object* v_activeTags_682_, lean_object* v_toBind_683_, lean_object* v_pushOutput_684_, lean_object* v___x_685_, lean_object* v_____x_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(v_breakHere_677_, v_w_678_, v_inst_679_, v_inst_680_, v_endTags_681_, v_activeTags_682_, v_toBind_683_, v_pushOutput_684_, v___x_685_, v_____x_686_);
lean_dec(v_breakHere_677_);
return v_res_687_;
}
}
static lean_object* _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_689_ = lean_string_length(v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(lean_object* v_a_690_, lean_object* v_p_691_, lean_object* v___x_692_, lean_object* v_indent_693_, lean_object* v_activeTags_694_, lean_object* v_tail_695_, lean_object* v_fla_696_, uint8_t v_flb_697_, lean_object* v_tail_698_, lean_object* v_w_699_, lean_object* v_inst_700_, lean_object* v_inst_701_, lean_object* v_toBind_702_, lean_object* v_gs_x27_703_, lean_object* v_____r_704_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v_is_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_705_ = lean_string_utf8_next(v_a_690_, v_p_691_);
v___x_706_ = lean_string_utf8_extract(v_a_690_, v___x_705_, v___x_692_);
lean_dec(v___x_705_);
v___x_707_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
v___x_708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set(v___x_708_, 1, v_indent_693_);
lean_ctor_set(v___x_708_, 2, v_activeTags_694_);
v_is_709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_is_709_, 0, v___x_708_);
lean_ctor_set(v_is_709_, 1, v_tail_695_);
v___x_710_ = lean_box(1);
v___x_711_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_696_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec_ref(v_gs_x27_703_);
lean_inc_ref(v_inst_701_);
lean_inc_ref(v_inst_700_);
lean_inc(v_w_699_);
v___x_712_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_697_, v_is_709_, v_tail_698_, v_w_699_, v_inst_700_, v_inst_701_);
v___x_713_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_713_, 0, v_w_699_);
lean_closure_set(v___x_713_, 1, v_inst_700_);
lean_closure_set(v___x_713_, 2, v_inst_701_);
v___x_714_ = lean_apply_4(v_toBind_702_, lean_box(0), lean_box(0), v___x_712_, v___x_713_);
return v___x_714_;
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; 
lean_dec(v_toBind_702_);
lean_dec(v_tail_698_);
v___x_715_ = lean_apply_1(v_gs_x27_703_, v_is_709_);
v___x_716_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_699_, v_inst_700_, v_inst_701_, v___x_715_);
return v___x_716_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed(lean_object* v_a_717_, lean_object* v_p_718_, lean_object* v___x_719_, lean_object* v_indent_720_, lean_object* v_activeTags_721_, lean_object* v_tail_722_, lean_object* v_fla_723_, lean_object* v_flb_724_, lean_object* v_tail_725_, lean_object* v_w_726_, lean_object* v_inst_727_, lean_object* v_inst_728_, lean_object* v_toBind_729_, lean_object* v_gs_x27_730_, lean_object* v_____r_731_){
_start:
{
uint8_t v_flb_2100__boxed_732_; lean_object* v_res_733_; 
v_flb_2100__boxed_732_ = lean_unbox(v_flb_724_);
v_res_733_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(v_a_717_, v_p_718_, v___x_719_, v_indent_720_, v_activeTags_721_, v_tail_722_, v_fla_723_, v_flb_2100__boxed_732_, v_tail_725_, v_w_726_, v_inst_727_, v_inst_728_, v_toBind_729_, v_gs_x27_730_, v_____r_731_);
lean_dec(v_fla_723_);
lean_dec(v___x_719_);
lean_dec(v_p_718_);
lean_dec_ref(v_a_717_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(lean_object* v_activeTags_734_, lean_object* v_a_735_, lean_object* v_indent_736_, lean_object* v_tail_737_, lean_object* v_gs_x27_738_, lean_object* v_w_739_, lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_____r_742_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = lean_nat_add(v_activeTags_734_, v___x_743_);
v___x_745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_745_, 0, v_a_735_);
lean_ctor_set(v___x_745_, 1, v_indent_736_);
lean_ctor_set(v___x_745_, 2, v___x_744_);
v___x_746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v_tail_737_);
v___x_747_ = lean_apply_1(v_gs_x27_738_, v___x_746_);
v___x_748_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_739_, v_inst_740_, v_inst_741_, v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed(lean_object* v_activeTags_749_, lean_object* v_a_750_, lean_object* v_indent_751_, lean_object* v_tail_752_, lean_object* v_gs_x27_753_, lean_object* v_w_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_____r_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(v_activeTags_749_, v_a_750_, v_indent_751_, v_tail_752_, v_gs_x27_753_, v_w_754_, v_inst_755_, v_inst_756_, v_____r_757_);
lean_dec(v_activeTags_749_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(lean_object* v_w_759_, lean_object* v_inst_760_, lean_object* v_inst_761_, lean_object* v_x_762_){
_start:
{
if (lean_obj_tag(v_x_762_) == 0)
{
lean_object* v_toApplicative_763_; lean_object* v_toPure_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_toApplicative_763_ = lean_ctor_get(v_inst_760_, 0);
lean_inc_ref(v_toApplicative_763_);
lean_dec_ref(v_inst_761_);
lean_dec_ref(v_inst_760_);
lean_dec(v_w_759_);
v_toPure_764_ = lean_ctor_get(v_toApplicative_763_, 1);
lean_inc(v_toPure_764_);
lean_dec_ref(v_toApplicative_763_);
v___x_765_ = lean_box(0);
v___x_766_ = lean_apply_2(v_toPure_764_, lean_box(0), v___x_765_);
return v___x_766_;
}
else
{
lean_object* v_head_767_; lean_object* v_items_768_; 
v_head_767_ = lean_ctor_get(v_x_762_, 0);
v_items_768_ = lean_ctor_get(v_head_767_, 1);
lean_inc(v_items_768_);
if (lean_obj_tag(v_items_768_) == 0)
{
lean_object* v_tail_769_; 
v_tail_769_ = lean_ctor_get(v_x_762_, 1);
lean_inc(v_tail_769_);
lean_dec_ref_known(v_x_762_, 2);
v_x_762_ = v_tail_769_;
goto _start;
}
else
{
lean_object* v_head_771_; lean_object* v_toBind_772_; lean_object* v_tail_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_916_; 
lean_inc(v_head_767_);
v_head_771_ = lean_ctor_get(v_items_768_, 0);
lean_inc(v_head_771_);
v_toBind_772_ = lean_ctor_get(v_inst_760_, 1);
v_tail_773_ = lean_ctor_get(v_x_762_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v_x_762_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v_x_762_, 0);
lean_dec(v_unused_917_);
v___x_775_ = v_x_762_;
v_isShared_776_ = v_isSharedCheck_916_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_tail_773_);
lean_dec(v_x_762_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_916_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_fla_777_; uint8_t v_flb_778_; lean_object* v_tail_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_914_; 
v_fla_777_ = lean_ctor_get(v_head_767_, 0);
lean_inc(v_fla_777_);
v_flb_778_ = lean_ctor_get_uint8(v_head_767_, sizeof(void*)*2);
lean_dec(v_head_767_);
v_tail_779_ = lean_ctor_get(v_items_768_, 1);
v_isSharedCheck_914_ = !lean_is_exclusive(v_items_768_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v_items_768_, 0);
lean_dec(v_unused_915_);
v___x_781_ = v_items_768_;
v_isShared_782_ = v_isSharedCheck_914_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_tail_779_);
lean_dec(v_items_768_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_914_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v_f_783_; lean_object* v_indent_784_; lean_object* v_activeTags_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_913_; 
v_f_783_ = lean_ctor_get(v_head_771_, 0);
v_indent_784_ = lean_ctor_get(v_head_771_, 1);
v_activeTags_785_ = lean_ctor_get(v_head_771_, 2);
v_isSharedCheck_913_ = !lean_is_exclusive(v_head_771_);
if (v_isSharedCheck_913_ == 0)
{
v___x_787_ = v_head_771_;
v_isShared_788_ = v_isSharedCheck_913_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_activeTags_785_);
lean_inc(v_indent_784_);
lean_inc(v_f_783_);
lean_dec(v_head_771_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_913_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v_gs_x27_790_; 
v___x_789_ = lean_box(v_flb_778_);
lean_inc(v_tail_773_);
lean_inc(v_fla_777_);
v_gs_x27_790_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v_gs_x27_790_, 0, v_fla_777_);
lean_closure_set(v_gs_x27_790_, 1, v___x_789_);
lean_closure_set(v_gs_x27_790_, 2, v_tail_773_);
switch(lean_obj_tag(v_f_783_))
{
case 0:
{
lean_object* v_endTags_791_; lean_object* v___f_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
lean_inc(v_toBind_772_);
lean_del_object(v___x_787_);
lean_dec(v_indent_784_);
lean_del_object(v___x_781_);
lean_dec(v_fla_777_);
lean_del_object(v___x_775_);
lean_dec(v_tail_773_);
v_endTags_791_ = lean_ctor_get(v_inst_761_, 4);
lean_inc(v_endTags_791_);
v___f_792_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_792_, 0, v_gs_x27_790_);
lean_closure_set(v___f_792_, 1, v_tail_779_);
lean_closure_set(v___f_792_, 2, v_w_759_);
lean_closure_set(v___f_792_, 3, v_inst_760_);
lean_closure_set(v___f_792_, 4, v_inst_761_);
v___x_793_ = lean_apply_1(v_endTags_791_, v_activeTags_785_);
v___x_794_ = lean_apply_4(v_toBind_772_, lean_box(0), lean_box(0), v___x_793_, v___f_792_);
return v___x_794_;
}
case 1:
{
lean_inc(v_toBind_772_);
lean_del_object(v___x_787_);
lean_del_object(v___x_781_);
lean_del_object(v___x_775_);
if (v_flb_778_ == 0)
{
uint8_t v___x_795_; 
lean_dec(v_tail_773_);
v___x_795_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_777_);
lean_dec(v_fla_777_);
if (v___x_795_ == 0)
{
lean_object* v_pushNewline_796_; lean_object* v_endTags_797_; lean_object* v___f_798_; lean_object* v___f_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_pushNewline_796_ = lean_ctor_get(v_inst_761_, 1);
lean_inc(v_pushNewline_796_);
v_endTags_797_ = lean_ctor_get(v_inst_761_, 4);
lean_inc(v_endTags_797_);
v___f_798_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_798_, 0, v_gs_x27_790_);
lean_closure_set(v___f_798_, 1, v_tail_779_);
lean_closure_set(v___f_798_, 2, v_w_759_);
lean_closure_set(v___f_798_, 3, v_inst_760_);
lean_closure_set(v___f_798_, 4, v_inst_761_);
lean_inc(v_toBind_772_);
v___f_799_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_799_, 0, v_endTags_797_);
lean_closure_set(v___f_799_, 1, v_activeTags_785_);
lean_closure_set(v___f_799_, 2, v_toBind_772_);
lean_closure_set(v___f_799_, 3, v___f_798_);
v___x_800_ = l_Int_toNat(v_indent_784_);
lean_dec(v_indent_784_);
v___x_801_ = lean_apply_1(v_pushNewline_796_, v___x_800_);
v___x_802_ = lean_apply_4(v_toBind_772_, lean_box(0), lean_box(0), v___x_801_, v___f_799_);
return v___x_802_;
}
else
{
lean_object* v_pushOutput_803_; lean_object* v_endTags_804_; lean_object* v___f_805_; lean_object* v___f_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v_indent_784_);
v_pushOutput_803_ = lean_ctor_get(v_inst_761_, 0);
lean_inc(v_pushOutput_803_);
v_endTags_804_ = lean_ctor_get(v_inst_761_, 4);
lean_inc(v_endTags_804_);
v___f_805_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_805_, 0, v_gs_x27_790_);
lean_closure_set(v___f_805_, 1, v_tail_779_);
lean_closure_set(v___f_805_, 2, v_w_759_);
lean_closure_set(v___f_805_, 3, v_inst_760_);
lean_closure_set(v___f_805_, 4, v_inst_761_);
lean_inc(v_toBind_772_);
v___f_806_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_806_, 0, v_endTags_804_);
lean_closure_set(v___f_806_, 1, v_activeTags_785_);
lean_closure_set(v___f_806_, 2, v_toBind_772_);
lean_closure_set(v___f_806_, 3, v___f_805_);
v___x_807_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_808_ = lean_apply_1(v_pushOutput_803_, v___x_807_);
v___x_809_ = lean_apply_4(v_toBind_772_, lean_box(0), lean_box(0), v___x_808_, v___f_806_);
return v___x_809_;
}
}
else
{
lean_object* v_pushOutput_810_; lean_object* v_pushNewline_811_; lean_object* v_endTags_812_; lean_object* v___x_813_; lean_object* v___f_814_; lean_object* v___f_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v_breakHere_818_; uint8_t v___x_819_; 
lean_dec_ref(v_gs_x27_790_);
v_pushOutput_810_ = lean_ctor_get(v_inst_761_, 0);
v_pushNewline_811_ = lean_ctor_get(v_inst_761_, 1);
v_endTags_812_ = lean_ctor_get(v_inst_761_, 4);
v___x_813_ = lean_box(v_flb_778_);
lean_inc_n(v_toBind_772_, 3);
lean_inc_ref(v_inst_761_);
lean_inc_ref(v_inst_760_);
lean_inc(v_w_759_);
lean_inc(v_tail_773_);
lean_inc(v_tail_779_);
v___f_814_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_814_, 0, v___x_813_);
lean_closure_set(v___f_814_, 1, v_tail_779_);
lean_closure_set(v___f_814_, 2, v_tail_773_);
lean_closure_set(v___f_814_, 3, v_w_759_);
lean_closure_set(v___f_814_, 4, v_inst_760_);
lean_closure_set(v___f_814_, 5, v_inst_761_);
lean_closure_set(v___f_814_, 6, v_toBind_772_);
lean_inc(v_activeTags_785_);
lean_inc(v_endTags_812_);
v___f_815_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_815_, 0, v_endTags_812_);
lean_closure_set(v___f_815_, 1, v_activeTags_785_);
lean_closure_set(v___f_815_, 2, v_toBind_772_);
lean_closure_set(v___f_815_, 3, v___f_814_);
v___x_816_ = l_Int_toNat(v_indent_784_);
lean_dec(v_indent_784_);
lean_inc(v_pushNewline_811_);
v___x_817_ = lean_apply_1(v_pushNewline_811_, v___x_816_);
v_breakHere_818_ = lean_apply_4(v_toBind_772_, lean_box(0), lean_box(0), v___x_817_, v___f_815_);
v___x_819_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_777_);
lean_dec(v_fla_777_);
if (v___x_819_ == 0)
{
lean_dec(v_activeTags_785_);
lean_dec(v_tail_779_);
lean_dec(v_tail_773_);
lean_dec(v_toBind_772_);
lean_dec_ref(v_inst_761_);
lean_dec_ref(v_inst_760_);
lean_dec(v_w_759_);
return v_breakHere_818_;
}
else
{
lean_object* v___x_820_; lean_object* v___f_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_820_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
lean_inc(v_pushOutput_810_);
lean_inc(v_toBind_772_);
lean_inc(v_endTags_812_);
lean_inc_ref(v_inst_761_);
lean_inc_ref(v_inst_760_);
lean_inc(v_w_759_);
v___f_821_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_821_, 0, v_breakHere_818_);
lean_closure_set(v___f_821_, 1, v_w_759_);
lean_closure_set(v___f_821_, 2, v_inst_760_);
lean_closure_set(v___f_821_, 3, v_inst_761_);
lean_closure_set(v___f_821_, 4, v_endTags_812_);
lean_closure_set(v___f_821_, 5, v_activeTags_785_);
lean_closure_set(v___f_821_, 6, v_toBind_772_);
lean_closure_set(v___f_821_, 7, v_pushOutput_810_);
lean_closure_set(v___f_821_, 8, v___x_820_);
v___x_822_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_823_ = lean_nat_sub(v_w_759_, v___x_822_);
lean_dec(v_w_759_);
v___x_824_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_778_, v_tail_779_, v_tail_773_, v___x_823_, v_inst_760_, v_inst_761_);
v___x_825_ = lean_apply_4(v_toBind_772_, lean_box(0), lean_box(0), v___x_824_, v___f_821_);
return v___x_825_;
}
}
}
case 2:
{
uint8_t v_force_826_; lean_object* v___f_827_; lean_object* v___f_828_; lean_object* v___f_829_; uint8_t v___y_834_; uint8_t v___x_838_; 
lean_inc_n(v_toBind_772_, 3);
lean_del_object(v___x_787_);
lean_del_object(v___x_781_);
lean_del_object(v___x_775_);
lean_dec(v_tail_773_);
v_force_826_ = lean_ctor_get_uint8(v_f_783_, 0);
lean_dec_ref_known(v_f_783_, 0);
lean_inc_ref_n(v_inst_761_, 3);
v___f_827_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_827_, 0, v_gs_x27_790_);
lean_closure_set(v___f_827_, 1, v_tail_779_);
lean_closure_set(v___f_827_, 2, v_w_759_);
lean_closure_set(v___f_827_, 3, v_inst_760_);
lean_closure_set(v___f_827_, 4, v_inst_761_);
lean_inc_ref(v___f_827_);
lean_inc(v_activeTags_785_);
v___f_828_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9), 5, 4);
lean_closure_set(v___f_828_, 0, v_inst_761_);
lean_closure_set(v___f_828_, 1, v_activeTags_785_);
lean_closure_set(v___f_828_, 2, v_toBind_772_);
lean_closure_set(v___f_828_, 3, v___f_827_);
lean_inc_ref(v___f_828_);
v___f_829_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_829_, 0, v_indent_784_);
lean_closure_set(v___f_829_, 1, v_inst_761_);
lean_closure_set(v___f_829_, 2, v_toBind_772_);
lean_closure_set(v___f_829_, 3, v___f_828_);
lean_closure_set(v___f_829_, 4, v___f_828_);
v___x_838_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_777_);
lean_dec(v_fla_777_);
if (v___x_838_ == 0)
{
v___y_834_ = v___x_838_;
goto v___jp_833_;
}
else
{
if (v_force_826_ == 0)
{
v___y_834_ = v___x_838_;
goto v___jp_833_;
}
else
{
lean_dec_ref(v___f_827_);
lean_dec(v_activeTags_785_);
goto v___jp_830_;
}
}
v___jp_830_:
{
lean_object* v_currColumn_831_; lean_object* v___x_832_; 
v_currColumn_831_ = lean_ctor_get(v_inst_761_, 2);
lean_inc(v_currColumn_831_);
lean_dec_ref(v_inst_761_);
v___x_832_ = lean_apply_4(v_toBind_772_, lean_box(0), lean_box(0), v_currColumn_831_, v___f_829_);
return v___x_832_;
}
v___jp_833_:
{
if (v___y_834_ == 0)
{
lean_dec_ref(v___f_827_);
lean_dec(v_activeTags_785_);
goto v___jp_830_;
}
else
{
lean_object* v_endTags_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec_ref(v___f_829_);
v_endTags_835_ = lean_ctor_get(v_inst_761_, 4);
lean_inc(v_endTags_835_);
lean_dec_ref(v_inst_761_);
v___x_836_ = lean_apply_1(v_endTags_835_, v_activeTags_785_);
v___x_837_ = lean_apply_4(v_toBind_772_, lean_box(0), lean_box(0), v___x_836_, v___f_827_);
return v___x_837_;
}
}
}
case 3:
{
lean_object* v_a_839_; uint32_t v___x_840_; lean_object* v_p_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
lean_inc(v_toBind_772_);
lean_del_object(v___x_787_);
lean_del_object(v___x_781_);
lean_del_object(v___x_775_);
v_a_839_ = lean_ctor_get(v_f_783_, 0);
lean_inc_ref_n(v_a_839_, 2);
lean_dec_ref_known(v_f_783_, 1);
v___x_840_ = 10;
v_p_841_ = lean_string_posof(v_a_839_, v___x_840_);
v___x_842_ = lean_string_utf8_byte_size(v_a_839_);
v___x_843_ = lean_nat_dec_eq(v_p_841_, v___x_842_);
if (v___x_843_ == 0)
{
lean_object* v_pushOutput_844_; lean_object* v_pushNewline_845_; lean_object* v___x_846_; lean_object* v___f_847_; lean_object* v___f_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_pushOutput_844_ = lean_ctor_get(v_inst_761_, 0);
lean_inc(v_pushOutput_844_);
v_pushNewline_845_ = lean_ctor_get(v_inst_761_, 1);
lean_inc(v_pushNewline_845_);
v___x_846_ = lean_box(v_flb_778_);
lean_inc_n(v_toBind_772_, 2);
lean_inc(v_indent_784_);
lean_inc(v_p_841_);
lean_inc_ref(v_a_839_);
v___f_847_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed), 15, 14);
lean_closure_set(v___f_847_, 0, v_a_839_);
lean_closure_set(v___f_847_, 1, v_p_841_);
lean_closure_set(v___f_847_, 2, v___x_842_);
lean_closure_set(v___f_847_, 3, v_indent_784_);
lean_closure_set(v___f_847_, 4, v_activeTags_785_);
lean_closure_set(v___f_847_, 5, v_tail_779_);
lean_closure_set(v___f_847_, 6, v_fla_777_);
lean_closure_set(v___f_847_, 7, v___x_846_);
lean_closure_set(v___f_847_, 8, v_tail_773_);
lean_closure_set(v___f_847_, 9, v_w_759_);
lean_closure_set(v___f_847_, 10, v_inst_760_);
lean_closure_set(v___f_847_, 11, v_inst_761_);
lean_closure_set(v___f_847_, 12, v_toBind_772_);
lean_closure_set(v___f_847_, 13, v_gs_x27_790_);
v___f_848_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_848_, 0, v_indent_784_);
lean_closure_set(v___f_848_, 1, v_pushNewline_845_);
lean_closure_set(v___f_848_, 2, v_toBind_772_);
lean_closure_set(v___f_848_, 3, v___f_847_);
v___x_849_ = lean_unsigned_to_nat(0u);
v___x_850_ = lean_string_utf8_extract(v_a_839_, v___x_849_, v_p_841_);
lean_dec(v_p_841_);
lean_dec_ref(v_a_839_);
v___x_851_ = lean_apply_1(v_pushOutput_844_, v___x_850_);
v___x_852_ = lean_apply_4(v_toBind_772_, lean_box(0), lean_box(0), v___x_851_, v___f_848_);
return v___x_852_;
}
else
{
lean_object* v_pushOutput_853_; lean_object* v_endTags_854_; lean_object* v___f_855_; lean_object* v___f_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec(v_p_841_);
lean_dec(v_indent_784_);
lean_dec(v_fla_777_);
lean_dec(v_tail_773_);
v_pushOutput_853_ = lean_ctor_get(v_inst_761_, 0);
lean_inc(v_pushOutput_853_);
v_endTags_854_ = lean_ctor_get(v_inst_761_, 4);
lean_inc(v_endTags_854_);
v___f_855_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_855_, 0, v_gs_x27_790_);
lean_closure_set(v___f_855_, 1, v_tail_779_);
lean_closure_set(v___f_855_, 2, v_w_759_);
lean_closure_set(v___f_855_, 3, v_inst_760_);
lean_closure_set(v___f_855_, 4, v_inst_761_);
lean_inc(v_toBind_772_);
v___f_856_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_856_, 0, v_endTags_854_);
lean_closure_set(v___f_856_, 1, v_activeTags_785_);
lean_closure_set(v___f_856_, 2, v_toBind_772_);
lean_closure_set(v___f_856_, 3, v___f_855_);
v___x_857_ = lean_apply_1(v_pushOutput_853_, v_a_839_);
v___x_858_ = lean_apply_4(v_toBind_772_, lean_box(0), lean_box(0), v___x_857_, v___f_856_);
return v___x_858_;
}
}
case 4:
{
lean_object* v_indent_859_; lean_object* v_f_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
lean_dec_ref(v_gs_x27_790_);
lean_del_object(v___x_775_);
v_indent_859_ = lean_ctor_get(v_f_783_, 0);
lean_inc(v_indent_859_);
v_f_860_ = lean_ctor_get(v_f_783_, 1);
lean_inc(v_f_860_);
lean_dec_ref_known(v_f_783_, 2);
v___x_861_ = lean_int_add(v_indent_784_, v_indent_859_);
lean_dec(v_indent_859_);
lean_dec(v_indent_784_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v___x_861_);
lean_ctor_set(v___x_787_, 0, v_f_860_);
v___x_863_ = v___x_787_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_f_860_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_activeTags_785_);
v___x_863_ = v_reuseFailAlloc_869_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_865_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_863_);
v___x_865_ = v___x_781_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_tail_779_);
v___x_865_ = v_reuseFailAlloc_868_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_866_; 
v___x_866_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_777_, v_flb_778_, v_tail_773_, v___x_865_);
v_x_762_ = v___x_866_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_870_; lean_object* v_a_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
lean_dec_ref(v_gs_x27_790_);
v_a_870_ = lean_ctor_get(v_f_783_, 0);
lean_inc(v_a_870_);
v_a_871_ = lean_ctor_get(v_f_783_, 1);
lean_inc(v_a_871_);
lean_dec_ref_known(v_f_783_, 2);
v___x_872_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_784_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 2, v___x_872_);
lean_ctor_set(v___x_787_, 0, v_a_870_);
v___x_874_ = v___x_787_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_870_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_indent_784_);
lean_ctor_set(v_reuseFailAlloc_884_, 2, v___x_872_);
v___x_874_ = v_reuseFailAlloc_884_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_875_, 0, v_a_871_);
lean_ctor_set(v___x_875_, 1, v_indent_784_);
lean_ctor_set(v___x_875_, 2, v_activeTags_785_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_875_);
v___x_877_ = v___x_781_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_tail_779_);
v___x_877_ = v_reuseFailAlloc_883_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_879_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v___x_877_);
lean_ctor_set(v___x_775_, 0, v___x_874_);
v___x_879_ = v___x_775_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___x_877_);
v___x_879_ = v_reuseFailAlloc_882_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_880_; 
v___x_880_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_777_, v_flb_778_, v_tail_773_, v___x_879_);
v_x_762_ = v___x_880_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_885_; uint8_t v_behavior_886_; uint8_t v___x_887_; 
lean_dec_ref(v_gs_x27_790_);
lean_del_object(v___x_775_);
v_a_885_ = lean_ctor_get(v_f_783_, 0);
lean_inc(v_a_885_);
v_behavior_886_ = lean_ctor_get_uint8(v_f_783_, sizeof(void*)*1);
lean_dec_ref_known(v_f_783_, 1);
v___x_887_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_777_);
if (v___x_887_ == 0)
{
lean_object* v___x_889_; 
lean_inc(v_toBind_772_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v_a_885_);
v___x_889_ = v___x_787_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_885_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_indent_784_);
lean_ctor_set(v_reuseFailAlloc_898_, 2, v_activeTags_785_);
v___x_889_ = v_reuseFailAlloc_898_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = lean_box(0);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v___x_890_);
lean_ctor_set(v___x_781_, 0, v___x_889_);
v___x_892_ = v___x_781_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v___x_890_);
v___x_892_ = v_reuseFailAlloc_897_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_893_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_777_, v_flb_778_, v_tail_773_, v_tail_779_);
lean_inc_ref(v_inst_761_);
lean_inc_ref(v_inst_760_);
lean_inc(v_w_759_);
v___x_894_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_behavior_886_, v___x_892_, v___x_893_, v_w_759_, v_inst_760_, v_inst_761_);
v___x_895_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_895_, 0, v_w_759_);
lean_closure_set(v___x_895_, 1, v_inst_760_);
lean_closure_set(v___x_895_, 2, v_inst_761_);
v___x_896_ = lean_apply_4(v_toBind_772_, lean_box(0), lean_box(0), v___x_894_, v___x_895_);
return v___x_896_;
}
}
}
else
{
lean_object* v___x_900_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v_a_885_);
v___x_900_ = v___x_787_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_885_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_indent_784_);
lean_ctor_set(v_reuseFailAlloc_906_, 2, v_activeTags_785_);
v___x_900_ = v_reuseFailAlloc_906_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_902_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_900_);
v___x_902_ = v___x_781_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_tail_779_);
v___x_902_ = v_reuseFailAlloc_905_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_903_; 
v___x_903_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_777_, v_flb_778_, v_tail_773_, v___x_902_);
v_x_762_ = v___x_903_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_907_; lean_object* v_a_908_; lean_object* v_startTag_909_; lean_object* v___f_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
lean_inc(v_toBind_772_);
lean_del_object(v___x_787_);
lean_del_object(v___x_781_);
lean_dec(v_fla_777_);
lean_del_object(v___x_775_);
lean_dec(v_tail_773_);
v_a_907_ = lean_ctor_get(v_f_783_, 0);
lean_inc(v_a_907_);
v_a_908_ = lean_ctor_get(v_f_783_, 1);
lean_inc(v_a_908_);
lean_dec_ref_known(v_f_783_, 2);
v_startTag_909_ = lean_ctor_get(v_inst_761_, 3);
lean_inc(v_startTag_909_);
v___f_910_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed), 9, 8);
lean_closure_set(v___f_910_, 0, v_activeTags_785_);
lean_closure_set(v___f_910_, 1, v_a_908_);
lean_closure_set(v___f_910_, 2, v_indent_784_);
lean_closure_set(v___f_910_, 3, v_tail_779_);
lean_closure_set(v___f_910_, 4, v_gs_x27_790_);
lean_closure_set(v___f_910_, 5, v_w_759_);
lean_closure_set(v___f_910_, 6, v_inst_760_);
lean_closure_set(v___f_910_, 7, v_inst_761_);
v___x_911_ = lean_apply_1(v_startTag_909_, v_a_907_);
v___x_912_ = lean_apply_4(v_toBind_772_, lean_box(0), lean_box(0), v___x_911_, v___f_910_);
return v___x_912_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4(lean_object* v_w_918_, lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_____x_921_, lean_object* v_____r_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_918_, v_inst_919_, v_inst_920_, v_____x_921_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be(lean_object* v_m_924_, lean_object* v_w_925_, lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_x_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_925_, v_inst_926_, v_inst_927_, v_x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___redArg(lean_object* v_f_930_, lean_object* v_w_931_, lean_object* v_indent_932_, lean_object* v_inst_933_, lean_object* v_inst_934_){
_start:
{
lean_object* v___x_935_; uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_935_ = lean_box(1);
v___x_936_ = 0;
v___x_937_ = lean_nat_to_int(v_indent_932_);
v___x_938_ = lean_unsigned_to_nat(0u);
v___x_939_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_939_, 0, v_f_930_);
lean_ctor_set(v___x_939_, 1, v___x_937_);
lean_ctor_set(v___x_939_, 2, v___x_938_);
v___x_940_ = lean_box(0);
v___x_941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_942_, 0, v___x_935_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
lean_ctor_set_uint8(v___x_942_, sizeof(void*)*2, v___x_936_);
v___x_943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_940_);
v___x_944_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_931_, v_inst_933_, v_inst_934_, v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM(lean_object* v_m_945_, lean_object* v_f_946_, lean_object* v_w_947_, lean_object* v_indent_948_, lean_object* v_inst_949_, lean_object* v_inst_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Std_Format_prettyM___redArg(v_f_946_, v_w_947_, v_indent_948_, v_inst_949_, v_inst_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_bracket(lean_object* v_l_952_, lean_object* v_f_953_, lean_object* v_r_954_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; lean_object* v___x_963_; 
v___x_955_ = lean_string_length(v_l_952_);
v___x_956_ = lean_nat_to_int(v___x_955_);
v___x_957_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_957_, 0, v_l_952_);
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v_f_953_);
v___x_959_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_959_, 0, v_r_954_);
v___x_960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_956_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = 0;
v___x_963_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set_uint8(v___x_963_, sizeof(void*)*1, v___x_962_);
return v___x_963_;
}
}
static lean_object* _init_l_Std_Format_paren___closed__2(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_Std_Format_paren___closed__0));
v___x_967_ = lean_string_length(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_Std_Format_paren___closed__3(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_obj_once(&l_Std_Format_paren___closed__2, &l_Std_Format_paren___closed__2_once, _init_l_Std_Format_paren___closed__2);
v___x_969_ = lean_nat_to_int(v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_paren(lean_object* v_f_974_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; lean_object* v___x_982_; 
v___x_975_ = lean_obj_once(&l_Std_Format_paren___closed__3, &l_Std_Format_paren___closed__3_once, _init_l_Std_Format_paren___closed__3);
v___x_976_ = ((lean_object*)(l_Std_Format_paren___closed__4));
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v_f_974_);
v___x_978_ = ((lean_object*)(l_Std_Format_paren___closed__5));
v___x_979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_977_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_975_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = 0;
v___x_982_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*1, v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l_Std_Format_sbracket___closed__2(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l_Std_Format_sbracket___closed__0));
v___x_986_ = lean_string_length(v___x_985_);
return v___x_986_;
}
}
static lean_object* _init_l_Std_Format_sbracket___closed__3(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_obj_once(&l_Std_Format_sbracket___closed__2, &l_Std_Format_sbracket___closed__2_once, _init_l_Std_Format_sbracket___closed__2);
v___x_988_ = lean_nat_to_int(v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_sbracket(lean_object* v_f_993_){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; lean_object* v___x_1001_; 
v___x_994_ = lean_obj_once(&l_Std_Format_sbracket___closed__3, &l_Std_Format_sbracket___closed__3_once, _init_l_Std_Format_sbracket___closed__3);
v___x_995_ = ((lean_object*)(l_Std_Format_sbracket___closed__4));
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v_f_993_);
v___x_997_ = ((lean_object*)(l_Std_Format_sbracket___closed__5));
v___x_998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_994_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = 0;
v___x_1001_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*1, v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_bracketFill(lean_object* v_l_1002_, lean_object* v_f_1003_, lean_object* v_r_1004_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1005_ = lean_string_length(v_l_1002_);
v___x_1006_ = lean_nat_to_int(v___x_1005_);
v___x_1007_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1007_, 0, v_l_1002_);
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v_f_1003_);
v___x_1009_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1009_, 0, v_r_1004_);
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1006_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = l_Std_Format_fill(v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l_Std_Format_defIndent(void){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_unsigned_to_nat(2u);
return v___x_1013_;
}
}
static uint8_t _init_l_Std_Format_defUnicode(void){
_start:
{
uint8_t v___x_1014_; 
v___x_1014_ = 1;
return v___x_1014_;
}
}
static lean_object* _init_l_Std_Format_defWidth(void){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_unsigned_to_nat(120u);
return v___x_1015_;
}
}
static lean_object* _init_l_Std_Format_nestD___closed__0(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_unsigned_to_nat(2u);
v___x_1017_ = lean_nat_to_int(v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nestD(lean_object* v_f_1018_){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_obj_once(&l_Std_Format_nestD___closed__0, &l_Std_Format_nestD___closed__0_once, _init_l_Std_Format_nestD___closed__0);
v___x_1020_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v_f_1018_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_indentD(lean_object* v_f_1021_){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = lean_box(1);
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v_f_1021_);
v___x_1024_ = l_Std_Format_nestD(v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(lean_object* v_s_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_out_1027_; lean_object* v_column_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1040_; 
v_out_1027_ = lean_ctor_get(v___y_1026_, 0);
v_column_1028_ = lean_ctor_get(v___y_1026_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___y_1026_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1030_ = v___y_1026_;
v_isShared_1031_ = v_isSharedCheck_1040_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_column_1028_);
lean_inc(v_out_1027_);
lean_dec(v___y_1026_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1040_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1032_ = lean_box(0);
v___x_1033_ = lean_string_append(v_out_1027_, v_s_1025_);
v___x_1034_ = lean_string_length(v_s_1025_);
v___x_1035_ = lean_nat_add(v_column_1028_, v___x_1034_);
lean_dec(v___x_1034_);
lean_dec(v_column_1028_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 1, v___x_1035_);
lean_ctor_set(v___x_1030_, 0, v___x_1033_);
v___x_1037_ = v___x_1030_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1032_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0___boxed(lean_object* v_s_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(v_s_1041_, v___y_1042_);
lean_dec_ref(v_s_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1(lean_object* v_indent_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_out_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1060_; 
v_out_1047_ = lean_ctor_get(v___y_1046_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___y_1046_);
if (v_isSharedCheck_1060_ == 0)
{
lean_object* v_unused_1061_; 
v_unused_1061_ = lean_ctor_get(v___y_1046_, 1);
lean_dec(v_unused_1061_);
v___x_1049_ = v___y_1046_;
v_isShared_1050_ = v_isSharedCheck_1060_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_out_1047_);
lean_dec(v___y_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1060_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; uint32_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1051_ = lean_box(0);
v___x_1052_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1053_ = 32;
lean_inc(v_indent_1045_);
v___x_1054_ = lean_string_pushn(v___x_1052_, v___x_1053_, v_indent_1045_);
v___x_1055_ = lean_string_append(v_out_1047_, v___x_1054_);
lean_dec_ref(v___x_1054_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 1, v_indent_1045_);
lean_ctor_set(v___x_1049_, 0, v___x_1055_);
v___x_1057_ = v___x_1049_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_indent_1045_);
v___x_1057_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1051_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
return v___x_1058_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__2(lean_object* v_____do__lift_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_column_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_column_1064_ = lean_ctor_get(v_____do__lift_1062_, 1);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_____do__lift_1062_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v_____do__lift_1062_, 0);
lean_dec(v_unused_1072_);
v___x_1066_ = v_____do__lift_1062_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_column_1064_);
lean_dec(v_____do__lift_1062_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v___y_1063_);
lean_ctor_set(v___x_1066_, 0, v_column_1064_);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_column_1064_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___y_1063_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(lean_object* v_x_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = lean_box(0);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v___y_1074_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3___boxed(lean_object* v_x_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(v_x_1077_, v___y_1078_);
lean_dec(v_x_1077_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(uint8_t v_flb_1115_, lean_object* v_items_1116_, lean_object* v_gs_1117_, lean_object* v_w_1118_, lean_object* v___y_1119_){
_start:
{
uint8_t v___y_1121_; lean_object* v_column_1126_; uint8_t v___x_1127_; uint8_t v___x_1128_; lean_object* v___x_1129_; lean_object* v_g_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v_r_1134_; lean_object* v___y_1136_; uint8_t v_foundLine_1141_; lean_object* v_space_1142_; uint8_t v___y_1144_; uint8_t v___x_1158_; 
v_column_1126_ = lean_ctor_get(v___y_1119_, 1);
v___x_1127_ = 0;
v___x_1128_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_1115_, v___x_1127_);
v___x_1129_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1129_, 0, v___x_1128_);
lean_inc(v_items_1116_);
v_g_1130_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_1130_, 0, v___x_1129_);
lean_ctor_set(v_g_1130_, 1, v_items_1116_);
lean_ctor_set_uint8(v_g_1130_, sizeof(void*)*2, v_flb_1115_);
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1132_, 0, v_g_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = lean_nat_sub(v_w_1118_, v_column_1126_);
lean_inc(v___x_1133_);
lean_inc(v_column_1126_);
v_r_1134_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_1132_, v_column_1126_, v___x_1133_);
v_foundLine_1141_ = lean_ctor_get_uint8(v_r_1134_, sizeof(void*)*1);
v_space_1142_ = lean_ctor_get(v_r_1134_, 0);
lean_inc(v_space_1142_);
v___x_1158_ = lean_nat_dec_lt(v___x_1133_, v_space_1142_);
if (v___x_1158_ == 0)
{
v___y_1144_ = v_foundLine_1141_;
goto v___jp_1143_;
}
else
{
v___y_1144_ = v___x_1158_;
goto v___jp_1143_;
}
v___jp_1120_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1122_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1122_, 0, v___y_1121_);
v___x_1123_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
lean_ctor_set(v___x_1123_, 1, v_items_1116_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*2, v_flb_1115_);
v___x_1124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
lean_ctor_set(v___x_1124_, 1, v_gs_1117_);
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
lean_ctor_set(v___x_1125_, 1, v___y_1119_);
return v___x_1125_;
}
v___jp_1135_:
{
uint8_t v_foundFlattenedHardLine_1137_; 
v_foundFlattenedHardLine_1137_ = lean_ctor_get_uint8(v_r_1134_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_1134_);
if (v_foundFlattenedHardLine_1137_ == 0)
{
lean_object* v_space_1138_; uint8_t v___x_1139_; 
v_space_1138_ = lean_ctor_get(v___y_1136_, 0);
lean_inc(v_space_1138_);
lean_dec_ref(v___y_1136_);
v___x_1139_ = lean_nat_dec_le(v_space_1138_, v___x_1133_);
lean_dec(v___x_1133_);
lean_dec(v_space_1138_);
v___y_1121_ = v___x_1139_;
goto v___jp_1120_;
}
else
{
uint8_t v___x_1140_; 
lean_dec_ref(v___y_1136_);
lean_dec(v___x_1133_);
v___x_1140_ = 0;
v___y_1121_ = v___x_1140_;
goto v___jp_1120_;
}
}
v___jp_1143_:
{
if (v___y_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v_r_u2082_1146_; uint8_t v_foundLine_1147_; uint8_t v_foundFlattenedHardLine_1148_; lean_object* v_space_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1157_; 
v___x_1145_ = lean_nat_sub(v___x_1133_, v_space_1142_);
lean_inc(v_column_1126_);
lean_inc(v_gs_1117_);
v_r_u2082_1146_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_1117_, v_column_1126_, v___x_1145_);
v_foundLine_1147_ = lean_ctor_get_uint8(v_r_u2082_1146_, sizeof(void*)*1);
v_foundFlattenedHardLine_1148_ = lean_ctor_get_uint8(v_r_u2082_1146_, sizeof(void*)*1 + 1);
v_space_1149_ = lean_ctor_get(v_r_u2082_1146_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_r_u2082_1146_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1151_ = v_r_u2082_1146_;
v_isShared_1152_ = v_isSharedCheck_1157_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_space_1149_);
lean_dec(v_r_u2082_1146_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1157_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = lean_nat_add(v_space_1142_, v_space_1149_);
lean_dec(v_space_1149_);
lean_dec(v_space_1142_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1153_);
v___x_1155_ = v___x_1151_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
lean_ctor_set_uint8(v_reuseFailAlloc_1156_, sizeof(void*)*1, v_foundLine_1147_);
lean_ctor_set_uint8(v_reuseFailAlloc_1156_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_1148_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
v___y_1136_ = v___x_1155_;
goto v___jp_1135_;
}
}
}
else
{
lean_dec(v_space_1142_);
lean_inc_ref(v_r_1134_);
v___y_1136_ = v_r_1134_;
goto v___jp_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1___boxed(lean_object* v_flb_1159_, lean_object* v_items_1160_, lean_object* v_gs_1161_, lean_object* v_w_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v_flb_boxed_1164_; lean_object* v_res_1165_; 
v_flb_boxed_1164_ = lean_unbox(v_flb_1159_);
v_res_1165_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_boxed_1164_, v_items_1160_, v_gs_1161_, v_w_1162_, v___y_1163_);
lean_dec(v_w_1162_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(lean_object* v_msg_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___f_1182_; lean_object* v___f_1183_; lean_object* v___f_1184_; lean_object* v___f_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_4858__overap_1194_; lean_object* v___x_1195_; 
v___f_1182_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0));
v___f_1183_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1));
v___f_1184_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2));
v___f_1185_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3));
v___x_1186_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4));
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v___f_1182_);
v___x_1188_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5));
v___x_1189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
lean_ctor_set(v___x_1189_, 2, v___f_1183_);
lean_ctor_set(v___x_1189_, 3, v___f_1184_);
lean_ctor_set(v___x_1189_, 4, v___f_1185_);
v___x_1190_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6));
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = lean_box(0);
v___x_1193_ = l_instInhabitedOfMonad___redArg(v___x_1191_, v___x_1192_);
v___x_4858__overap_1194_ = lean_panic_fn_borrowed(v___x_1193_, v_msg_1180_);
lean_dec(v___x_1193_);
v___x_1195_ = lean_apply_1(v___x_4858__overap_1194_, v___y_1181_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(lean_object* v_w_1196_, lean_object* v_x_1197_, lean_object* v___y_1198_){
_start:
{
if (lean_obj_tag(v_x_1197_) == 0)
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_box(0);
v___x_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v___y_1198_);
return v___x_1200_;
}
else
{
lean_object* v_head_1201_; lean_object* v_items_1202_; 
v_head_1201_ = lean_ctor_get(v_x_1197_, 0);
v_items_1202_ = lean_ctor_get(v_head_1201_, 1);
lean_inc(v_items_1202_);
if (lean_obj_tag(v_items_1202_) == 0)
{
lean_object* v_tail_1203_; 
v_tail_1203_ = lean_ctor_get(v_x_1197_, 1);
lean_inc(v_tail_1203_);
lean_dec_ref_known(v_x_1197_, 2);
v_x_1197_ = v_tail_1203_;
goto _start;
}
else
{
lean_object* v_head_1205_; lean_object* v_tail_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1476_; 
lean_inc(v_head_1201_);
v_head_1205_ = lean_ctor_get(v_items_1202_, 0);
lean_inc(v_head_1205_);
v_tail_1206_ = lean_ctor_get(v_x_1197_, 1);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_x_1197_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; 
v_unused_1477_ = lean_ctor_get(v_x_1197_, 0);
lean_dec(v_unused_1477_);
v___x_1208_ = v_x_1197_;
v_isShared_1209_ = v_isSharedCheck_1476_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_tail_1206_);
lean_dec(v_x_1197_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1476_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v_fla_1210_; uint8_t v_flb_1211_; lean_object* v_tail_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1474_; 
v_fla_1210_ = lean_ctor_get(v_head_1201_, 0);
lean_inc(v_fla_1210_);
v_flb_1211_ = lean_ctor_get_uint8(v_head_1201_, sizeof(void*)*2);
lean_dec(v_head_1201_);
v_tail_1212_ = lean_ctor_get(v_items_1202_, 1);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_items_1202_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; 
v_unused_1475_ = lean_ctor_get(v_items_1202_, 0);
lean_dec(v_unused_1475_);
v___x_1214_ = v_items_1202_;
v_isShared_1215_ = v_isSharedCheck_1474_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_tail_1212_);
lean_dec(v_items_1202_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1474_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v_f_1216_; lean_object* v_indent_1217_; lean_object* v_activeTags_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1473_; 
v_f_1216_ = lean_ctor_get(v_head_1205_, 0);
v_indent_1217_ = lean_ctor_get(v_head_1205_, 1);
v_activeTags_1218_ = lean_ctor_get(v_head_1205_, 2);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_head_1205_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1220_ = v_head_1205_;
v_isShared_1221_ = v_isSharedCheck_1473_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_activeTags_1218_);
lean_inc(v_indent_1217_);
lean_inc(v_f_1216_);
lean_dec(v_head_1205_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1473_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
uint8_t v___y_1255_; 
switch(lean_obj_tag(v_f_1216_))
{
case 0:
{
lean_object* v___x_1258_; 
lean_del_object(v___x_1220_);
lean_dec(v_activeTags_1218_);
lean_dec(v_indent_1217_);
lean_del_object(v___x_1214_);
lean_del_object(v___x_1208_);
v___x_1258_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1210_, v_flb_1211_, v_tail_1206_, v_tail_1212_);
v_x_1197_ = v___x_1258_;
goto _start;
}
case 1:
{
lean_del_object(v___x_1220_);
lean_dec(v_activeTags_1218_);
lean_del_object(v___x_1214_);
lean_del_object(v___x_1208_);
if (v_flb_1211_ == 0)
{
uint8_t v___x_1260_; 
v___x_1260_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1210_);
if (v___x_1260_ == 0)
{
lean_object* v_out_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1275_; 
v_out_1261_ = lean_ctor_get(v___y_1198_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___y_1198_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v___y_1198_, 1);
lean_dec(v_unused_1276_);
v___x_1263_ = v___y_1198_;
v_isShared_1264_ = v_isSharedCheck_1275_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_out_1261_);
lean_dec(v___y_1198_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1275_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; uint32_t v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1265_ = l_Int_toNat(v_indent_1217_);
lean_dec(v_indent_1217_);
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
v___x_1272_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1210_, v_flb_1211_, v_tail_1206_, v_tail_1212_);
v_x_1197_ = v___x_1272_;
v___y_1198_ = v___x_1271_;
goto _start;
}
}
}
else
{
lean_object* v_out_1277_; lean_object* v_column_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1291_; 
lean_dec(v_indent_1217_);
v_out_1277_ = lean_ctor_get(v___y_1198_, 0);
v_column_1278_ = lean_ctor_get(v___y_1198_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___y_1198_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1280_ = v___y_1198_;
v_isShared_1281_ = v_isSharedCheck_1291_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_column_1278_);
lean_inc(v_out_1277_);
lean_dec(v___y_1198_);
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
v___x_1288_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1210_, v_flb_1211_, v_tail_1206_, v_tail_1212_);
v_x_1197_ = v___x_1288_;
v___y_1198_ = v___x_1287_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = l_Int_toNat(v_indent_1217_);
lean_dec(v_indent_1217_);
v___x_1293_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1210_);
lean_dec(v_fla_1210_);
if (v___x_1293_ == 0)
{
lean_object* v_out_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1309_; 
v_out_1294_ = lean_ctor_get(v___y_1198_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___y_1198_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v___y_1198_, 1);
lean_dec(v_unused_1310_);
v___x_1296_ = v___y_1198_;
v_isShared_1297_ = v_isSharedCheck_1309_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_out_1294_);
lean_dec(v___y_1198_);
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
v___x_1304_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1211_, v_tail_1212_, v_tail_1206_, v_w_1196_, v___x_1303_);
v_fst_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_fst_1305_);
v_snd_1306_ = lean_ctor_get(v___x_1304_, 1);
lean_inc(v_snd_1306_);
lean_dec_ref(v___x_1304_);
v_x_1197_ = v_fst_1305_;
v___y_1198_ = v_snd_1306_;
goto _start;
}
}
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v_fst_1315_; 
v___x_1311_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_1312_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_1313_ = lean_nat_sub(v_w_1196_, v___x_1312_);
lean_inc(v_tail_1206_);
lean_inc(v_tail_1212_);
v___x_1314_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1211_, v_tail_1212_, v_tail_1206_, v___x_1313_, v___y_1198_);
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
v___x_1330_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1211_, v_tail_1212_, v_tail_1206_, v_w_1196_, v___x_1329_);
v_fst_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_fst_1331_);
v_snd_1332_ = lean_ctor_get(v___x_1330_, 1);
lean_inc(v_snd_1332_);
lean_dec_ref(v___x_1330_);
v_x_1197_ = v_fst_1331_;
v___y_1198_ = v_snd_1332_;
goto _start;
}
}
}
else
{
lean_object* v_out_1337_; lean_object* v_column_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1348_; 
lean_dec(v___x_1292_);
lean_dec(v_tail_1212_);
lean_dec(v_tail_1206_);
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
v_x_1197_ = v_fst_1315_;
v___y_1198_ = v___x_1345_;
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
lean_dec(v_tail_1212_);
lean_dec(v_tail_1206_);
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
lean_del_object(v___x_1220_);
lean_dec(v_activeTags_1218_);
lean_del_object(v___x_1214_);
lean_del_object(v___x_1208_);
v_force_1352_ = lean_ctor_get_uint8(v_f_1216_, 0);
lean_dec_ref_known(v_f_1216_, 0);
v___x_1353_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1210_);
if (v___x_1353_ == 0)
{
v___y_1255_ = v___x_1353_;
goto v___jp_1254_;
}
else
{
if (v_force_1352_ == 0)
{
v___y_1255_ = v___x_1353_;
goto v___jp_1254_;
}
else
{
goto v___jp_1222_;
}
}
}
case 3:
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1412_; 
lean_del_object(v___x_1208_);
v_a_1354_ = lean_ctor_get(v_f_1216_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_f_1216_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1356_ = v_f_1216_;
v_isShared_1357_ = v_isSharedCheck_1412_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v_f_1216_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1412_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
uint32_t v___x_1358_; lean_object* v_p_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1358_ = 10;
lean_inc_ref(v_a_1354_);
v_p_1359_ = lean_string_posof(v_a_1354_, v___x_1358_);
v___x_1360_ = lean_string_utf8_byte_size(v_a_1354_);
v___x_1361_ = lean_nat_dec_eq(v_p_1359_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_object* v_out_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1396_; 
v_out_1362_ = lean_ctor_get(v___y_1198_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___y_1198_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; 
v_unused_1397_ = lean_ctor_get(v___y_1198_, 1);
lean_dec(v_unused_1397_);
v___x_1364_ = v___y_1198_;
v_isShared_1365_ = v_isSharedCheck_1396_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_out_1362_);
lean_dec(v___y_1198_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1396_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; uint32_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1366_ = lean_unsigned_to_nat(0u);
v___x_1367_ = lean_string_utf8_extract(v_a_1354_, v___x_1366_, v_p_1359_);
v___x_1368_ = lean_string_append(v_out_1362_, v___x_1367_);
lean_dec_ref(v___x_1367_);
v___x_1369_ = l_Int_toNat(v_indent_1217_);
v___x_1370_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1371_ = 32;
lean_inc(v___x_1369_);
v___x_1372_ = lean_string_pushn(v___x_1370_, v___x_1371_, v___x_1369_);
v___x_1373_ = lean_string_append(v___x_1368_, v___x_1372_);
lean_dec_ref(v___x_1372_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v___x_1369_);
lean_ctor_set(v___x_1364_, 0, v___x_1373_);
v___x_1375_ = v___x_1364_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v___x_1369_);
v___x_1375_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1376_ = lean_string_utf8_next(v_a_1354_, v_p_1359_);
lean_dec(v_p_1359_);
v___x_1377_ = lean_string_utf8_extract(v_a_1354_, v___x_1376_, v___x_1360_);
lean_dec(v___x_1376_);
lean_dec_ref(v_a_1354_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 0, v___x_1377_);
v___x_1379_ = v___x_1356_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1381_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1379_);
v___x_1381_ = v___x_1220_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_indent_1217_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_activeTags_1218_);
v___x_1381_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v_is_1383_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1381_);
v_is_1383_ = v___x_1214_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_tail_1212_);
v_is_1383_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1384_ = lean_box(1);
v___x_1385_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_1210_, v___x_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v_fst_1387_; lean_object* v_snd_1388_; 
lean_dec(v_fla_1210_);
v___x_1386_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1211_, v_is_1383_, v_tail_1206_, v_w_1196_, v___x_1375_);
v_fst_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_fst_1387_);
v_snd_1388_ = lean_ctor_get(v___x_1386_, 1);
lean_inc(v_snd_1388_);
lean_dec_ref(v___x_1386_);
v_x_1197_ = v_fst_1387_;
v___y_1198_ = v_snd_1388_;
goto _start;
}
else
{
lean_object* v___x_1390_; 
v___x_1390_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1210_, v_flb_1211_, v_tail_1206_, v_is_1383_);
v_x_1197_ = v___x_1390_;
v___y_1198_ = v___x_1375_;
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
lean_object* v_out_1398_; lean_object* v_column_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1411_; 
lean_dec(v_p_1359_);
lean_del_object(v___x_1356_);
lean_del_object(v___x_1220_);
lean_dec(v_activeTags_1218_);
lean_dec(v_indent_1217_);
lean_del_object(v___x_1214_);
v_out_1398_ = lean_ctor_get(v___y_1198_, 0);
v_column_1399_ = lean_ctor_get(v___y_1198_, 1);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___y_1198_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1401_ = v___y_1198_;
v_isShared_1402_ = v_isSharedCheck_1411_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_column_1399_);
lean_inc(v_out_1398_);
lean_dec(v___y_1198_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1411_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1403_ = lean_string_append(v_out_1398_, v_a_1354_);
v___x_1404_ = lean_string_length(v_a_1354_);
lean_dec_ref(v_a_1354_);
v___x_1405_ = lean_nat_add(v_column_1399_, v___x_1404_);
lean_dec(v___x_1404_);
lean_dec(v_column_1399_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 1, v___x_1405_);
lean_ctor_set(v___x_1401_, 0, v___x_1403_);
v___x_1407_ = v___x_1401_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; 
v___x_1408_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1210_, v_flb_1211_, v_tail_1206_, v_tail_1212_);
v_x_1197_ = v___x_1408_;
v___y_1198_ = v___x_1407_;
goto _start;
}
}
}
}
}
case 4:
{
lean_object* v_indent_1413_; lean_object* v_f_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
lean_del_object(v___x_1208_);
v_indent_1413_ = lean_ctor_get(v_f_1216_, 0);
lean_inc(v_indent_1413_);
v_f_1414_ = lean_ctor_get(v_f_1216_, 1);
lean_inc(v_f_1414_);
lean_dec_ref_known(v_f_1216_, 2);
v___x_1415_ = lean_int_add(v_indent_1217_, v_indent_1413_);
lean_dec(v_indent_1413_);
lean_dec(v_indent_1217_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 1, v___x_1415_);
lean_ctor_set(v___x_1220_, 0, v_f_1414_);
v___x_1417_ = v___x_1220_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_f_1414_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v_activeTags_1218_);
v___x_1417_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1419_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1417_);
v___x_1419_ = v___x_1214_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_tail_1212_);
v___x_1419_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1420_; 
v___x_1420_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1210_, v_flb_1211_, v_tail_1206_, v___x_1419_);
v_x_1197_ = v___x_1420_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_1424_; lean_object* v_a_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
v_a_1424_ = lean_ctor_get(v_f_1216_, 0);
lean_inc(v_a_1424_);
v_a_1425_ = lean_ctor_get(v_f_1216_, 1);
lean_inc(v_a_1425_);
lean_dec_ref_known(v_f_1216_, 2);
v___x_1426_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_1217_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 2, v___x_1426_);
lean_ctor_set(v___x_1220_, 0, v_a_1424_);
v___x_1428_ = v___x_1220_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1424_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_indent_1217_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1429_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1429_, 0, v_a_1425_);
lean_ctor_set(v___x_1429_, 1, v_indent_1217_);
lean_ctor_set(v___x_1429_, 2, v_activeTags_1218_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1429_);
v___x_1431_ = v___x_1214_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_tail_1212_);
v___x_1431_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1433_; 
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 1, v___x_1431_);
lean_ctor_set(v___x_1208_, 0, v___x_1428_);
v___x_1433_ = v___x_1208_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; 
v___x_1434_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1210_, v_flb_1211_, v_tail_1206_, v___x_1433_);
v_x_1197_ = v___x_1434_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_1439_; uint8_t v_behavior_1440_; uint8_t v___x_1441_; 
lean_del_object(v___x_1208_);
v_a_1439_ = lean_ctor_get(v_f_1216_, 0);
lean_inc(v_a_1439_);
v_behavior_1440_ = lean_ctor_get_uint8(v_f_1216_, sizeof(void*)*1);
lean_dec_ref_known(v_f_1216_, 1);
v___x_1441_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1210_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1443_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v_a_1439_);
v___x_1443_ = v___x_1220_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1439_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_indent_1217_);
lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_activeTags_1218_);
v___x_1443_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = lean_box(0);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 1, v___x_1444_);
lean_ctor_set(v___x_1214_, 0, v___x_1443_);
v___x_1446_ = v___x_1214_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v_fst_1449_; lean_object* v_snd_1450_; 
v___x_1447_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1210_, v_flb_1211_, v_tail_1206_, v_tail_1212_);
v___x_1448_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_behavior_1440_, v___x_1446_, v___x_1447_, v_w_1196_, v___y_1198_);
v_fst_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_fst_1449_);
v_snd_1450_ = lean_ctor_get(v___x_1448_, 1);
lean_inc(v_snd_1450_);
lean_dec_ref(v___x_1448_);
v_x_1197_ = v_fst_1449_;
v___y_1198_ = v_snd_1450_;
goto _start;
}
}
}
else
{
lean_object* v___x_1455_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v_a_1439_);
v___x_1455_ = v___x_1220_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1439_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_indent_1217_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_activeTags_1218_);
v___x_1455_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1457_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1455_);
v___x_1457_ = v___x_1214_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_tail_1212_);
v___x_1457_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; 
v___x_1458_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1210_, v_flb_1211_, v_tail_1206_, v___x_1457_);
v_x_1197_ = v___x_1458_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
lean_del_object(v___x_1208_);
v_a_1462_ = lean_ctor_get(v_f_1216_, 1);
lean_inc(v_a_1462_);
lean_dec_ref_known(v_f_1216_, 2);
v___x_1463_ = lean_unsigned_to_nat(1u);
v___x_1464_ = lean_nat_add(v_activeTags_1218_, v___x_1463_);
lean_dec(v_activeTags_1218_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 2, v___x_1464_);
lean_ctor_set(v___x_1220_, 0, v_a_1462_);
v___x_1466_ = v___x_1220_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1462_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_indent_1217_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1468_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1466_);
v___x_1468_ = v___x_1214_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_tail_1212_);
v___x_1468_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1469_; 
v___x_1469_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1210_, v_flb_1211_, v_tail_1206_, v___x_1468_);
v_x_1197_ = v___x_1469_;
goto _start;
}
}
}
}
v___jp_1222_:
{
lean_object* v_out_1223_; lean_object* v_column_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1253_; 
v_out_1223_ = lean_ctor_get(v___y_1198_, 0);
v_column_1224_ = lean_ctor_get(v___y_1198_, 1);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___y_1198_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1226_ = v___y_1198_;
v_isShared_1227_ = v_isSharedCheck_1253_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_column_1224_);
lean_inc(v_out_1223_);
lean_dec(v___y_1198_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1253_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; uint8_t v___x_1229_; 
lean_inc(v_column_1224_);
v___x_1228_ = lean_nat_to_int(v_column_1224_);
v___x_1229_ = lean_int_dec_lt(v___x_1228_, v_indent_1217_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; uint32_t v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
lean_dec(v___x_1228_);
lean_dec(v_column_1224_);
v___x_1230_ = l_Int_toNat(v_indent_1217_);
lean_dec(v_indent_1217_);
v___x_1231_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1232_ = 32;
lean_inc(v___x_1230_);
v___x_1233_ = lean_string_pushn(v___x_1231_, v___x_1232_, v___x_1230_);
v___x_1234_ = lean_string_append(v_out_1223_, v___x_1233_);
lean_dec_ref(v___x_1233_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v___x_1230_);
lean_ctor_set(v___x_1226_, 0, v___x_1234_);
v___x_1236_ = v___x_1226_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v___x_1230_);
v___x_1236_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; 
v___x_1237_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1210_, v_flb_1211_, v_tail_1206_, v_tail_1212_);
v_x_1197_ = v___x_1237_;
v___y_1198_ = v___x_1236_;
goto _start;
}
}
else
{
lean_object* v___x_1240_; uint32_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1240_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_1241_ = 32;
v___x_1242_ = lean_int_sub(v_indent_1217_, v___x_1228_);
lean_dec(v___x_1228_);
lean_dec(v_indent_1217_);
v___x_1243_ = l_Int_toNat(v___x_1242_);
lean_dec(v___x_1242_);
v___x_1244_ = lean_string_pushn(v___x_1240_, v___x_1241_, v___x_1243_);
v___x_1245_ = lean_string_append(v_out_1223_, v___x_1244_);
v___x_1246_ = lean_string_length(v___x_1244_);
lean_dec_ref(v___x_1244_);
v___x_1247_ = lean_nat_add(v_column_1224_, v___x_1246_);
lean_dec(v___x_1246_);
lean_dec(v_column_1224_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v___x_1247_);
lean_ctor_set(v___x_1226_, 0, v___x_1245_);
v___x_1249_ = v___x_1226_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1245_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1250_; 
v___x_1250_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1210_, v_flb_1211_, v_tail_1206_, v_tail_1212_);
v_x_1197_ = v___x_1250_;
v___y_1198_ = v___x_1249_;
goto _start;
}
}
}
}
v___jp_1254_:
{
if (v___y_1255_ == 0)
{
goto v___jp_1222_;
}
else
{
lean_object* v___x_1256_; 
lean_dec(v_indent_1217_);
v___x_1256_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1210_, v_flb_1211_, v_tail_1206_, v_tail_1212_);
v_x_1197_ = v___x_1256_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0___boxed(lean_object* v_w_1478_, lean_object* v_x_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_1478_, v_x_1479_, v___y_1480_);
lean_dec(v_w_1478_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(lean_object* v_f_1482_, lean_object* v_w_1483_, lean_object* v_indent_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1486_; uint8_t v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1486_ = lean_box(1);
v___x_1487_ = 0;
v___x_1488_ = lean_nat_to_int(v_indent_1484_);
v___x_1489_ = lean_unsigned_to_nat(0u);
v___x_1490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1490_, 0, v_f_1482_);
lean_ctor_set(v___x_1490_, 1, v___x_1488_);
lean_ctor_set(v___x_1490_, 2, v___x_1489_);
v___x_1491_ = lean_box(0);
v___x_1492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1490_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
v___x_1493_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1493_, 0, v___x_1486_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*2, v___x_1487_);
v___x_1494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
lean_ctor_set(v___x_1494_, 1, v___x_1491_);
v___x_1495_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_1483_, v___x_1494_, v___y_1485_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0___boxed(lean_object* v_f_1496_, lean_object* v_w_1497_, lean_object* v_indent_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(v_f_1496_, v_w_1497_, v_indent_1498_, v___y_1499_);
lean_dec(v_w_1497_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty(lean_object* v_f_1501_, lean_object* v_width_1502_, lean_object* v_indent_1503_, lean_object* v_column_1504_){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v_snd_1508_; lean_object* v_out_1509_; 
v___x_1505_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
lean_ctor_set(v___x_1506_, 1, v_column_1504_);
v___x_1507_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(v_f_1501_, v_width_1502_, v_indent_1503_, v___x_1506_);
v_snd_1508_ = lean_ctor_get(v___x_1507_, 1);
lean_inc(v_snd_1508_);
lean_dec_ref(v___x_1507_);
v_out_1509_ = lean_ctor_get(v_snd_1508_, 0);
lean_inc_ref(v_out_1509_);
lean_dec(v_snd_1508_);
return v_out_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty___boxed(lean_object* v_f_1510_, lean_object* v_width_1511_, lean_object* v_indent_1512_, lean_object* v_column_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Std_Format_pretty(v_f_1510_, v_width_1511_, v_indent_1512_, v_column_1513_);
lean_dec(v_width_1511_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0(lean_object* v_f_1515_){
_start:
{
lean_inc(v_f_1515_);
return v_f_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object* v_f_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Std_instToFormatFormat___lam__0(v_f_1516_);
lean_dec(v_f_1516_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatString___lam__0(lean_object* v_s_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1521_, 0, v_s_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg___lam__0(lean_object* v_x_1524_, lean_object* v_inst_1525_, lean_object* v_x1_1526_, lean_object* v_x2_1527_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1528_, 0, v_x1_1526_);
lean_ctor_set(v___x_1528_, 1, v_x_1524_);
v___x_1529_ = lean_apply_1(v_inst_1525_, v_x2_1527_);
v___x_1530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg(lean_object* v_inst_1531_, lean_object* v_x_1532_, lean_object* v_x_1533_){
_start:
{
if (lean_obj_tag(v_x_1532_) == 0)
{
lean_object* v___x_1534_; 
lean_dec(v_x_1533_);
lean_dec_ref(v_inst_1531_);
v___x_1534_ = lean_box(0);
return v___x_1534_;
}
else
{
lean_object* v_tail_1535_; 
v_tail_1535_ = lean_ctor_get(v_x_1532_, 1);
if (lean_obj_tag(v_tail_1535_) == 0)
{
lean_object* v_head_1536_; lean_object* v___x_1537_; 
lean_dec(v_x_1533_);
v_head_1536_ = lean_ctor_get(v_x_1532_, 0);
lean_inc(v_head_1536_);
lean_dec_ref_known(v_x_1532_, 2);
v___x_1537_ = lean_apply_1(v_inst_1531_, v_head_1536_);
return v___x_1537_;
}
else
{
lean_object* v_head_1538_; lean_object* v___f_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_inc(v_tail_1535_);
v_head_1538_ = lean_ctor_get(v_x_1532_, 0);
lean_inc(v_head_1538_);
lean_dec_ref_known(v_x_1532_, 2);
lean_inc_ref(v_inst_1531_);
v___f_1539_ = lean_alloc_closure((void*)(l_Std_Format_joinSep___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1539_, 0, v_x_1533_);
lean_closure_set(v___f_1539_, 1, v_inst_1531_);
v___x_1540_ = lean_apply_1(v_inst_1531_, v_head_1538_);
v___x_1541_ = l_List_foldl___redArg(v___f_1539_, v___x_1540_, v_tail_1535_);
return v___x_1541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep(lean_object* v_00_u03b1_1542_, lean_object* v_inst_1543_, lean_object* v_x_1544_, lean_object* v_x_1545_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Std_Format_joinSep___redArg(v_inst_1543_, v_x_1544_, v_x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg___lam__0(lean_object* v_pre_1547_, lean_object* v_inst_1548_, lean_object* v_x1_1549_, lean_object* v_x2_1550_){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1551_, 0, v_x1_1549_);
lean_ctor_set(v___x_1551_, 1, v_pre_1547_);
v___x_1552_ = lean_apply_1(v_inst_1548_, v_x2_1550_);
v___x_1553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg(lean_object* v_inst_1554_, lean_object* v_pre_1555_, lean_object* v_x_1556_){
_start:
{
if (lean_obj_tag(v_x_1556_) == 0)
{
lean_object* v___x_1557_; 
lean_dec(v_pre_1555_);
lean_dec_ref(v_inst_1554_);
v___x_1557_ = lean_box(0);
return v___x_1557_;
}
else
{
lean_object* v_head_1558_; lean_object* v_tail_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1569_; 
v_head_1558_ = lean_ctor_get(v_x_1556_, 0);
v_tail_1559_ = lean_ctor_get(v_x_1556_, 1);
v_isSharedCheck_1569_ = !lean_is_exclusive(v_x_1556_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1561_ = v_x_1556_;
v_isShared_1562_ = v_isSharedCheck_1569_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_tail_1559_);
lean_inc(v_head_1558_);
lean_dec(v_x_1556_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1569_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___f_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
lean_inc_ref(v_inst_1554_);
lean_inc(v_pre_1555_);
v___f_1563_ = lean_alloc_closure((void*)(l_Std_Format_prefixJoin___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1563_, 0, v_pre_1555_);
lean_closure_set(v___f_1563_, 1, v_inst_1554_);
v___x_1564_ = lean_apply_1(v_inst_1554_, v_head_1558_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set_tag(v___x_1561_, 5);
lean_ctor_set(v___x_1561_, 1, v___x_1564_);
lean_ctor_set(v___x_1561_, 0, v_pre_1555_);
v___x_1566_ = v___x_1561_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_pre_1555_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_List_foldl___redArg(v___f_1563_, v___x_1566_, v_tail_1559_);
return v___x_1567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin(lean_object* v_00_u03b1_1570_, lean_object* v_inst_1571_, lean_object* v_pre_1572_, lean_object* v_x_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Std_Format_prefixJoin___redArg(v_inst_1571_, v_pre_1572_, v_x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg___lam__0(lean_object* v_inst_1575_, lean_object* v_x_1576_, lean_object* v_x1_1577_, lean_object* v_x2_1578_){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1579_ = lean_apply_1(v_inst_1575_, v_x2_1578_);
v___x_1580_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1580_, 0, v_x1_1577_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
lean_ctor_set(v___x_1581_, 1, v_x_1576_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg(lean_object* v_inst_1582_, lean_object* v_x_1583_, lean_object* v_x_1584_){
_start:
{
if (lean_obj_tag(v_x_1583_) == 0)
{
lean_object* v___x_1585_; 
lean_dec(v_x_1584_);
lean_dec_ref(v_inst_1582_);
v___x_1585_ = lean_box(0);
return v___x_1585_;
}
else
{
lean_object* v_head_1586_; lean_object* v_tail_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1597_; 
v_head_1586_ = lean_ctor_get(v_x_1583_, 0);
v_tail_1587_ = lean_ctor_get(v_x_1583_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_x_1583_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1589_ = v_x_1583_;
v_isShared_1590_ = v_isSharedCheck_1597_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_tail_1587_);
lean_inc(v_head_1586_);
lean_dec(v_x_1583_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1597_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___f_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
lean_inc(v_x_1584_);
lean_inc_ref(v_inst_1582_);
v___f_1591_ = lean_alloc_closure((void*)(l_Std_Format_joinSuffix___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1591_, 0, v_inst_1582_);
lean_closure_set(v___f_1591_, 1, v_x_1584_);
v___x_1592_ = lean_apply_1(v_inst_1582_, v_head_1586_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set_tag(v___x_1589_, 5);
lean_ctor_set(v___x_1589_, 1, v_x_1584_);
lean_ctor_set(v___x_1589_, 0, v___x_1592_);
v___x_1594_ = v___x_1589_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_x_1584_);
v___x_1594_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_List_foldl___redArg(v___f_1591_, v___x_1594_, v_tail_1587_);
return v___x_1595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix(lean_object* v_00_u03b1_1598_, lean_object* v_inst_1599_, lean_object* v_x_1600_, lean_object* v_x_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Std_Format_joinSuffix___redArg(v_inst_1599_, v_x_1600_, v_x_1601_);
return v___x_1602_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_State(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Format_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
