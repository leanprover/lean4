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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v_x_21__boxed_57_; uint8_t v_y_22__boxed_58_; uint8_t v_res_59_; lean_object* v_r_60_; 
v_x_21__boxed_57_ = lean_unbox(v_x_55_);
v_y_22__boxed_58_ = lean_unbox(v_y_56_);
v_res_59_ = l_Std_Format_instBEqFlattenBehavior_beq(v_x_21__boxed_57_, v_y_22__boxed_58_);
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
uint8_t v_foundLine_235_; lean_object* v_space_236_; uint8_t v___x_237_; 
v_foundLine_235_ = lean_ctor_get_uint8(v_r_u2081_233_, sizeof(void*)*1);
v_space_236_ = lean_ctor_get(v_r_u2081_233_, 0);
v___x_237_ = lean_nat_dec_lt(v_w_232_, v_space_236_);
if (v___x_237_ == 0)
{
if (v_foundLine_235_ == 0)
{
lean_object* v___x_238_; lean_object* v_r_u2082_239_; uint8_t v_foundLine_240_; uint8_t v_foundFlattenedHardLine_241_; lean_object* v_space_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_250_; 
v___x_238_ = lean_nat_sub(v_w_232_, v_space_236_);
v_r_u2082_239_ = lean_apply_1(v_r_u2082_234_, v___x_238_);
v_foundLine_240_ = lean_ctor_get_uint8(v_r_u2082_239_, sizeof(void*)*1);
v_foundFlattenedHardLine_241_ = lean_ctor_get_uint8(v_r_u2082_239_, sizeof(void*)*1 + 1);
v_space_242_ = lean_ctor_get(v_r_u2082_239_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v_r_u2082_239_);
if (v_isSharedCheck_250_ == 0)
{
v___x_244_ = v_r_u2082_239_;
v_isShared_245_ = v_isSharedCheck_250_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_space_242_);
lean_dec(v_r_u2082_239_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_250_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_246_ = lean_nat_add(v_space_236_, v_space_242_);
lean_dec(v_space_242_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_246_);
v___x_248_ = v___x_244_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
lean_ctor_set_uint8(v_reuseFailAlloc_249_, sizeof(void*)*1, v_foundLine_240_);
lean_ctor_set_uint8(v_reuseFailAlloc_249_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_241_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
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
else
{
lean_dec_ref(v_r_u2082_234_);
lean_inc_ref(v_r_u2081_233_);
return v_r_u2081_233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_merge___boxed(lean_object* v_w_251_, lean_object* v_r_u2081_252_, lean_object* v_r_u2082_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l___private_Init_Data_Format_Basic_0__Std_Format_merge(v_w_251_, v_r_u2081_252_, v_r_u2082_253_);
lean_dec_ref(v_r_u2081_252_);
lean_dec(v_w_251_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_spec__0(lean_object* v_a_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lean_nat_to_int(v_a_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(lean_object* v_x_260_, uint8_t v_x_261_, lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
uint8_t v___y_265_; 
switch(lean_obj_tag(v_x_260_))
{
case 0:
{
lean_object* v___x_274_; 
lean_dec(v_x_263_);
lean_dec(v_x_262_);
v___x_274_ = ((lean_object*)(l_Std_Format_instInhabitedSpaceResult_default___closed__0));
return v___x_274_;
}
case 1:
{
lean_dec(v_x_263_);
lean_dec(v_x_262_);
if (v_x_261_ == 0)
{
uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = 1;
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*1, v___x_275_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*1 + 1, v_x_261_);
return v___x_277_;
}
else
{
lean_object* v___x_278_; 
v___x_278_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0));
return v___x_278_;
}
}
case 2:
{
if (v_x_261_ == 0)
{
lean_dec_ref_known(v_x_260_, 0);
v___y_265_ = v_x_261_;
goto v___jp_264_;
}
else
{
uint8_t v_force_279_; 
v_force_279_ = lean_ctor_get_uint8(v_x_260_, 0);
lean_dec_ref_known(v_x_260_, 0);
if (v_force_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec(v_x_263_);
lean_dec(v_x_262_);
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*1, v_force_279_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*1 + 1, v_force_279_);
return v___x_281_;
}
else
{
uint8_t v___x_282_; 
v___x_282_ = 0;
v___y_265_ = v___x_282_;
goto v___jp_264_;
}
}
}
case 3:
{
lean_object* v_a_283_; uint32_t v___x_284_; lean_object* v_p_285_; lean_object* v_off_286_; uint8_t v___y_288_; lean_object* v___x_291_; uint8_t v_decide_292_; 
lean_dec(v_x_263_);
lean_dec(v_x_262_);
v_a_283_ = lean_ctor_get(v_x_260_, 0);
lean_inc_ref_n(v_a_283_, 3);
lean_dec_ref_known(v_x_260_, 1);
v___x_284_ = 10;
v_p_285_ = lean_string_posof(v_a_283_, v___x_284_);
lean_inc(v_p_285_);
v_off_286_ = lean_string_offsetofpos(v_a_283_, v_p_285_);
v___x_291_ = lean_string_utf8_byte_size(v_a_283_);
lean_dec_ref(v_a_283_);
v_decide_292_ = lean_nat_dec_eq(v_p_285_, v___x_291_);
lean_dec(v_p_285_);
if (v_decide_292_ == 0)
{
uint8_t v___x_293_; 
v___x_293_ = 1;
v___y_288_ = v___x_293_;
goto v___jp_287_;
}
else
{
uint8_t v___x_294_; 
v___x_294_ = 0;
v___y_288_ = v___x_294_;
goto v___jp_287_;
}
v___jp_287_:
{
if (v_x_261_ == 0)
{
lean_object* v___x_289_; 
v___x_289_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_289_, 0, v_off_286_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*1, v___y_288_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*1 + 1, v_x_261_);
return v___x_289_;
}
else
{
lean_object* v___x_290_; 
v___x_290_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_290_, 0, v_off_286_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*1, v___y_288_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*1 + 1, v___y_288_);
return v___x_290_;
}
}
}
case 4:
{
lean_object* v_indent_295_; lean_object* v_f_296_; lean_object* v___x_297_; 
v_indent_295_ = lean_ctor_get(v_x_260_, 0);
lean_inc(v_indent_295_);
v_f_296_ = lean_ctor_get(v_x_260_, 1);
lean_inc(v_f_296_);
lean_dec_ref_known(v_x_260_, 2);
v___x_297_ = lean_int_sub(v_x_262_, v_indent_295_);
lean_dec(v_indent_295_);
lean_dec(v_x_262_);
v_x_260_ = v_f_296_;
v_x_262_ = v___x_297_;
goto _start;
}
case 5:
{
lean_object* v_a_299_; lean_object* v_a_300_; lean_object* v___x_301_; uint8_t v_foundLine_302_; lean_object* v_space_303_; uint8_t v___x_304_; 
v_a_299_ = lean_ctor_get(v_x_260_, 0);
lean_inc(v_a_299_);
v_a_300_ = lean_ctor_get(v_x_260_, 1);
lean_inc(v_a_300_);
lean_dec_ref_known(v_x_260_, 2);
lean_inc(v_x_263_);
lean_inc(v_x_262_);
v___x_301_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_a_299_, v_x_261_, v_x_262_, v_x_263_);
v_foundLine_302_ = lean_ctor_get_uint8(v___x_301_, sizeof(void*)*1);
v_space_303_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_space_303_);
v___x_304_ = lean_nat_dec_lt(v_x_263_, v_space_303_);
if (v___x_304_ == 0)
{
if (v_foundLine_302_ == 0)
{
lean_object* v___x_305_; lean_object* v_r_u2082_306_; uint8_t v_foundLine_307_; uint8_t v_foundFlattenedHardLine_308_; lean_object* v_space_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_317_; 
lean_dec_ref(v___x_301_);
v___x_305_ = lean_nat_sub(v_x_263_, v_space_303_);
lean_dec(v_x_263_);
v_r_u2082_306_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_a_300_, v_x_261_, v_x_262_, v___x_305_);
v_foundLine_307_ = lean_ctor_get_uint8(v_r_u2082_306_, sizeof(void*)*1);
v_foundFlattenedHardLine_308_ = lean_ctor_get_uint8(v_r_u2082_306_, sizeof(void*)*1 + 1);
v_space_309_ = lean_ctor_get(v_r_u2082_306_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v_r_u2082_306_);
if (v_isSharedCheck_317_ == 0)
{
v___x_311_ = v_r_u2082_306_;
v_isShared_312_ = v_isSharedCheck_317_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_space_309_);
lean_dec(v_r_u2082_306_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_317_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_313_ = lean_nat_add(v_space_303_, v_space_309_);
lean_dec(v_space_309_);
lean_dec(v_space_303_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_313_);
v___x_315_ = v___x_311_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
lean_ctor_set_uint8(v_reuseFailAlloc_316_, sizeof(void*)*1, v_foundLine_307_);
lean_ctor_set_uint8(v_reuseFailAlloc_316_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_308_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
else
{
lean_dec(v_space_303_);
lean_dec(v_a_300_);
lean_dec(v_x_263_);
lean_dec(v_x_262_);
return v___x_301_;
}
}
else
{
lean_dec(v_space_303_);
lean_dec(v_a_300_);
lean_dec(v_x_263_);
lean_dec(v_x_262_);
return v___x_301_;
}
}
case 6:
{
lean_object* v_a_318_; uint8_t v___x_319_; 
v_a_318_ = lean_ctor_get(v_x_260_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v_x_260_, 1);
v___x_319_ = 1;
v_x_260_ = v_a_318_;
v_x_261_ = v___x_319_;
goto _start;
}
default: 
{
lean_object* v_a_321_; 
v_a_321_ = lean_ctor_get(v_x_260_, 1);
lean_inc(v_a_321_);
lean_dec_ref_known(v_x_260_, 2);
v_x_260_ = v_a_321_;
goto _start;
}
}
v___jp_264_:
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_nat_to_int(v_x_263_);
v___x_267_ = lean_int_dec_lt(v___x_266_, v_x_262_);
if (v___x_267_ == 0)
{
uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec(v___x_266_);
lean_dec(v_x_262_);
v___x_268_ = 1;
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*1, v___x_268_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*1 + 1, v___x_267_);
return v___x_270_;
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_int_sub(v_x_262_, v___x_266_);
lean_dec(v___x_266_);
lean_dec(v_x_262_);
v___x_272_ = l_Int_toNat(v___x_271_);
lean_dec(v___x_271_);
v___x_273_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*1, v___y_265_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*1 + 1, v___y_265_);
return v___x_273_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___boxed(lean_object* v_x_323_, lean_object* v_x_324_, lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
uint8_t v_x_398__boxed_327_; lean_object* v_res_328_; 
v_x_398__boxed_327_ = lean_unbox(v_x_324_);
v_res_328_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_x_323_, v_x_398__boxed_327_, v_x_325_, v_x_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx(lean_object* v_x_329_){
_start:
{
if (lean_obj_tag(v_x_329_) == 0)
{
lean_object* v___x_330_; 
v___x_330_ = lean_unsigned_to_nat(0u);
return v___x_330_;
}
else
{
lean_object* v___x_331_; 
v___x_331_ = lean_unsigned_to_nat(1u);
return v___x_331_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx___boxed(lean_object* v_x_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Std_Format_FlattenAllowability_ctorIdx(v_x_332_);
lean_dec(v_x_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___redArg(lean_object* v_t_334_, lean_object* v_k_335_){
_start:
{
if (lean_obj_tag(v_t_334_) == 0)
{
uint8_t v_fits_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_fits_336_ = lean_ctor_get_uint8(v_t_334_, 0);
v___x_337_ = lean_box(v_fits_336_);
v___x_338_ = lean_apply_1(v_k_335_, v___x_337_);
return v___x_338_;
}
else
{
return v_k_335_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___redArg___boxed(lean_object* v_t_339_, lean_object* v_k_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_339_, v_k_340_);
lean_dec(v_t_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim(lean_object* v_motive_342_, lean_object* v_ctorIdx_343_, lean_object* v_t_344_, lean_object* v_h_345_, lean_object* v_k_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_344_, v_k_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___boxed(lean_object* v_motive_348_, lean_object* v_ctorIdx_349_, lean_object* v_t_350_, lean_object* v_h_351_, lean_object* v_k_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_Format_FlattenAllowability_ctorElim(v_motive_348_, v_ctorIdx_349_, v_t_350_, v_h_351_, v_k_352_);
lean_dec(v_t_350_);
lean_dec(v_ctorIdx_349_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___redArg(lean_object* v_t_354_, lean_object* v_allow_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_354_, v_allow_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___redArg___boxed(lean_object* v_t_357_, lean_object* v_allow_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Std_Format_FlattenAllowability_allow_elim___redArg(v_t_357_, v_allow_358_);
lean_dec(v_t_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim(lean_object* v_motive_360_, lean_object* v_t_361_, lean_object* v_h_362_, lean_object* v_allow_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_361_, v_allow_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___boxed(lean_object* v_motive_365_, lean_object* v_t_366_, lean_object* v_h_367_, lean_object* v_allow_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Std_Format_FlattenAllowability_allow_elim(v_motive_365_, v_t_366_, v_h_367_, v_allow_368_);
lean_dec(v_t_366_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___redArg(lean_object* v_t_370_, lean_object* v_disallow_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_370_, v_disallow_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___redArg___boxed(lean_object* v_t_373_, lean_object* v_disallow_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Std_Format_FlattenAllowability_disallow_elim___redArg(v_t_373_, v_disallow_374_);
lean_dec(v_t_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim(lean_object* v_motive_376_, lean_object* v_t_377_, lean_object* v_h_378_, lean_object* v_disallow_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_377_, v_disallow_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___boxed(lean_object* v_motive_381_, lean_object* v_t_382_, lean_object* v_h_383_, lean_object* v_disallow_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Std_Format_FlattenAllowability_disallow_elim(v_motive_381_, v_t_382_, v_h_383_, v_disallow_384_);
lean_dec(v_t_382_);
return v_res_385_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_instBEqFlattenAllowability_beq(lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
if (lean_obj_tag(v_x_386_) == 0)
{
if (lean_obj_tag(v_x_387_) == 0)
{
uint8_t v_fits_388_; 
v_fits_388_ = lean_ctor_get_uint8(v_x_387_, 0);
if (v_fits_388_ == 0)
{
uint8_t v_fits_389_; 
v_fits_389_ = lean_ctor_get_uint8(v_x_386_, 0);
if (v_fits_389_ == 0)
{
uint8_t v___x_390_; 
v___x_390_ = 1;
return v___x_390_;
}
else
{
return v_fits_388_;
}
}
else
{
uint8_t v_fits_391_; 
v_fits_391_ = lean_ctor_get_uint8(v_x_386_, 0);
return v_fits_391_;
}
}
else
{
uint8_t v___x_392_; 
v___x_392_ = 0;
return v___x_392_;
}
}
else
{
if (lean_obj_tag(v_x_387_) == 1)
{
uint8_t v___x_393_; 
v___x_393_ = 1;
return v___x_393_;
}
else
{
uint8_t v___x_394_; 
v___x_394_ = 0;
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_instBEqFlattenAllowability_beq___boxed(lean_object* v_x_395_, lean_object* v_x_396_){
_start:
{
uint8_t v_res_397_; lean_object* v_r_398_; 
v_res_397_ = l_Std_Format_instBEqFlattenAllowability_beq(v_x_395_, v_x_396_);
lean_dec(v_x_396_);
lean_dec(v_x_395_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_FlattenAllowability_shouldFlatten(lean_object* v_x_401_){
_start:
{
if (lean_obj_tag(v_x_401_) == 0)
{
uint8_t v_fits_402_; 
v_fits_402_ = lean_ctor_get_uint8(v_x_401_, 0);
if (v_fits_402_ == 1)
{
return v_fits_402_;
}
else
{
uint8_t v___x_403_; 
v___x_403_ = 0;
return v___x_403_;
}
}
else
{
uint8_t v___x_404_; 
v___x_404_ = 0;
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_shouldFlatten___boxed(lean_object* v_x_405_){
_start:
{
uint8_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_x_405_);
lean_dec(v_x_405_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(lean_object* v_x_408_, lean_object* v_x_409_, lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_408_) == 0)
{
lean_object* v___x_411_; 
lean_dec(v_x_410_);
lean_dec(v_x_409_);
v___x_411_ = ((lean_object*)(l_Std_Format_instInhabitedSpaceResult_default___closed__0));
return v___x_411_;
}
else
{
lean_object* v_head_412_; lean_object* v_items_413_; 
v_head_412_ = lean_ctor_get(v_x_408_, 0);
lean_inc(v_head_412_);
v_items_413_ = lean_ctor_get(v_head_412_, 1);
lean_inc(v_items_413_);
if (lean_obj_tag(v_items_413_) == 0)
{
lean_object* v_tail_414_; 
lean_dec(v_head_412_);
v_tail_414_ = lean_ctor_get(v_x_408_, 1);
lean_inc(v_tail_414_);
lean_dec_ref_known(v_x_408_, 2);
v_x_408_ = v_tail_414_;
goto _start;
}
else
{
lean_object* v_head_416_; lean_object* v_tail_417_; lean_object* v_fla_418_; uint8_t v_flb_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_459_; 
v_head_416_ = lean_ctor_get(v_items_413_, 0);
lean_inc(v_head_416_);
v_tail_417_ = lean_ctor_get(v_x_408_, 1);
lean_inc(v_tail_417_);
lean_dec_ref_known(v_x_408_, 2);
v_fla_418_ = lean_ctor_get(v_head_412_, 0);
v_flb_419_ = lean_ctor_get_uint8(v_head_412_, sizeof(void*)*2);
v_isSharedCheck_459_ = !lean_is_exclusive(v_head_412_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; 
v_unused_460_ = lean_ctor_get(v_head_412_, 1);
lean_dec(v_unused_460_);
v___x_421_ = v_head_412_;
v_isShared_422_ = v_isSharedCheck_459_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_fla_418_);
lean_dec(v_head_412_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_459_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v_tail_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_457_; 
v_tail_423_ = lean_ctor_get(v_items_413_, 1);
v_isSharedCheck_457_ = !lean_is_exclusive(v_items_413_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; 
v_unused_458_ = lean_ctor_get(v_items_413_, 0);
lean_dec(v_unused_458_);
v___x_425_ = v_items_413_;
v_isShared_426_ = v_isSharedCheck_457_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_tail_423_);
lean_dec(v_items_413_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_457_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v_f_427_; lean_object* v_indent_428_; uint8_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v_foundLine_435_; lean_object* v_space_436_; uint8_t v___x_437_; 
v_f_427_ = lean_ctor_get(v_head_416_, 0);
lean_inc(v_f_427_);
v_indent_428_ = lean_ctor_get(v_head_416_, 1);
lean_inc(v_indent_428_);
lean_dec(v_head_416_);
v___x_429_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_418_);
lean_inc_n(v_x_410_, 2);
v___x_430_ = lean_nat_to_int(v_x_410_);
lean_inc(v_x_409_);
v___x_431_ = lean_nat_to_int(v_x_409_);
v___x_432_ = lean_int_add(v___x_430_, v___x_431_);
lean_dec(v___x_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_int_sub(v___x_432_, v_indent_428_);
lean_dec(v_indent_428_);
lean_dec(v___x_432_);
v___x_434_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_f_427_, v___x_429_, v___x_433_, v_x_410_);
v_foundLine_435_ = lean_ctor_get_uint8(v___x_434_, sizeof(void*)*1);
v_space_436_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_space_436_);
v___x_437_ = lean_nat_dec_lt(v_x_410_, v_space_436_);
if (v___x_437_ == 0)
{
if (v_foundLine_435_ == 0)
{
lean_object* v___x_439_; 
lean_dec_ref(v___x_434_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 1, v_tail_423_);
v___x_439_ = v___x_421_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_fla_418_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_tail_423_);
lean_ctor_set_uint8(v_reuseFailAlloc_456_, sizeof(void*)*2, v_flb_419_);
v___x_439_ = v_reuseFailAlloc_456_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_441_; 
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 1, v_tail_417_);
lean_ctor_set(v___x_425_, 0, v___x_439_);
v___x_441_ = v___x_425_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_tail_417_);
v___x_441_ = v_reuseFailAlloc_455_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_442_; lean_object* v_r_u2082_443_; uint8_t v_foundLine_444_; uint8_t v_foundFlattenedHardLine_445_; lean_object* v_space_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_454_; 
v___x_442_ = lean_nat_sub(v_x_410_, v_space_436_);
lean_dec(v_x_410_);
v_r_u2082_443_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_441_, v_x_409_, v___x_442_);
v_foundLine_444_ = lean_ctor_get_uint8(v_r_u2082_443_, sizeof(void*)*1);
v_foundFlattenedHardLine_445_ = lean_ctor_get_uint8(v_r_u2082_443_, sizeof(void*)*1 + 1);
v_space_446_ = lean_ctor_get(v_r_u2082_443_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v_r_u2082_443_);
if (v_isSharedCheck_454_ == 0)
{
v___x_448_ = v_r_u2082_443_;
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_space_446_);
lean_dec(v_r_u2082_443_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_450_ = lean_nat_add(v_space_436_, v_space_446_);
lean_dec(v_space_446_);
lean_dec(v_space_436_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_450_);
v___x_452_ = v___x_448_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
lean_ctor_set_uint8(v_reuseFailAlloc_453_, sizeof(void*)*1, v_foundLine_444_);
lean_ctor_set_uint8(v_reuseFailAlloc_453_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_445_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
else
{
lean_dec(v_space_436_);
lean_del_object(v___x_425_);
lean_dec(v_tail_423_);
lean_del_object(v___x_421_);
lean_dec(v_fla_418_);
lean_dec(v_tail_417_);
lean_dec(v_x_410_);
lean_dec(v_x_409_);
return v___x_434_;
}
}
else
{
lean_dec(v_space_436_);
lean_del_object(v___x_425_);
lean_dec(v_tail_423_);
lean_del_object(v___x_421_);
lean_dec(v_fla_418_);
lean_dec(v_tail_417_);
lean_dec(v_x_410_);
lean_dec(v_x_409_);
return v___x_434_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(uint8_t v_flb_461_, lean_object* v_items_462_, lean_object* v_w_463_, lean_object* v_gs_464_, lean_object* v_toPure_465_, lean_object* v_k_466_){
_start:
{
uint8_t v___y_468_; uint8_t v___x_473_; uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v_g_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v_r_480_; lean_object* v___y_482_; uint8_t v_foundLine_487_; lean_object* v_space_488_; uint8_t v___x_489_; 
v___x_473_ = 0;
v___x_474_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_461_, v___x_473_);
v___x_475_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_475_, 0, v___x_474_);
lean_inc(v_items_462_);
v_g_476_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_476_, 0, v___x_475_);
lean_ctor_set(v_g_476_, 1, v_items_462_);
lean_ctor_set_uint8(v_g_476_, sizeof(void*)*2, v_flb_461_);
v___x_477_ = lean_box(0);
v___x_478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_478_, 0, v_g_476_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = lean_nat_sub(v_w_463_, v_k_466_);
lean_inc(v___x_479_);
lean_inc(v_k_466_);
v_r_480_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_478_, v_k_466_, v___x_479_);
v_foundLine_487_ = lean_ctor_get_uint8(v_r_480_, sizeof(void*)*1);
v_space_488_ = lean_ctor_get(v_r_480_, 0);
lean_inc(v_space_488_);
v___x_489_ = lean_nat_dec_lt(v___x_479_, v_space_488_);
if (v___x_489_ == 0)
{
if (v_foundLine_487_ == 0)
{
lean_object* v___x_490_; lean_object* v_r_u2082_491_; uint8_t v_foundLine_492_; uint8_t v_foundFlattenedHardLine_493_; lean_object* v_space_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_502_; 
v___x_490_ = lean_nat_sub(v___x_479_, v_space_488_);
lean_inc(v_gs_464_);
v_r_u2082_491_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_464_, v_k_466_, v___x_490_);
v_foundLine_492_ = lean_ctor_get_uint8(v_r_u2082_491_, sizeof(void*)*1);
v_foundFlattenedHardLine_493_ = lean_ctor_get_uint8(v_r_u2082_491_, sizeof(void*)*1 + 1);
v_space_494_ = lean_ctor_get(v_r_u2082_491_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v_r_u2082_491_);
if (v_isSharedCheck_502_ == 0)
{
v___x_496_ = v_r_u2082_491_;
v_isShared_497_ = v_isSharedCheck_502_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_space_494_);
lean_dec(v_r_u2082_491_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_502_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_498_ = lean_nat_add(v_space_488_, v_space_494_);
lean_dec(v_space_494_);
lean_dec(v_space_488_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_498_);
v___x_500_ = v___x_496_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
lean_ctor_set_uint8(v_reuseFailAlloc_501_, sizeof(void*)*1, v_foundLine_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_501_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_493_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
v___y_482_ = v___x_500_;
goto v___jp_481_;
}
}
}
else
{
lean_dec(v_space_488_);
lean_dec(v_k_466_);
lean_inc_ref(v_r_480_);
v___y_482_ = v_r_480_;
goto v___jp_481_;
}
}
else
{
lean_dec(v_space_488_);
lean_dec(v_k_466_);
lean_inc_ref(v_r_480_);
v___y_482_ = v_r_480_;
goto v___jp_481_;
}
v___jp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_469_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_469_, 0, v___y_468_);
v___x_470_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v_items_462_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*2, v_flb_461_);
v___x_471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v_gs_464_);
v___x_472_ = lean_apply_2(v_toPure_465_, lean_box(0), v___x_471_);
return v___x_472_;
}
v___jp_481_:
{
uint8_t v_foundFlattenedHardLine_483_; 
v_foundFlattenedHardLine_483_ = lean_ctor_get_uint8(v_r_480_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_480_);
if (v_foundFlattenedHardLine_483_ == 0)
{
lean_object* v_space_484_; uint8_t v___x_485_; 
v_space_484_ = lean_ctor_get(v___y_482_, 0);
lean_inc(v_space_484_);
lean_dec_ref(v___y_482_);
v___x_485_ = lean_nat_dec_le(v_space_484_, v___x_479_);
lean_dec(v___x_479_);
lean_dec(v_space_484_);
v___y_468_ = v___x_485_;
goto v___jp_467_;
}
else
{
uint8_t v___x_486_; 
lean_dec_ref(v___y_482_);
lean_dec(v___x_479_);
v___x_486_ = 0;
v___y_468_ = v___x_486_;
goto v___jp_467_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed(lean_object* v_flb_503_, lean_object* v_items_504_, lean_object* v_w_505_, lean_object* v_gs_506_, lean_object* v_toPure_507_, lean_object* v_k_508_){
_start:
{
uint8_t v_flb_boxed_509_; lean_object* v_res_510_; 
v_flb_boxed_509_ = lean_unbox(v_flb_503_);
v_res_510_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(v_flb_boxed_509_, v_items_504_, v_w_505_, v_gs_506_, v_toPure_507_, v_k_508_);
lean_dec(v_w_505_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(uint8_t v_flb_511_, lean_object* v_items_512_, lean_object* v_gs_513_, lean_object* v_w_514_, lean_object* v_inst_515_, lean_object* v_inst_516_){
_start:
{
lean_object* v_toApplicative_517_; lean_object* v_toBind_518_; lean_object* v_currColumn_519_; lean_object* v_toPure_520_; lean_object* v___x_521_; lean_object* v___f_522_; lean_object* v___x_523_; 
v_toApplicative_517_ = lean_ctor_get(v_inst_515_, 0);
lean_inc_ref(v_toApplicative_517_);
v_toBind_518_ = lean_ctor_get(v_inst_515_, 1);
lean_inc(v_toBind_518_);
lean_dec_ref(v_inst_515_);
v_currColumn_519_ = lean_ctor_get(v_inst_516_, 2);
lean_inc(v_currColumn_519_);
lean_dec_ref(v_inst_516_);
v_toPure_520_ = lean_ctor_get(v_toApplicative_517_, 1);
lean_inc(v_toPure_520_);
lean_dec_ref(v_toApplicative_517_);
v___x_521_ = lean_box(v_flb_511_);
v___f_522_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_522_, 0, v___x_521_);
lean_closure_set(v___f_522_, 1, v_items_512_);
lean_closure_set(v___f_522_, 2, v_w_514_);
lean_closure_set(v___f_522_, 3, v_gs_513_);
lean_closure_set(v___f_522_, 4, v_toPure_520_);
v___x_523_ = lean_apply_4(v_toBind_518_, lean_box(0), lean_box(0), v_currColumn_519_, v___f_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___boxed(lean_object* v_flb_524_, lean_object* v_items_525_, lean_object* v_gs_526_, lean_object* v_w_527_, lean_object* v_inst_528_, lean_object* v_inst_529_){
_start:
{
uint8_t v_flb_boxed_530_; lean_object* v_res_531_; 
v_flb_boxed_530_ = lean_unbox(v_flb_524_);
v_res_531_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_boxed_530_, v_items_525_, v_gs_526_, v_w_527_, v_inst_528_, v_inst_529_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(lean_object* v_m_532_, uint8_t v_flb_533_, lean_object* v_items_534_, lean_object* v_gs_535_, lean_object* v_w_536_, lean_object* v_inst_537_, lean_object* v_inst_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_533_, v_items_534_, v_gs_535_, v_w_536_, v_inst_537_, v_inst_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___boxed(lean_object* v_m_540_, lean_object* v_flb_541_, lean_object* v_items_542_, lean_object* v_gs_543_, lean_object* v_w_544_, lean_object* v_inst_545_, lean_object* v_inst_546_){
_start:
{
uint8_t v_flb_boxed_547_; lean_object* v_res_548_; 
v_flb_boxed_547_ = lean_unbox(v_flb_541_);
v_res_548_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(v_m_540_, v_flb_boxed_547_, v_items_542_, v_gs_543_, v_w_544_, v_inst_545_, v_inst_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(lean_object* v_fla_549_, uint8_t v_flb_550_, lean_object* v_tail_551_, lean_object* v_is_x27_552_){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_553_, 0, v_fla_549_);
lean_ctor_set(v___x_553_, 1, v_is_x27_552_);
lean_ctor_set_uint8(v___x_553_, sizeof(void*)*2, v_flb_550_);
v___x_554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v_tail_551_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed(lean_object* v_fla_555_, lean_object* v_flb_556_, lean_object* v_tail_557_, lean_object* v_is_x27_558_){
_start:
{
uint8_t v_flb_1429__boxed_559_; lean_object* v_res_560_; 
v_flb_1429__boxed_559_ = lean_unbox(v_flb_556_);
v_res_560_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_555_, v_flb_1429__boxed_559_, v_tail_557_, v_is_x27_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3(lean_object* v_endTags_561_, lean_object* v_activeTags_562_, lean_object* v_toBind_563_, lean_object* v___f_564_, lean_object* v_____r_565_){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_apply_1(v_endTags_561_, v_activeTags_562_);
v___x_567_ = lean_apply_4(v_toBind_563_, lean_box(0), lean_box(0), v___x_566_, v___f_564_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(lean_object* v_indent_568_, lean_object* v_pushNewline_569_, lean_object* v_toBind_570_, lean_object* v___f_571_, lean_object* v_____r_572_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = l_Int_toNat(v_indent_568_);
v___x_574_ = lean_apply_1(v_pushNewline_569_, v___x_573_);
v___x_575_ = lean_apply_4(v_toBind_570_, lean_box(0), lean_box(0), v___x_574_, v___f_571_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed(lean_object* v_indent_576_, lean_object* v_pushNewline_577_, lean_object* v_toBind_578_, lean_object* v___f_579_, lean_object* v_____r_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(v_indent_576_, v_pushNewline_577_, v_toBind_578_, v___f_579_, v_____r_580_);
lean_dec(v_indent_576_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(lean_object* v_indent_582_, lean_object* v_inst_583_, lean_object* v_toBind_584_, lean_object* v___f_585_, lean_object* v___f_586_, lean_object* v_k_587_){
_start:
{
lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_588_ = lean_nat_to_int(v_k_587_);
v___x_589_ = lean_int_dec_lt(v___x_588_, v_indent_582_);
if (v___x_589_ == 0)
{
lean_object* v_pushNewline_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
lean_dec(v___x_588_);
lean_dec(v___f_586_);
v_pushNewline_590_ = lean_ctor_get(v_inst_583_, 1);
lean_inc(v_pushNewline_590_);
lean_dec_ref(v_inst_583_);
v___x_591_ = l_Int_toNat(v_indent_582_);
v___x_592_ = lean_apply_1(v_pushNewline_590_, v___x_591_);
v___x_593_ = lean_apply_4(v_toBind_584_, lean_box(0), lean_box(0), v___x_592_, v___f_585_);
return v___x_593_;
}
else
{
lean_object* v_pushOutput_594_; lean_object* v___x_595_; uint32_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec(v___f_585_);
v_pushOutput_594_ = lean_ctor_get(v_inst_583_, 0);
lean_inc(v_pushOutput_594_);
lean_dec_ref(v_inst_583_);
v___x_595_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_596_ = 32;
v___x_597_ = lean_int_sub(v_indent_582_, v___x_588_);
lean_dec(v___x_588_);
v___x_598_ = l_Int_toNat(v___x_597_);
lean_dec(v___x_597_);
v___x_599_ = lean_string_pushn(v___x_595_, v___x_596_, v___x_598_);
v___x_600_ = lean_apply_1(v_pushOutput_594_, v___x_599_);
v___x_601_ = lean_apply_4(v_toBind_584_, lean_box(0), lean_box(0), v___x_600_, v___f_586_);
return v___x_601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed(lean_object* v_indent_602_, lean_object* v_inst_603_, lean_object* v_toBind_604_, lean_object* v___f_605_, lean_object* v___f_606_, lean_object* v_k_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(v_indent_602_, v_inst_603_, v_toBind_604_, v___f_605_, v___f_606_, v_k_607_);
lean_dec(v_indent_602_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9(lean_object* v_inst_609_, lean_object* v_activeTags_610_, lean_object* v_toBind_611_, lean_object* v___f_612_, lean_object* v_____r_613_){
_start:
{
lean_object* v_endTags_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_endTags_614_ = lean_ctor_get(v_inst_609_, 4);
lean_inc(v_endTags_614_);
lean_dec_ref(v_inst_609_);
v___x_615_ = lean_apply_1(v_endTags_614_, v_activeTags_610_);
v___x_616_ = lean_apply_4(v_toBind_611_, lean_box(0), lean_box(0), v___x_615_, v___f_612_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1(lean_object* v_gs_x27_617_, lean_object* v_tail_618_, lean_object* v_w_619_, lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_____r_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_apply_1(v_gs_x27_617_, v_tail_618_);
v___x_624_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_619_, v_inst_620_, v_inst_621_, v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(uint8_t v_flb_626_, lean_object* v_tail_627_, lean_object* v_tail_628_, lean_object* v_w_629_, lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_toBind_632_, lean_object* v_____r_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
lean_inc_ref(v_inst_631_);
lean_inc_ref(v_inst_630_);
lean_inc(v_w_629_);
v___x_634_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_626_, v_tail_627_, v_tail_628_, v_w_629_, v_inst_630_, v_inst_631_);
v___x_635_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_635_, 0, v_w_629_);
lean_closure_set(v___x_635_, 1, v_inst_630_);
lean_closure_set(v___x_635_, 2, v_inst_631_);
v___x_636_ = lean_apply_4(v_toBind_632_, lean_box(0), lean_box(0), v___x_634_, v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed(lean_object* v_flb_637_, lean_object* v_tail_638_, lean_object* v_tail_639_, lean_object* v_w_640_, lean_object* v_inst_641_, lean_object* v_inst_642_, lean_object* v_toBind_643_, lean_object* v_____r_644_){
_start:
{
uint8_t v_flb_1521__boxed_645_; lean_object* v_res_646_; 
v_flb_1521__boxed_645_ = lean_unbox(v_flb_637_);
v_res_646_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(v_flb_1521__boxed_645_, v_tail_638_, v_tail_639_, v_w_640_, v_inst_641_, v_inst_642_, v_toBind_643_, v_____r_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(lean_object* v_breakHere_648_, lean_object* v_w_649_, lean_object* v_inst_650_, lean_object* v_inst_651_, lean_object* v_endTags_652_, lean_object* v_activeTags_653_, lean_object* v_toBind_654_, lean_object* v_pushOutput_655_, lean_object* v___x_656_, lean_object* v___x_657_, lean_object* v_____x_658_){
_start:
{
if (lean_obj_tag(v_____x_658_) == 1)
{
lean_object* v_head_659_; lean_object* v_fla_660_; uint8_t v___x_661_; 
v_head_659_ = lean_ctor_get(v_____x_658_, 0);
v_fla_660_ = lean_ctor_get(v_head_659_, 0);
v___x_661_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_660_);
if (v___x_661_ == 0)
{
lean_dec_ref_known(v_____x_658_, 2);
lean_dec_ref(v___x_656_);
lean_dec(v_pushOutput_655_);
lean_dec(v_toBind_654_);
lean_dec(v_activeTags_653_);
lean_dec(v_endTags_652_);
lean_dec_ref(v_inst_651_);
lean_dec_ref(v_inst_650_);
lean_dec(v_w_649_);
lean_inc(v_breakHere_648_);
return v_breakHere_648_;
}
else
{
lean_object* v___f_662_; lean_object* v___f_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___f_662_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4), 5, 4);
lean_closure_set(v___f_662_, 0, v_w_649_);
lean_closure_set(v___f_662_, 1, v_inst_650_);
lean_closure_set(v___f_662_, 2, v_inst_651_);
lean_closure_set(v___f_662_, 3, v_____x_658_);
lean_inc(v_toBind_654_);
v___f_663_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_663_, 0, v_endTags_652_);
lean_closure_set(v___f_663_, 1, v_activeTags_653_);
lean_closure_set(v___f_663_, 2, v_toBind_654_);
lean_closure_set(v___f_663_, 3, v___f_662_);
v___x_664_ = lean_apply_1(v_pushOutput_655_, v___x_656_);
v___x_665_ = lean_apply_4(v_toBind_654_, lean_box(0), lean_box(0), v___x_664_, v___f_663_);
return v___x_665_;
}
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec(v_____x_658_);
lean_dec_ref(v___x_656_);
lean_dec(v_pushOutput_655_);
lean_dec(v_toBind_654_);
lean_dec(v_activeTags_653_);
lean_dec(v_endTags_652_);
lean_dec_ref(v_inst_651_);
lean_dec_ref(v_inst_650_);
lean_dec(v_w_649_);
v___x_666_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0));
v___x_667_ = l_panic___redArg(v___x_657_, v___x_666_);
return v___x_667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed(lean_object* v_breakHere_668_, lean_object* v_w_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_endTags_672_, lean_object* v_activeTags_673_, lean_object* v_toBind_674_, lean_object* v_pushOutput_675_, lean_object* v___x_676_, lean_object* v___x_677_, lean_object* v_____x_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(v_breakHere_668_, v_w_669_, v_inst_670_, v_inst_671_, v_endTags_672_, v_activeTags_673_, v_toBind_674_, v_pushOutput_675_, v___x_676_, v___x_677_, v_____x_678_);
lean_dec(v___x_677_);
lean_dec(v_breakHere_668_);
return v_res_679_;
}
}
static lean_object* _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_681_ = lean_string_length(v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(lean_object* v_a_682_, lean_object* v_p_683_, lean_object* v___x_684_, lean_object* v_indent_685_, lean_object* v_activeTags_686_, lean_object* v_tail_687_, lean_object* v_fla_688_, uint8_t v_flb_689_, lean_object* v_tail_690_, lean_object* v_w_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_toBind_694_, lean_object* v_gs_x27_695_, lean_object* v_____r_696_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v_is_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_697_ = lean_string_utf8_next(v_a_682_, v_p_683_);
v___x_698_ = lean_string_utf8_extract(v_a_682_, v___x_697_, v___x_684_);
lean_dec(v___x_697_);
v___x_699_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
v___x_700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v_indent_685_);
lean_ctor_set(v___x_700_, 2, v_activeTags_686_);
v_is_701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_is_701_, 0, v___x_700_);
lean_ctor_set(v_is_701_, 1, v_tail_687_);
v___x_702_ = lean_box(1);
v___x_703_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_688_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec_ref(v_gs_x27_695_);
lean_inc_ref(v_inst_693_);
lean_inc_ref(v_inst_692_);
lean_inc(v_w_691_);
v___x_704_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_689_, v_is_701_, v_tail_690_, v_w_691_, v_inst_692_, v_inst_693_);
v___x_705_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_705_, 0, v_w_691_);
lean_closure_set(v___x_705_, 1, v_inst_692_);
lean_closure_set(v___x_705_, 2, v_inst_693_);
v___x_706_ = lean_apply_4(v_toBind_694_, lean_box(0), lean_box(0), v___x_704_, v___x_705_);
return v___x_706_;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec(v_toBind_694_);
lean_dec(v_tail_690_);
v___x_707_ = lean_apply_1(v_gs_x27_695_, v_is_701_);
v___x_708_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_691_, v_inst_692_, v_inst_693_, v___x_707_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed(lean_object* v_a_709_, lean_object* v_p_710_, lean_object* v___x_711_, lean_object* v_indent_712_, lean_object* v_activeTags_713_, lean_object* v_tail_714_, lean_object* v_fla_715_, lean_object* v_flb_716_, lean_object* v_tail_717_, lean_object* v_w_718_, lean_object* v_inst_719_, lean_object* v_inst_720_, lean_object* v_toBind_721_, lean_object* v_gs_x27_722_, lean_object* v_____r_723_){
_start:
{
uint8_t v_flb_1545__boxed_724_; lean_object* v_res_725_; 
v_flb_1545__boxed_724_ = lean_unbox(v_flb_716_);
v_res_725_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(v_a_709_, v_p_710_, v___x_711_, v_indent_712_, v_activeTags_713_, v_tail_714_, v_fla_715_, v_flb_1545__boxed_724_, v_tail_717_, v_w_718_, v_inst_719_, v_inst_720_, v_toBind_721_, v_gs_x27_722_, v_____r_723_);
lean_dec(v_fla_715_);
lean_dec(v___x_711_);
lean_dec(v_p_710_);
lean_dec_ref(v_a_709_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(lean_object* v_activeTags_726_, lean_object* v_a_727_, lean_object* v_indent_728_, lean_object* v_tail_729_, lean_object* v_gs_x27_730_, lean_object* v_w_731_, lean_object* v_inst_732_, lean_object* v_inst_733_, lean_object* v_____r_734_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = lean_nat_add(v_activeTags_726_, v___x_735_);
v___x_737_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_737_, 0, v_a_727_);
lean_ctor_set(v___x_737_, 1, v_indent_728_);
lean_ctor_set(v___x_737_, 2, v___x_736_);
v___x_738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v_tail_729_);
v___x_739_ = lean_apply_1(v_gs_x27_730_, v___x_738_);
v___x_740_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_731_, v_inst_732_, v_inst_733_, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed(lean_object* v_activeTags_741_, lean_object* v_a_742_, lean_object* v_indent_743_, lean_object* v_tail_744_, lean_object* v_gs_x27_745_, lean_object* v_w_746_, lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v_____r_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(v_activeTags_741_, v_a_742_, v_indent_743_, v_tail_744_, v_gs_x27_745_, v_w_746_, v_inst_747_, v_inst_748_, v_____r_749_);
lean_dec(v_activeTags_741_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(lean_object* v_w_751_, lean_object* v_inst_752_, lean_object* v_inst_753_, lean_object* v_x_754_){
_start:
{
if (lean_obj_tag(v_x_754_) == 0)
{
lean_object* v_toApplicative_755_; lean_object* v_toPure_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_toApplicative_755_ = lean_ctor_get(v_inst_752_, 0);
lean_inc_ref(v_toApplicative_755_);
lean_dec_ref(v_inst_753_);
lean_dec_ref(v_inst_752_);
lean_dec(v_w_751_);
v_toPure_756_ = lean_ctor_get(v_toApplicative_755_, 1);
lean_inc(v_toPure_756_);
lean_dec_ref(v_toApplicative_755_);
v___x_757_ = lean_box(0);
v___x_758_ = lean_apply_2(v_toPure_756_, lean_box(0), v___x_757_);
return v___x_758_;
}
else
{
lean_object* v_head_759_; lean_object* v_items_760_; 
v_head_759_ = lean_ctor_get(v_x_754_, 0);
v_items_760_ = lean_ctor_get(v_head_759_, 1);
lean_inc(v_items_760_);
if (lean_obj_tag(v_items_760_) == 0)
{
lean_object* v_tail_761_; 
v_tail_761_ = lean_ctor_get(v_x_754_, 1);
lean_inc(v_tail_761_);
lean_dec_ref_known(v_x_754_, 2);
v_x_754_ = v_tail_761_;
goto _start;
}
else
{
lean_object* v_head_763_; lean_object* v_toBind_764_; lean_object* v_tail_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_910_; 
lean_inc(v_head_759_);
v_head_763_ = lean_ctor_get(v_items_760_, 0);
lean_inc(v_head_763_);
v_toBind_764_ = lean_ctor_get(v_inst_752_, 1);
v_tail_765_ = lean_ctor_get(v_x_754_, 1);
v_isSharedCheck_910_ = !lean_is_exclusive(v_x_754_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v_x_754_, 0);
lean_dec(v_unused_911_);
v___x_767_ = v_x_754_;
v_isShared_768_ = v_isSharedCheck_910_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_tail_765_);
lean_dec(v_x_754_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_910_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v_fla_769_; uint8_t v_flb_770_; lean_object* v_tail_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_908_; 
v_fla_769_ = lean_ctor_get(v_head_759_, 0);
lean_inc(v_fla_769_);
v_flb_770_ = lean_ctor_get_uint8(v_head_759_, sizeof(void*)*2);
lean_dec(v_head_759_);
v_tail_771_ = lean_ctor_get(v_items_760_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v_items_760_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; 
v_unused_909_ = lean_ctor_get(v_items_760_, 0);
lean_dec(v_unused_909_);
v___x_773_ = v_items_760_;
v_isShared_774_ = v_isSharedCheck_908_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_tail_771_);
lean_dec(v_items_760_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_908_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_f_775_; lean_object* v_indent_776_; lean_object* v_activeTags_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_907_; 
v_f_775_ = lean_ctor_get(v_head_763_, 0);
v_indent_776_ = lean_ctor_get(v_head_763_, 1);
v_activeTags_777_ = lean_ctor_get(v_head_763_, 2);
v_isSharedCheck_907_ = !lean_is_exclusive(v_head_763_);
if (v_isSharedCheck_907_ == 0)
{
v___x_779_ = v_head_763_;
v_isShared_780_ = v_isSharedCheck_907_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_activeTags_777_);
lean_inc(v_indent_776_);
lean_inc(v_f_775_);
lean_dec(v_head_763_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_907_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v_gs_x27_782_; 
v___x_781_ = lean_box(v_flb_770_);
lean_inc(v_tail_765_);
lean_inc(v_fla_769_);
v_gs_x27_782_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v_gs_x27_782_, 0, v_fla_769_);
lean_closure_set(v_gs_x27_782_, 1, v___x_781_);
lean_closure_set(v_gs_x27_782_, 2, v_tail_765_);
switch(lean_obj_tag(v_f_775_))
{
case 0:
{
lean_object* v_endTags_783_; lean_object* v___f_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
lean_inc(v_toBind_764_);
lean_del_object(v___x_779_);
lean_dec(v_indent_776_);
lean_del_object(v___x_773_);
lean_dec(v_fla_769_);
lean_del_object(v___x_767_);
lean_dec(v_tail_765_);
v_endTags_783_ = lean_ctor_get(v_inst_753_, 4);
lean_inc(v_endTags_783_);
v___f_784_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_784_, 0, v_gs_x27_782_);
lean_closure_set(v___f_784_, 1, v_tail_771_);
lean_closure_set(v___f_784_, 2, v_w_751_);
lean_closure_set(v___f_784_, 3, v_inst_752_);
lean_closure_set(v___f_784_, 4, v_inst_753_);
v___x_785_ = lean_apply_1(v_endTags_783_, v_activeTags_777_);
v___x_786_ = lean_apply_4(v_toBind_764_, lean_box(0), lean_box(0), v___x_785_, v___f_784_);
return v___x_786_;
}
case 1:
{
lean_inc(v_toBind_764_);
lean_del_object(v___x_779_);
lean_del_object(v___x_773_);
lean_del_object(v___x_767_);
if (v_flb_770_ == 0)
{
uint8_t v___x_787_; 
lean_dec(v_tail_765_);
v___x_787_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_769_);
lean_dec(v_fla_769_);
if (v___x_787_ == 0)
{
lean_object* v_pushNewline_788_; lean_object* v_endTags_789_; lean_object* v___f_790_; lean_object* v___f_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_pushNewline_788_ = lean_ctor_get(v_inst_753_, 1);
lean_inc(v_pushNewline_788_);
v_endTags_789_ = lean_ctor_get(v_inst_753_, 4);
lean_inc(v_endTags_789_);
v___f_790_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_790_, 0, v_gs_x27_782_);
lean_closure_set(v___f_790_, 1, v_tail_771_);
lean_closure_set(v___f_790_, 2, v_w_751_);
lean_closure_set(v___f_790_, 3, v_inst_752_);
lean_closure_set(v___f_790_, 4, v_inst_753_);
lean_inc(v_toBind_764_);
v___f_791_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_791_, 0, v_endTags_789_);
lean_closure_set(v___f_791_, 1, v_activeTags_777_);
lean_closure_set(v___f_791_, 2, v_toBind_764_);
lean_closure_set(v___f_791_, 3, v___f_790_);
v___x_792_ = l_Int_toNat(v_indent_776_);
lean_dec(v_indent_776_);
v___x_793_ = lean_apply_1(v_pushNewline_788_, v___x_792_);
v___x_794_ = lean_apply_4(v_toBind_764_, lean_box(0), lean_box(0), v___x_793_, v___f_791_);
return v___x_794_;
}
else
{
lean_object* v_pushOutput_795_; lean_object* v_endTags_796_; lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec(v_indent_776_);
v_pushOutput_795_ = lean_ctor_get(v_inst_753_, 0);
lean_inc(v_pushOutput_795_);
v_endTags_796_ = lean_ctor_get(v_inst_753_, 4);
lean_inc(v_endTags_796_);
v___f_797_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_797_, 0, v_gs_x27_782_);
lean_closure_set(v___f_797_, 1, v_tail_771_);
lean_closure_set(v___f_797_, 2, v_w_751_);
lean_closure_set(v___f_797_, 3, v_inst_752_);
lean_closure_set(v___f_797_, 4, v_inst_753_);
lean_inc(v_toBind_764_);
v___f_798_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_798_, 0, v_endTags_796_);
lean_closure_set(v___f_798_, 1, v_activeTags_777_);
lean_closure_set(v___f_798_, 2, v_toBind_764_);
lean_closure_set(v___f_798_, 3, v___f_797_);
v___x_799_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_800_ = lean_apply_1(v_pushOutput_795_, v___x_799_);
v___x_801_ = lean_apply_4(v_toBind_764_, lean_box(0), lean_box(0), v___x_800_, v___f_798_);
return v___x_801_;
}
}
else
{
lean_object* v_pushOutput_802_; lean_object* v_pushNewline_803_; lean_object* v_endTags_804_; lean_object* v___x_805_; lean_object* v___f_806_; lean_object* v___f_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_breakHere_810_; uint8_t v___x_811_; 
lean_dec_ref(v_gs_x27_782_);
v_pushOutput_802_ = lean_ctor_get(v_inst_753_, 0);
v_pushNewline_803_ = lean_ctor_get(v_inst_753_, 1);
v_endTags_804_ = lean_ctor_get(v_inst_753_, 4);
v___x_805_ = lean_box(v_flb_770_);
lean_inc_n(v_toBind_764_, 3);
lean_inc_ref(v_inst_753_);
lean_inc_ref(v_inst_752_);
lean_inc(v_w_751_);
lean_inc(v_tail_765_);
lean_inc(v_tail_771_);
v___f_806_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_806_, 0, v___x_805_);
lean_closure_set(v___f_806_, 1, v_tail_771_);
lean_closure_set(v___f_806_, 2, v_tail_765_);
lean_closure_set(v___f_806_, 3, v_w_751_);
lean_closure_set(v___f_806_, 4, v_inst_752_);
lean_closure_set(v___f_806_, 5, v_inst_753_);
lean_closure_set(v___f_806_, 6, v_toBind_764_);
lean_inc(v_activeTags_777_);
lean_inc(v_endTags_804_);
v___f_807_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_807_, 0, v_endTags_804_);
lean_closure_set(v___f_807_, 1, v_activeTags_777_);
lean_closure_set(v___f_807_, 2, v_toBind_764_);
lean_closure_set(v___f_807_, 3, v___f_806_);
v___x_808_ = l_Int_toNat(v_indent_776_);
lean_dec(v_indent_776_);
lean_inc(v_pushNewline_803_);
v___x_809_ = lean_apply_1(v_pushNewline_803_, v___x_808_);
v_breakHere_810_ = lean_apply_4(v_toBind_764_, lean_box(0), lean_box(0), v___x_809_, v___f_807_);
v___x_811_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_769_);
lean_dec(v_fla_769_);
if (v___x_811_ == 0)
{
lean_dec(v_activeTags_777_);
lean_dec(v_tail_771_);
lean_dec(v_tail_765_);
lean_dec(v_toBind_764_);
lean_dec_ref(v_inst_753_);
lean_dec_ref(v_inst_752_);
lean_dec(v_w_751_);
return v_breakHere_810_;
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___f_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_812_ = lean_box(0);
lean_inc_ref_n(v_inst_752_, 2);
v___x_813_ = l_instInhabitedOfMonad___redArg(v_inst_752_, v___x_812_);
v___x_814_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
lean_inc(v_pushOutput_802_);
lean_inc(v_toBind_764_);
lean_inc(v_endTags_804_);
lean_inc_ref(v_inst_753_);
lean_inc(v_w_751_);
v___f_815_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed), 11, 10);
lean_closure_set(v___f_815_, 0, v_breakHere_810_);
lean_closure_set(v___f_815_, 1, v_w_751_);
lean_closure_set(v___f_815_, 2, v_inst_752_);
lean_closure_set(v___f_815_, 3, v_inst_753_);
lean_closure_set(v___f_815_, 4, v_endTags_804_);
lean_closure_set(v___f_815_, 5, v_activeTags_777_);
lean_closure_set(v___f_815_, 6, v_toBind_764_);
lean_closure_set(v___f_815_, 7, v_pushOutput_802_);
lean_closure_set(v___f_815_, 8, v___x_814_);
lean_closure_set(v___f_815_, 9, v___x_813_);
v___x_816_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_817_ = lean_nat_sub(v_w_751_, v___x_816_);
lean_dec(v_w_751_);
v___x_818_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_770_, v_tail_771_, v_tail_765_, v___x_817_, v_inst_752_, v_inst_753_);
v___x_819_ = lean_apply_4(v_toBind_764_, lean_box(0), lean_box(0), v___x_818_, v___f_815_);
return v___x_819_;
}
}
}
case 2:
{
uint8_t v_force_820_; lean_object* v___f_821_; lean_object* v___f_822_; lean_object* v___f_823_; uint8_t v___y_828_; uint8_t v___x_832_; 
lean_inc_n(v_toBind_764_, 3);
lean_del_object(v___x_779_);
lean_del_object(v___x_773_);
lean_del_object(v___x_767_);
lean_dec(v_tail_765_);
v_force_820_ = lean_ctor_get_uint8(v_f_775_, 0);
lean_dec_ref_known(v_f_775_, 0);
lean_inc_ref_n(v_inst_753_, 3);
v___f_821_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_821_, 0, v_gs_x27_782_);
lean_closure_set(v___f_821_, 1, v_tail_771_);
lean_closure_set(v___f_821_, 2, v_w_751_);
lean_closure_set(v___f_821_, 3, v_inst_752_);
lean_closure_set(v___f_821_, 4, v_inst_753_);
lean_inc_ref(v___f_821_);
lean_inc(v_activeTags_777_);
v___f_822_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9), 5, 4);
lean_closure_set(v___f_822_, 0, v_inst_753_);
lean_closure_set(v___f_822_, 1, v_activeTags_777_);
lean_closure_set(v___f_822_, 2, v_toBind_764_);
lean_closure_set(v___f_822_, 3, v___f_821_);
lean_inc_ref(v___f_822_);
v___f_823_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_823_, 0, v_indent_776_);
lean_closure_set(v___f_823_, 1, v_inst_753_);
lean_closure_set(v___f_823_, 2, v_toBind_764_);
lean_closure_set(v___f_823_, 3, v___f_822_);
lean_closure_set(v___f_823_, 4, v___f_822_);
v___x_832_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_769_);
lean_dec(v_fla_769_);
if (v___x_832_ == 0)
{
v___y_828_ = v___x_832_;
goto v___jp_827_;
}
else
{
if (v_force_820_ == 0)
{
v___y_828_ = v___x_832_;
goto v___jp_827_;
}
else
{
lean_dec_ref(v___f_821_);
lean_dec(v_activeTags_777_);
goto v___jp_824_;
}
}
v___jp_824_:
{
lean_object* v_currColumn_825_; lean_object* v___x_826_; 
v_currColumn_825_ = lean_ctor_get(v_inst_753_, 2);
lean_inc(v_currColumn_825_);
lean_dec_ref(v_inst_753_);
v___x_826_ = lean_apply_4(v_toBind_764_, lean_box(0), lean_box(0), v_currColumn_825_, v___f_823_);
return v___x_826_;
}
v___jp_827_:
{
if (v___y_828_ == 0)
{
lean_dec_ref(v___f_821_);
lean_dec(v_activeTags_777_);
goto v___jp_824_;
}
else
{
lean_object* v_endTags_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_dec_ref(v___f_823_);
v_endTags_829_ = lean_ctor_get(v_inst_753_, 4);
lean_inc(v_endTags_829_);
lean_dec_ref(v_inst_753_);
v___x_830_ = lean_apply_1(v_endTags_829_, v_activeTags_777_);
v___x_831_ = lean_apply_4(v_toBind_764_, lean_box(0), lean_box(0), v___x_830_, v___f_821_);
return v___x_831_;
}
}
}
case 3:
{
lean_object* v_a_833_; uint32_t v___x_834_; lean_object* v_p_835_; lean_object* v___x_836_; uint8_t v_decide_837_; 
lean_inc(v_toBind_764_);
lean_del_object(v___x_779_);
lean_del_object(v___x_773_);
lean_del_object(v___x_767_);
v_a_833_ = lean_ctor_get(v_f_775_, 0);
lean_inc_ref_n(v_a_833_, 2);
lean_dec_ref_known(v_f_775_, 1);
v___x_834_ = 10;
v_p_835_ = lean_string_posof(v_a_833_, v___x_834_);
v___x_836_ = lean_string_utf8_byte_size(v_a_833_);
v_decide_837_ = lean_nat_dec_eq(v_p_835_, v___x_836_);
if (v_decide_837_ == 0)
{
lean_object* v_pushOutput_838_; lean_object* v_pushNewline_839_; lean_object* v___x_840_; lean_object* v___f_841_; lean_object* v___f_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_pushOutput_838_ = lean_ctor_get(v_inst_753_, 0);
lean_inc(v_pushOutput_838_);
v_pushNewline_839_ = lean_ctor_get(v_inst_753_, 1);
lean_inc(v_pushNewline_839_);
v___x_840_ = lean_box(v_flb_770_);
lean_inc_n(v_toBind_764_, 2);
lean_inc(v_indent_776_);
lean_inc(v_p_835_);
lean_inc_ref(v_a_833_);
v___f_841_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed), 15, 14);
lean_closure_set(v___f_841_, 0, v_a_833_);
lean_closure_set(v___f_841_, 1, v_p_835_);
lean_closure_set(v___f_841_, 2, v___x_836_);
lean_closure_set(v___f_841_, 3, v_indent_776_);
lean_closure_set(v___f_841_, 4, v_activeTags_777_);
lean_closure_set(v___f_841_, 5, v_tail_771_);
lean_closure_set(v___f_841_, 6, v_fla_769_);
lean_closure_set(v___f_841_, 7, v___x_840_);
lean_closure_set(v___f_841_, 8, v_tail_765_);
lean_closure_set(v___f_841_, 9, v_w_751_);
lean_closure_set(v___f_841_, 10, v_inst_752_);
lean_closure_set(v___f_841_, 11, v_inst_753_);
lean_closure_set(v___f_841_, 12, v_toBind_764_);
lean_closure_set(v___f_841_, 13, v_gs_x27_782_);
v___f_842_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_842_, 0, v_indent_776_);
lean_closure_set(v___f_842_, 1, v_pushNewline_839_);
lean_closure_set(v___f_842_, 2, v_toBind_764_);
lean_closure_set(v___f_842_, 3, v___f_841_);
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = lean_string_utf8_extract(v_a_833_, v___x_843_, v_p_835_);
lean_dec(v_p_835_);
lean_dec_ref(v_a_833_);
v___x_845_ = lean_apply_1(v_pushOutput_838_, v___x_844_);
v___x_846_ = lean_apply_4(v_toBind_764_, lean_box(0), lean_box(0), v___x_845_, v___f_842_);
return v___x_846_;
}
else
{
lean_object* v_pushOutput_847_; lean_object* v_endTags_848_; lean_object* v___f_849_; lean_object* v___f_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v_p_835_);
lean_dec(v_indent_776_);
lean_dec(v_fla_769_);
lean_dec(v_tail_765_);
v_pushOutput_847_ = lean_ctor_get(v_inst_753_, 0);
lean_inc(v_pushOutput_847_);
v_endTags_848_ = lean_ctor_get(v_inst_753_, 4);
lean_inc(v_endTags_848_);
v___f_849_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_849_, 0, v_gs_x27_782_);
lean_closure_set(v___f_849_, 1, v_tail_771_);
lean_closure_set(v___f_849_, 2, v_w_751_);
lean_closure_set(v___f_849_, 3, v_inst_752_);
lean_closure_set(v___f_849_, 4, v_inst_753_);
lean_inc(v_toBind_764_);
v___f_850_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_850_, 0, v_endTags_848_);
lean_closure_set(v___f_850_, 1, v_activeTags_777_);
lean_closure_set(v___f_850_, 2, v_toBind_764_);
lean_closure_set(v___f_850_, 3, v___f_849_);
v___x_851_ = lean_apply_1(v_pushOutput_847_, v_a_833_);
v___x_852_ = lean_apply_4(v_toBind_764_, lean_box(0), lean_box(0), v___x_851_, v___f_850_);
return v___x_852_;
}
}
case 4:
{
lean_object* v_indent_853_; lean_object* v_f_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
lean_dec_ref(v_gs_x27_782_);
lean_del_object(v___x_767_);
v_indent_853_ = lean_ctor_get(v_f_775_, 0);
lean_inc(v_indent_853_);
v_f_854_ = lean_ctor_get(v_f_775_, 1);
lean_inc(v_f_854_);
lean_dec_ref_known(v_f_775_, 2);
v___x_855_ = lean_int_add(v_indent_776_, v_indent_853_);
lean_dec(v_indent_853_);
lean_dec(v_indent_776_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v___x_855_);
lean_ctor_set(v___x_779_, 0, v_f_854_);
v___x_857_ = v___x_779_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_f_854_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_863_, 2, v_activeTags_777_);
v___x_857_ = v_reuseFailAlloc_863_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_859_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_857_);
v___x_859_ = v___x_773_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_tail_771_);
v___x_859_ = v_reuseFailAlloc_862_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; 
v___x_860_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_769_, v_flb_770_, v_tail_765_, v___x_859_);
v_x_754_ = v___x_860_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_864_; lean_object* v_a_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
lean_dec_ref(v_gs_x27_782_);
v_a_864_ = lean_ctor_get(v_f_775_, 0);
lean_inc(v_a_864_);
v_a_865_ = lean_ctor_get(v_f_775_, 1);
lean_inc(v_a_865_);
lean_dec_ref_known(v_f_775_, 2);
v___x_866_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_776_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 2, v___x_866_);
lean_ctor_set(v___x_779_, 0, v_a_864_);
v___x_868_ = v___x_779_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_864_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_indent_776_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v___x_866_);
v___x_868_ = v_reuseFailAlloc_878_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_869_, 0, v_a_865_);
lean_ctor_set(v___x_869_, 1, v_indent_776_);
lean_ctor_set(v___x_869_, 2, v_activeTags_777_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_869_);
v___x_871_ = v___x_773_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_tail_771_);
v___x_871_ = v_reuseFailAlloc_877_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_873_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v___x_871_);
lean_ctor_set(v___x_767_, 0, v___x_868_);
v___x_873_ = v___x_767_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_871_);
v___x_873_ = v_reuseFailAlloc_876_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; 
v___x_874_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_769_, v_flb_770_, v_tail_765_, v___x_873_);
v_x_754_ = v___x_874_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_879_; uint8_t v_behavior_880_; uint8_t v___x_881_; 
lean_dec_ref(v_gs_x27_782_);
lean_del_object(v___x_767_);
v_a_879_ = lean_ctor_get(v_f_775_, 0);
lean_inc(v_a_879_);
v_behavior_880_ = lean_ctor_get_uint8(v_f_775_, sizeof(void*)*1);
lean_dec_ref_known(v_f_775_, 1);
v___x_881_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_769_);
if (v___x_881_ == 0)
{
lean_object* v___x_883_; 
lean_inc(v_toBind_764_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v_a_879_);
v___x_883_ = v___x_779_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_879_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_indent_776_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_activeTags_777_);
v___x_883_ = v_reuseFailAlloc_892_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_box(0);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_884_);
lean_ctor_set(v___x_773_, 0, v___x_883_);
v___x_886_ = v___x_773_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_884_);
v___x_886_ = v_reuseFailAlloc_891_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_887_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_769_, v_flb_770_, v_tail_765_, v_tail_771_);
lean_inc_ref(v_inst_753_);
lean_inc_ref(v_inst_752_);
lean_inc(v_w_751_);
v___x_888_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_behavior_880_, v___x_886_, v___x_887_, v_w_751_, v_inst_752_, v_inst_753_);
v___x_889_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_889_, 0, v_w_751_);
lean_closure_set(v___x_889_, 1, v_inst_752_);
lean_closure_set(v___x_889_, 2, v_inst_753_);
v___x_890_ = lean_apply_4(v_toBind_764_, lean_box(0), lean_box(0), v___x_888_, v___x_889_);
return v___x_890_;
}
}
}
else
{
lean_object* v___x_894_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v_a_879_);
v___x_894_ = v___x_779_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_879_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_indent_776_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v_activeTags_777_);
v___x_894_ = v_reuseFailAlloc_900_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_896_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_894_);
v___x_896_ = v___x_773_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_tail_771_);
v___x_896_ = v_reuseFailAlloc_899_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; 
v___x_897_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_769_, v_flb_770_, v_tail_765_, v___x_896_);
v_x_754_ = v___x_897_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_901_; lean_object* v_a_902_; lean_object* v_startTag_903_; lean_object* v___f_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_inc(v_toBind_764_);
lean_del_object(v___x_779_);
lean_del_object(v___x_773_);
lean_dec(v_fla_769_);
lean_del_object(v___x_767_);
lean_dec(v_tail_765_);
v_a_901_ = lean_ctor_get(v_f_775_, 0);
lean_inc(v_a_901_);
v_a_902_ = lean_ctor_get(v_f_775_, 1);
lean_inc(v_a_902_);
lean_dec_ref_known(v_f_775_, 2);
v_startTag_903_ = lean_ctor_get(v_inst_753_, 3);
lean_inc(v_startTag_903_);
v___f_904_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed), 9, 8);
lean_closure_set(v___f_904_, 0, v_activeTags_777_);
lean_closure_set(v___f_904_, 1, v_a_902_);
lean_closure_set(v___f_904_, 2, v_indent_776_);
lean_closure_set(v___f_904_, 3, v_tail_771_);
lean_closure_set(v___f_904_, 4, v_gs_x27_782_);
lean_closure_set(v___f_904_, 5, v_w_751_);
lean_closure_set(v___f_904_, 6, v_inst_752_);
lean_closure_set(v___f_904_, 7, v_inst_753_);
v___x_905_ = lean_apply_1(v_startTag_903_, v_a_901_);
v___x_906_ = lean_apply_4(v_toBind_764_, lean_box(0), lean_box(0), v___x_905_, v___f_904_);
return v___x_906_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4(lean_object* v_w_912_, lean_object* v_inst_913_, lean_object* v_inst_914_, lean_object* v_____x_915_, lean_object* v_____r_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_912_, v_inst_913_, v_inst_914_, v_____x_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be(lean_object* v_m_918_, lean_object* v_w_919_, lean_object* v_inst_920_, lean_object* v_inst_921_, lean_object* v_x_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_919_, v_inst_920_, v_inst_921_, v_x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___redArg(lean_object* v_f_924_, lean_object* v_w_925_, lean_object* v_indent_926_, lean_object* v_inst_927_, lean_object* v_inst_928_){
_start:
{
lean_object* v___x_929_; uint8_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_929_ = lean_box(1);
v___x_930_ = 0;
v___x_931_ = lean_nat_to_int(v_indent_926_);
v___x_932_ = lean_unsigned_to_nat(0u);
v___x_933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_933_, 0, v_f_924_);
lean_ctor_set(v___x_933_, 1, v___x_931_);
lean_ctor_set(v___x_933_, 2, v___x_932_);
v___x_934_ = lean_box(0);
v___x_935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_936_, 0, v___x_929_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
lean_ctor_set_uint8(v___x_936_, sizeof(void*)*2, v___x_930_);
v___x_937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_934_);
v___x_938_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_925_, v_inst_927_, v_inst_928_, v___x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM(lean_object* v_m_939_, lean_object* v_f_940_, lean_object* v_w_941_, lean_object* v_indent_942_, lean_object* v_inst_943_, lean_object* v_inst_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Std_Format_prettyM___redArg(v_f_940_, v_w_941_, v_indent_942_, v_inst_943_, v_inst_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_bracket(lean_object* v_l_946_, lean_object* v_f_947_, lean_object* v_r_948_){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; lean_object* v___x_957_; 
v___x_949_ = lean_string_length(v_l_946_);
v___x_950_ = lean_nat_to_int(v___x_949_);
v___x_951_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_951_, 0, v_l_946_);
v___x_952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set(v___x_952_, 1, v_f_947_);
v___x_953_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_953_, 0, v_r_948_);
v___x_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_950_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = 0;
v___x_957_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set_uint8(v___x_957_, sizeof(void*)*1, v___x_956_);
return v___x_957_;
}
}
static lean_object* _init_l_Std_Format_paren___closed__2(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_Std_Format_paren___closed__0));
v___x_961_ = lean_string_length(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l_Std_Format_paren___closed__3(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_obj_once(&l_Std_Format_paren___closed__2, &l_Std_Format_paren___closed__2_once, _init_l_Std_Format_paren___closed__2);
v___x_963_ = lean_nat_to_int(v___x_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_paren(lean_object* v_f_968_){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; lean_object* v___x_976_; 
v___x_969_ = lean_obj_once(&l_Std_Format_paren___closed__3, &l_Std_Format_paren___closed__3_once, _init_l_Std_Format_paren___closed__3);
v___x_970_ = ((lean_object*)(l_Std_Format_paren___closed__4));
v___x_971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v_f_968_);
v___x_972_ = ((lean_object*)(l_Std_Format_paren___closed__5));
v___x_973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_969_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = 0;
v___x_976_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*1, v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l_Std_Format_sbracket___closed__2(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = ((lean_object*)(l_Std_Format_sbracket___closed__0));
v___x_980_ = lean_string_length(v___x_979_);
return v___x_980_;
}
}
static lean_object* _init_l_Std_Format_sbracket___closed__3(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_obj_once(&l_Std_Format_sbracket___closed__2, &l_Std_Format_sbracket___closed__2_once, _init_l_Std_Format_sbracket___closed__2);
v___x_982_ = lean_nat_to_int(v___x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_sbracket(lean_object* v_f_987_){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; lean_object* v___x_995_; 
v___x_988_ = lean_obj_once(&l_Std_Format_sbracket___closed__3, &l_Std_Format_sbracket___closed__3_once, _init_l_Std_Format_sbracket___closed__3);
v___x_989_ = ((lean_object*)(l_Std_Format_sbracket___closed__4));
v___x_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v_f_987_);
v___x_991_ = ((lean_object*)(l_Std_Format_sbracket___closed__5));
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_988_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = 0;
v___x_995_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*1, v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_bracketFill(lean_object* v_l_996_, lean_object* v_f_997_, lean_object* v_r_998_){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_999_ = lean_string_length(v_l_996_);
v___x_1000_ = lean_nat_to_int(v___x_999_);
v___x_1001_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1001_, 0, v_l_996_);
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v_f_997_);
v___x_1003_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1003_, 0, v_r_998_);
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1000_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Std_Format_fill(v___x_1005_);
return v___x_1006_;
}
}
static lean_object* _init_l_Std_Format_defIndent(void){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_unsigned_to_nat(2u);
return v___x_1007_;
}
}
static uint8_t _init_l_Std_Format_defUnicode(void){
_start:
{
uint8_t v___x_1008_; 
v___x_1008_ = 1;
return v___x_1008_;
}
}
static lean_object* _init_l_Std_Format_defWidth(void){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_unsigned_to_nat(120u);
return v___x_1009_;
}
}
static lean_object* _init_l_Std_Format_nestD___closed__0(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_unsigned_to_nat(2u);
v___x_1011_ = lean_nat_to_int(v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nestD(lean_object* v_f_1012_){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_obj_once(&l_Std_Format_nestD___closed__0, &l_Std_Format_nestD___closed__0_once, _init_l_Std_Format_nestD___closed__0);
v___x_1014_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v_f_1012_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_indentD(lean_object* v_f_1015_){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = lean_box(1);
v___x_1017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v_f_1015_);
v___x_1018_ = l_Std_Format_nestD(v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(lean_object* v_s_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_out_1021_; lean_object* v_column_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1034_; 
v_out_1021_ = lean_ctor_get(v___y_1020_, 0);
v_column_1022_ = lean_ctor_get(v___y_1020_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___y_1020_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1024_ = v___y_1020_;
v_isShared_1025_ = v_isSharedCheck_1034_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_column_1022_);
lean_inc(v_out_1021_);
lean_dec(v___y_1020_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1034_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_string_append(v_out_1021_, v_s_1019_);
v___x_1028_ = lean_string_length(v_s_1019_);
v___x_1029_ = lean_nat_add(v_column_1022_, v___x_1028_);
lean_dec(v___x_1028_);
lean_dec(v_column_1022_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 1, v___x_1029_);
lean_ctor_set(v___x_1024_, 0, v___x_1027_);
v___x_1031_ = v___x_1024_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1026_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
return v___x_1032_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0___boxed(lean_object* v_s_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(v_s_1035_, v___y_1036_);
lean_dec_ref(v_s_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1(lean_object* v_indent_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_out_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1054_; 
v_out_1041_ = lean_ctor_get(v___y_1040_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___y_1040_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; 
v_unused_1055_ = lean_ctor_get(v___y_1040_, 1);
lean_dec(v_unused_1055_);
v___x_1043_ = v___y_1040_;
v_isShared_1044_ = v_isSharedCheck_1054_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_out_1041_);
lean_dec(v___y_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1054_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; uint32_t v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1045_ = lean_box(0);
v___x_1046_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1047_ = 32;
lean_inc(v_indent_1039_);
v___x_1048_ = lean_string_pushn(v___x_1046_, v___x_1047_, v_indent_1039_);
v___x_1049_ = lean_string_append(v_out_1041_, v___x_1048_);
lean_dec_ref(v___x_1048_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 1, v_indent_1039_);
lean_ctor_set(v___x_1043_, 0, v___x_1049_);
v___x_1051_ = v___x_1043_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_indent_1039_);
v___x_1051_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1045_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
return v___x_1052_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__2(lean_object* v_____do__lift_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_column_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
v_column_1058_ = lean_ctor_get(v_____do__lift_1056_, 1);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_____do__lift_1056_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; 
v_unused_1066_ = lean_ctor_get(v_____do__lift_1056_, 0);
lean_dec(v_unused_1066_);
v___x_1060_ = v_____do__lift_1056_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_column_1058_);
lean_dec(v_____do__lift_1056_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 1, v___y_1057_);
lean_ctor_set(v___x_1060_, 0, v_column_1058_);
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_column_1058_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v___y_1057_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(lean_object* v_x_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___y_1068_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3___boxed(lean_object* v_x_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(v_x_1071_, v___y_1072_);
lean_dec(v_x_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(uint8_t v_flb_1109_, lean_object* v_items_1110_, lean_object* v_gs_1111_, lean_object* v_w_1112_, lean_object* v___y_1113_){
_start:
{
uint8_t v___y_1115_; lean_object* v_column_1120_; uint8_t v___x_1121_; uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v_g_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v_r_1128_; lean_object* v___y_1130_; uint8_t v_foundLine_1135_; lean_object* v_space_1136_; uint8_t v___x_1137_; 
v_column_1120_ = lean_ctor_get(v___y_1113_, 1);
v___x_1121_ = 0;
v___x_1122_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_1109_, v___x_1121_);
v___x_1123_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1123_, 0, v___x_1122_);
lean_inc(v_items_1110_);
v_g_1124_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_1124_, 0, v___x_1123_);
lean_ctor_set(v_g_1124_, 1, v_items_1110_);
lean_ctor_set_uint8(v_g_1124_, sizeof(void*)*2, v_flb_1109_);
v___x_1125_ = lean_box(0);
v___x_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1126_, 0, v_g_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = lean_nat_sub(v_w_1112_, v_column_1120_);
lean_inc(v___x_1127_);
lean_inc(v_column_1120_);
v_r_1128_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_1126_, v_column_1120_, v___x_1127_);
v_foundLine_1135_ = lean_ctor_get_uint8(v_r_1128_, sizeof(void*)*1);
v_space_1136_ = lean_ctor_get(v_r_1128_, 0);
lean_inc(v_space_1136_);
v___x_1137_ = lean_nat_dec_lt(v___x_1127_, v_space_1136_);
if (v___x_1137_ == 0)
{
if (v_foundLine_1135_ == 0)
{
lean_object* v___x_1138_; lean_object* v_r_u2082_1139_; uint8_t v_foundLine_1140_; uint8_t v_foundFlattenedHardLine_1141_; lean_object* v_space_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1150_; 
v___x_1138_ = lean_nat_sub(v___x_1127_, v_space_1136_);
lean_inc(v_column_1120_);
lean_inc(v_gs_1111_);
v_r_u2082_1139_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_1111_, v_column_1120_, v___x_1138_);
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
v___x_1146_ = lean_nat_add(v_space_1136_, v_space_1142_);
lean_dec(v_space_1142_);
lean_dec(v_space_1136_);
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
v___y_1130_ = v___x_1148_;
goto v___jp_1129_;
}
}
}
else
{
lean_dec(v_space_1136_);
lean_inc_ref(v_r_1128_);
v___y_1130_ = v_r_1128_;
goto v___jp_1129_;
}
}
else
{
lean_dec(v_space_1136_);
lean_inc_ref(v_r_1128_);
v___y_1130_ = v_r_1128_;
goto v___jp_1129_;
}
v___jp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1116_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1116_, 0, v___y_1115_);
v___x_1117_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v_items_1110_);
lean_ctor_set_uint8(v___x_1117_, sizeof(void*)*2, v_flb_1109_);
v___x_1118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v_gs_1111_);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
lean_ctor_set(v___x_1119_, 1, v___y_1113_);
return v___x_1119_;
}
v___jp_1129_:
{
uint8_t v_foundFlattenedHardLine_1131_; 
v_foundFlattenedHardLine_1131_ = lean_ctor_get_uint8(v_r_1128_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_1128_);
if (v_foundFlattenedHardLine_1131_ == 0)
{
lean_object* v_space_1132_; uint8_t v___x_1133_; 
v_space_1132_ = lean_ctor_get(v___y_1130_, 0);
lean_inc(v_space_1132_);
lean_dec_ref(v___y_1130_);
v___x_1133_ = lean_nat_dec_le(v_space_1132_, v___x_1127_);
lean_dec(v___x_1127_);
lean_dec(v_space_1132_);
v___y_1115_ = v___x_1133_;
goto v___jp_1114_;
}
else
{
uint8_t v___x_1134_; 
lean_dec_ref(v___y_1130_);
lean_dec(v___x_1127_);
v___x_1134_ = 0;
v___y_1115_ = v___x_1134_;
goto v___jp_1114_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1___boxed(lean_object* v_flb_1151_, lean_object* v_items_1152_, lean_object* v_gs_1153_, lean_object* v_w_1154_, lean_object* v___y_1155_){
_start:
{
uint8_t v_flb_boxed_1156_; lean_object* v_res_1157_; 
v_flb_boxed_1156_ = lean_unbox(v_flb_1151_);
v_res_1157_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_boxed_1156_, v_items_1152_, v_gs_1153_, v_w_1154_, v___y_1155_);
lean_dec(v_w_1154_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(lean_object* v_msg_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___f_1174_; lean_object* v___f_1175_; lean_object* v___f_1176_; lean_object* v___f_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_4870__overap_1186_; lean_object* v___x_1187_; 
v___f_1174_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0));
v___f_1175_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1));
v___f_1176_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2));
v___f_1177_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3));
v___x_1178_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4));
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
lean_ctor_set(v___x_1179_, 1, v___f_1174_);
v___x_1180_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5));
v___x_1181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
lean_ctor_set(v___x_1181_, 2, v___f_1175_);
lean_ctor_set(v___x_1181_, 3, v___f_1176_);
lean_ctor_set(v___x_1181_, 4, v___f_1177_);
v___x_1182_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6));
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = lean_box(0);
v___x_1185_ = l_instInhabitedOfMonad___redArg(v___x_1183_, v___x_1184_);
v___x_4870__overap_1186_ = lean_panic_fn_borrowed(v___x_1185_, v_msg_1172_);
lean_dec(v___x_1185_);
v___x_1187_ = lean_apply_1(v___x_4870__overap_1186_, v___y_1173_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(lean_object* v_w_1188_, lean_object* v_x_1189_, lean_object* v___y_1190_){
_start:
{
if (lean_obj_tag(v_x_1189_) == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_box(0);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v___y_1190_);
return v___x_1192_;
}
else
{
lean_object* v_head_1193_; lean_object* v_items_1194_; 
v_head_1193_ = lean_ctor_get(v_x_1189_, 0);
v_items_1194_ = lean_ctor_get(v_head_1193_, 1);
lean_inc(v_items_1194_);
if (lean_obj_tag(v_items_1194_) == 0)
{
lean_object* v_tail_1195_; 
v_tail_1195_ = lean_ctor_get(v_x_1189_, 1);
lean_inc(v_tail_1195_);
lean_dec_ref_known(v_x_1189_, 2);
v_x_1189_ = v_tail_1195_;
goto _start;
}
else
{
lean_object* v_head_1197_; lean_object* v_tail_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1468_; 
lean_inc(v_head_1193_);
v_head_1197_ = lean_ctor_get(v_items_1194_, 0);
lean_inc(v_head_1197_);
v_tail_1198_ = lean_ctor_get(v_x_1189_, 1);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_x_1189_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; 
v_unused_1469_ = lean_ctor_get(v_x_1189_, 0);
lean_dec(v_unused_1469_);
v___x_1200_ = v_x_1189_;
v_isShared_1201_ = v_isSharedCheck_1468_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_tail_1198_);
lean_dec(v_x_1189_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1468_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v_fla_1202_; uint8_t v_flb_1203_; lean_object* v_tail_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1466_; 
v_fla_1202_ = lean_ctor_get(v_head_1193_, 0);
lean_inc(v_fla_1202_);
v_flb_1203_ = lean_ctor_get_uint8(v_head_1193_, sizeof(void*)*2);
lean_dec(v_head_1193_);
v_tail_1204_ = lean_ctor_get(v_items_1194_, 1);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_items_1194_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v_items_1194_, 0);
lean_dec(v_unused_1467_);
v___x_1206_ = v_items_1194_;
v_isShared_1207_ = v_isSharedCheck_1466_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_tail_1204_);
lean_dec(v_items_1194_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1466_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v_f_1208_; lean_object* v_indent_1209_; lean_object* v_activeTags_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1465_; 
v_f_1208_ = lean_ctor_get(v_head_1197_, 0);
v_indent_1209_ = lean_ctor_get(v_head_1197_, 1);
v_activeTags_1210_ = lean_ctor_get(v_head_1197_, 2);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_head_1197_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1212_ = v_head_1197_;
v_isShared_1213_ = v_isSharedCheck_1465_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_activeTags_1210_);
lean_inc(v_indent_1209_);
lean_inc(v_f_1208_);
lean_dec(v_head_1197_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1465_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
uint8_t v___y_1247_; 
switch(lean_obj_tag(v_f_1208_))
{
case 0:
{
lean_object* v___x_1250_; 
lean_del_object(v___x_1212_);
lean_dec(v_activeTags_1210_);
lean_dec(v_indent_1209_);
lean_del_object(v___x_1206_);
lean_del_object(v___x_1200_);
v___x_1250_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1202_, v_flb_1203_, v_tail_1198_, v_tail_1204_);
v_x_1189_ = v___x_1250_;
goto _start;
}
case 1:
{
lean_del_object(v___x_1212_);
lean_dec(v_activeTags_1210_);
lean_del_object(v___x_1206_);
lean_del_object(v___x_1200_);
if (v_flb_1203_ == 0)
{
uint8_t v___x_1252_; 
v___x_1252_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1202_);
if (v___x_1252_ == 0)
{
lean_object* v_out_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1267_; 
v_out_1253_ = lean_ctor_get(v___y_1190_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___y_1190_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; 
v_unused_1268_ = lean_ctor_get(v___y_1190_, 1);
lean_dec(v_unused_1268_);
v___x_1255_ = v___y_1190_;
v_isShared_1256_ = v_isSharedCheck_1267_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_out_1253_);
lean_dec(v___y_1190_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1267_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; uint32_t v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1257_ = l_Int_toNat(v_indent_1209_);
lean_dec(v_indent_1209_);
v___x_1258_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1259_ = 32;
lean_inc(v___x_1257_);
v___x_1260_ = lean_string_pushn(v___x_1258_, v___x_1259_, v___x_1257_);
v___x_1261_ = lean_string_append(v_out_1253_, v___x_1260_);
lean_dec_ref(v___x_1260_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 1, v___x_1257_);
lean_ctor_set(v___x_1255_, 0, v___x_1261_);
v___x_1263_ = v___x_1255_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v___x_1257_);
v___x_1263_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1264_; 
v___x_1264_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1202_, v_flb_1203_, v_tail_1198_, v_tail_1204_);
v_x_1189_ = v___x_1264_;
v___y_1190_ = v___x_1263_;
goto _start;
}
}
}
else
{
lean_object* v_out_1269_; lean_object* v_column_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1283_; 
lean_dec(v_indent_1209_);
v_out_1269_ = lean_ctor_get(v___y_1190_, 0);
v_column_1270_ = lean_ctor_get(v___y_1190_, 1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___y_1190_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1272_ = v___y_1190_;
v_isShared_1273_ = v_isSharedCheck_1283_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_column_1270_);
lean_inc(v_out_1269_);
lean_dec(v___y_1190_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1283_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1274_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_1275_ = lean_string_append(v_out_1269_, v___x_1274_);
v___x_1276_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_1277_ = lean_nat_add(v_column_1270_, v___x_1276_);
lean_dec(v_column_1270_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 1, v___x_1277_);
lean_ctor_set(v___x_1272_, 0, v___x_1275_);
v___x_1279_ = v___x_1272_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1280_; 
v___x_1280_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1202_, v_flb_1203_, v_tail_1198_, v_tail_1204_);
v_x_1189_ = v___x_1280_;
v___y_1190_ = v___x_1279_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = l_Int_toNat(v_indent_1209_);
lean_dec(v_indent_1209_);
v___x_1285_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1202_);
lean_dec(v_fla_1202_);
if (v___x_1285_ == 0)
{
lean_object* v_out_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1301_; 
v_out_1286_ = lean_ctor_get(v___y_1190_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___y_1190_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; 
v_unused_1302_ = lean_ctor_get(v___y_1190_, 1);
lean_dec(v_unused_1302_);
v___x_1288_ = v___y_1190_;
v_isShared_1289_ = v_isSharedCheck_1301_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_out_1286_);
lean_dec(v___y_1190_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1301_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; uint32_t v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1290_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1291_ = 32;
lean_inc(v___x_1284_);
v___x_1292_ = lean_string_pushn(v___x_1290_, v___x_1291_, v___x_1284_);
v___x_1293_ = lean_string_append(v_out_1286_, v___x_1292_);
lean_dec_ref(v___x_1292_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 1, v___x_1284_);
lean_ctor_set(v___x_1288_, 0, v___x_1293_);
v___x_1295_ = v___x_1288_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v___x_1284_);
v___x_1295_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
lean_object* v___x_1296_; lean_object* v_fst_1297_; lean_object* v_snd_1298_; 
v___x_1296_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1203_, v_tail_1204_, v_tail_1198_, v_w_1188_, v___x_1295_);
v_fst_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_fst_1297_);
v_snd_1298_ = lean_ctor_get(v___x_1296_, 1);
lean_inc(v_snd_1298_);
lean_dec_ref(v___x_1296_);
v_x_1189_ = v_fst_1297_;
v___y_1190_ = v_snd_1298_;
goto _start;
}
}
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v_fst_1307_; 
v___x_1303_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_1304_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_1305_ = lean_nat_sub(v_w_1188_, v___x_1304_);
lean_inc(v_tail_1198_);
lean_inc(v_tail_1204_);
v___x_1306_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1203_, v_tail_1204_, v_tail_1198_, v___x_1305_, v___y_1190_);
lean_dec(v___x_1305_);
v_fst_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_fst_1307_);
if (lean_obj_tag(v_fst_1307_) == 1)
{
lean_object* v_head_1308_; lean_object* v_snd_1309_; lean_object* v_fla_1310_; uint8_t v___x_1311_; 
v_head_1308_ = lean_ctor_get(v_fst_1307_, 0);
v_snd_1309_ = lean_ctor_get(v___x_1306_, 1);
lean_inc(v_snd_1309_);
lean_dec_ref(v___x_1306_);
v_fla_1310_ = lean_ctor_get(v_head_1308_, 0);
v___x_1311_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1310_);
if (v___x_1311_ == 0)
{
lean_object* v_out_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref_known(v_fst_1307_, 2);
v_out_1312_ = lean_ctor_get(v_snd_1309_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_snd_1309_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; 
v_unused_1328_ = lean_ctor_get(v_snd_1309_, 1);
lean_dec(v_unused_1328_);
v___x_1314_ = v_snd_1309_;
v_isShared_1315_ = v_isSharedCheck_1327_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_out_1312_);
lean_dec(v_snd_1309_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1327_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; uint32_t v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1316_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1317_ = 32;
lean_inc(v___x_1284_);
v___x_1318_ = lean_string_pushn(v___x_1316_, v___x_1317_, v___x_1284_);
v___x_1319_ = lean_string_append(v_out_1312_, v___x_1318_);
lean_dec_ref(v___x_1318_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 1, v___x_1284_);
lean_ctor_set(v___x_1314_, 0, v___x_1319_);
v___x_1321_ = v___x_1314_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___x_1284_);
v___x_1321_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; lean_object* v_fst_1323_; lean_object* v_snd_1324_; 
v___x_1322_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1203_, v_tail_1204_, v_tail_1198_, v_w_1188_, v___x_1321_);
v_fst_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_fst_1323_);
v_snd_1324_ = lean_ctor_get(v___x_1322_, 1);
lean_inc(v_snd_1324_);
lean_dec_ref(v___x_1322_);
v_x_1189_ = v_fst_1323_;
v___y_1190_ = v_snd_1324_;
goto _start;
}
}
}
else
{
lean_object* v_out_1329_; lean_object* v_column_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v___x_1284_);
lean_dec(v_tail_1204_);
lean_dec(v_tail_1198_);
v_out_1329_ = lean_ctor_get(v_snd_1309_, 0);
v_column_1330_ = lean_ctor_get(v_snd_1309_, 1);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_snd_1309_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1332_ = v_snd_1309_;
v_isShared_1333_ = v_isSharedCheck_1340_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_column_1330_);
lean_inc(v_out_1329_);
lean_dec(v_snd_1309_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1340_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1334_ = lean_string_append(v_out_1329_, v___x_1303_);
v___x_1335_ = lean_nat_add(v_column_1330_, v___x_1304_);
lean_dec(v_column_1330_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 1, v___x_1335_);
lean_ctor_set(v___x_1332_, 0, v___x_1334_);
v___x_1337_ = v___x_1332_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
v_x_1189_ = v_fst_1307_;
v___y_1190_ = v___x_1337_;
goto _start;
}
}
}
}
else
{
lean_object* v_snd_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec(v_fst_1307_);
lean_dec(v___x_1284_);
lean_dec(v_tail_1204_);
lean_dec(v_tail_1198_);
v_snd_1341_ = lean_ctor_get(v___x_1306_, 1);
lean_inc(v_snd_1341_);
lean_dec_ref(v___x_1306_);
v___x_1342_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0));
v___x_1343_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(v___x_1342_, v_snd_1341_);
return v___x_1343_;
}
}
}
}
case 2:
{
uint8_t v_force_1344_; uint8_t v___x_1345_; 
lean_del_object(v___x_1212_);
lean_dec(v_activeTags_1210_);
lean_del_object(v___x_1206_);
lean_del_object(v___x_1200_);
v_force_1344_ = lean_ctor_get_uint8(v_f_1208_, 0);
lean_dec_ref_known(v_f_1208_, 0);
v___x_1345_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1202_);
if (v___x_1345_ == 0)
{
v___y_1247_ = v___x_1345_;
goto v___jp_1246_;
}
else
{
if (v_force_1344_ == 0)
{
v___y_1247_ = v___x_1345_;
goto v___jp_1246_;
}
else
{
goto v___jp_1214_;
}
}
}
case 3:
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1404_; 
lean_del_object(v___x_1200_);
v_a_1346_ = lean_ctor_get(v_f_1208_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_f_1208_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1348_ = v_f_1208_;
v_isShared_1349_ = v_isSharedCheck_1404_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v_f_1208_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1404_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
uint32_t v___x_1350_; lean_object* v_p_1351_; lean_object* v___x_1352_; uint8_t v_decide_1353_; 
v___x_1350_ = 10;
lean_inc_ref(v_a_1346_);
v_p_1351_ = lean_string_posof(v_a_1346_, v___x_1350_);
v___x_1352_ = lean_string_utf8_byte_size(v_a_1346_);
v_decide_1353_ = lean_nat_dec_eq(v_p_1351_, v___x_1352_);
if (v_decide_1353_ == 0)
{
lean_object* v_out_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1388_; 
v_out_1354_ = lean_ctor_get(v___y_1190_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___y_1190_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; 
v_unused_1389_ = lean_ctor_get(v___y_1190_, 1);
lean_dec(v_unused_1389_);
v___x_1356_ = v___y_1190_;
v_isShared_1357_ = v_isSharedCheck_1388_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_out_1354_);
lean_dec(v___y_1190_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1388_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint32_t v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = lean_string_utf8_extract(v_a_1346_, v___x_1358_, v_p_1351_);
v___x_1360_ = lean_string_append(v_out_1354_, v___x_1359_);
lean_dec_ref(v___x_1359_);
v___x_1361_ = l_Int_toNat(v_indent_1209_);
v___x_1362_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1363_ = 32;
lean_inc(v___x_1361_);
v___x_1364_ = lean_string_pushn(v___x_1362_, v___x_1363_, v___x_1361_);
v___x_1365_ = lean_string_append(v___x_1360_, v___x_1364_);
lean_dec_ref(v___x_1364_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 1, v___x_1361_);
lean_ctor_set(v___x_1356_, 0, v___x_1365_);
v___x_1367_ = v___x_1356_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v___x_1361_);
v___x_1367_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1368_ = lean_string_utf8_next(v_a_1346_, v_p_1351_);
lean_dec(v_p_1351_);
v___x_1369_ = lean_string_utf8_extract(v_a_1346_, v___x_1368_, v___x_1352_);
lean_dec(v___x_1368_);
lean_dec_ref(v_a_1346_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1369_);
v___x_1371_ = v___x_1348_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1373_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___x_1371_);
v___x_1373_ = v___x_1212_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_indent_1209_);
lean_ctor_set(v_reuseFailAlloc_1385_, 2, v_activeTags_1210_);
v___x_1373_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v_is_1375_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1373_);
v_is_1375_ = v___x_1206_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_tail_1204_);
v_is_1375_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1376_ = lean_box(1);
v___x_1377_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_1202_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; lean_object* v_fst_1379_; lean_object* v_snd_1380_; 
lean_dec(v_fla_1202_);
v___x_1378_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1203_, v_is_1375_, v_tail_1198_, v_w_1188_, v___x_1367_);
v_fst_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_fst_1379_);
v_snd_1380_ = lean_ctor_get(v___x_1378_, 1);
lean_inc(v_snd_1380_);
lean_dec_ref(v___x_1378_);
v_x_1189_ = v_fst_1379_;
v___y_1190_ = v_snd_1380_;
goto _start;
}
else
{
lean_object* v___x_1382_; 
v___x_1382_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1202_, v_flb_1203_, v_tail_1198_, v_is_1375_);
v_x_1189_ = v___x_1382_;
v___y_1190_ = v___x_1367_;
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
lean_object* v_out_1390_; lean_object* v_column_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1403_; 
lean_dec(v_p_1351_);
lean_del_object(v___x_1348_);
lean_del_object(v___x_1212_);
lean_dec(v_activeTags_1210_);
lean_dec(v_indent_1209_);
lean_del_object(v___x_1206_);
v_out_1390_ = lean_ctor_get(v___y_1190_, 0);
v_column_1391_ = lean_ctor_get(v___y_1190_, 1);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___y_1190_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1393_ = v___y_1190_;
v_isShared_1394_ = v_isSharedCheck_1403_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_column_1391_);
lean_inc(v_out_1390_);
lean_dec(v___y_1190_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1403_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1395_ = lean_string_append(v_out_1390_, v_a_1346_);
v___x_1396_ = lean_string_length(v_a_1346_);
lean_dec_ref(v_a_1346_);
v___x_1397_ = lean_nat_add(v_column_1391_, v___x_1396_);
lean_dec(v___x_1396_);
lean_dec(v_column_1391_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 1, v___x_1397_);
lean_ctor_set(v___x_1393_, 0, v___x_1395_);
v___x_1399_ = v___x_1393_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; 
v___x_1400_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1202_, v_flb_1203_, v_tail_1198_, v_tail_1204_);
v_x_1189_ = v___x_1400_;
v___y_1190_ = v___x_1399_;
goto _start;
}
}
}
}
}
case 4:
{
lean_object* v_indent_1405_; lean_object* v_f_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
lean_del_object(v___x_1200_);
v_indent_1405_ = lean_ctor_get(v_f_1208_, 0);
lean_inc(v_indent_1405_);
v_f_1406_ = lean_ctor_get(v_f_1208_, 1);
lean_inc(v_f_1406_);
lean_dec_ref_known(v_f_1208_, 2);
v___x_1407_ = lean_int_add(v_indent_1209_, v_indent_1405_);
lean_dec(v_indent_1405_);
lean_dec(v_indent_1209_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v___x_1407_);
lean_ctor_set(v___x_1212_, 0, v_f_1406_);
v___x_1409_ = v___x_1212_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_f_1406_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_activeTags_1210_);
v___x_1409_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1411_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1409_);
v___x_1411_ = v___x_1206_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_tail_1204_);
v___x_1411_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; 
v___x_1412_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1202_, v_flb_1203_, v_tail_1198_, v___x_1411_);
v_x_1189_ = v___x_1412_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_1416_; lean_object* v_a_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; 
v_a_1416_ = lean_ctor_get(v_f_1208_, 0);
lean_inc(v_a_1416_);
v_a_1417_ = lean_ctor_get(v_f_1208_, 1);
lean_inc(v_a_1417_);
lean_dec_ref_known(v_f_1208_, 2);
v___x_1418_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_1209_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 2, v___x_1418_);
lean_ctor_set(v___x_1212_, 0, v_a_1416_);
v___x_1420_ = v___x_1212_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1416_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_indent_1209_);
lean_ctor_set(v_reuseFailAlloc_1430_, 2, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1421_, 0, v_a_1417_);
lean_ctor_set(v___x_1421_, 1, v_indent_1209_);
lean_ctor_set(v___x_1421_, 2, v_activeTags_1210_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1421_);
v___x_1423_ = v___x_1206_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_tail_1204_);
v___x_1423_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1425_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 1, v___x_1423_);
lean_ctor_set(v___x_1200_, 0, v___x_1420_);
v___x_1425_ = v___x_1200_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1426_; 
v___x_1426_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1202_, v_flb_1203_, v_tail_1198_, v___x_1425_);
v_x_1189_ = v___x_1426_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_1431_; uint8_t v_behavior_1432_; uint8_t v___x_1433_; 
lean_del_object(v___x_1200_);
v_a_1431_ = lean_ctor_get(v_f_1208_, 0);
lean_inc(v_a_1431_);
v_behavior_1432_ = lean_ctor_get_uint8(v_f_1208_, sizeof(void*)*1);
lean_dec_ref_known(v_f_1208_, 1);
v___x_1433_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1202_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1435_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v_a_1431_);
v___x_1435_ = v___x_1212_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1431_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_indent_1209_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_activeTags_1210_);
v___x_1435_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = lean_box(0);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v___x_1436_);
lean_ctor_set(v___x_1206_, 0, v___x_1435_);
v___x_1438_ = v___x_1206_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v_fst_1441_; lean_object* v_snd_1442_; 
v___x_1439_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1202_, v_flb_1203_, v_tail_1198_, v_tail_1204_);
v___x_1440_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_behavior_1432_, v___x_1438_, v___x_1439_, v_w_1188_, v___y_1190_);
v_fst_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_fst_1441_);
v_snd_1442_ = lean_ctor_get(v___x_1440_, 1);
lean_inc(v_snd_1442_);
lean_dec_ref(v___x_1440_);
v_x_1189_ = v_fst_1441_;
v___y_1190_ = v_snd_1442_;
goto _start;
}
}
}
else
{
lean_object* v___x_1447_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v_a_1431_);
v___x_1447_ = v___x_1212_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1431_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_indent_1209_);
lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_activeTags_1210_);
v___x_1447_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1449_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1447_);
v___x_1449_ = v___x_1206_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_tail_1204_);
v___x_1449_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1450_; 
v___x_1450_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1202_, v_flb_1203_, v_tail_1198_, v___x_1449_);
v_x_1189_ = v___x_1450_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
lean_del_object(v___x_1200_);
v_a_1454_ = lean_ctor_get(v_f_1208_, 1);
lean_inc(v_a_1454_);
lean_dec_ref_known(v_f_1208_, 2);
v___x_1455_ = lean_unsigned_to_nat(1u);
v___x_1456_ = lean_nat_add(v_activeTags_1210_, v___x_1455_);
lean_dec(v_activeTags_1210_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 2, v___x_1456_);
lean_ctor_set(v___x_1212_, 0, v_a_1454_);
v___x_1458_ = v___x_1212_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1454_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_indent_1209_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1460_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1458_);
v___x_1460_ = v___x_1206_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_tail_1204_);
v___x_1460_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1461_; 
v___x_1461_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1202_, v_flb_1203_, v_tail_1198_, v___x_1460_);
v_x_1189_ = v___x_1461_;
goto _start;
}
}
}
}
v___jp_1214_:
{
lean_object* v_out_1215_; lean_object* v_column_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1245_; 
v_out_1215_ = lean_ctor_get(v___y_1190_, 0);
v_column_1216_ = lean_ctor_get(v___y_1190_, 1);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___y_1190_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1218_ = v___y_1190_;
v_isShared_1219_ = v_isSharedCheck_1245_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_column_1216_);
lean_inc(v_out_1215_);
lean_dec(v___y_1190_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1245_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; uint8_t v___x_1221_; 
lean_inc(v_column_1216_);
v___x_1220_ = lean_nat_to_int(v_column_1216_);
v___x_1221_ = lean_int_dec_lt(v___x_1220_, v_indent_1209_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; lean_object* v___x_1223_; uint32_t v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
lean_dec(v___x_1220_);
lean_dec(v_column_1216_);
v___x_1222_ = l_Int_toNat(v_indent_1209_);
lean_dec(v_indent_1209_);
v___x_1223_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1224_ = 32;
lean_inc(v___x_1222_);
v___x_1225_ = lean_string_pushn(v___x_1223_, v___x_1224_, v___x_1222_);
v___x_1226_ = lean_string_append(v_out_1215_, v___x_1225_);
lean_dec_ref(v___x_1225_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 1, v___x_1222_);
lean_ctor_set(v___x_1218_, 0, v___x_1226_);
v___x_1228_ = v___x_1218_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v___x_1222_);
v___x_1228_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1229_; 
v___x_1229_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1202_, v_flb_1203_, v_tail_1198_, v_tail_1204_);
v_x_1189_ = v___x_1229_;
v___y_1190_ = v___x_1228_;
goto _start;
}
}
else
{
lean_object* v___x_1232_; uint32_t v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1232_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_1233_ = 32;
v___x_1234_ = lean_int_sub(v_indent_1209_, v___x_1220_);
lean_dec(v___x_1220_);
lean_dec(v_indent_1209_);
v___x_1235_ = l_Int_toNat(v___x_1234_);
lean_dec(v___x_1234_);
v___x_1236_ = lean_string_pushn(v___x_1232_, v___x_1233_, v___x_1235_);
v___x_1237_ = lean_string_append(v_out_1215_, v___x_1236_);
v___x_1238_ = lean_string_length(v___x_1236_);
lean_dec_ref(v___x_1236_);
v___x_1239_ = lean_nat_add(v_column_1216_, v___x_1238_);
lean_dec(v___x_1238_);
lean_dec(v_column_1216_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 1, v___x_1239_);
lean_ctor_set(v___x_1218_, 0, v___x_1237_);
v___x_1241_ = v___x_1218_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1242_; 
v___x_1242_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1202_, v_flb_1203_, v_tail_1198_, v_tail_1204_);
v_x_1189_ = v___x_1242_;
v___y_1190_ = v___x_1241_;
goto _start;
}
}
}
}
v___jp_1246_:
{
if (v___y_1247_ == 0)
{
goto v___jp_1214_;
}
else
{
lean_object* v___x_1248_; 
lean_dec(v_indent_1209_);
v___x_1248_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1202_, v_flb_1203_, v_tail_1198_, v_tail_1204_);
v_x_1189_ = v___x_1248_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0___boxed(lean_object* v_w_1470_, lean_object* v_x_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_1470_, v_x_1471_, v___y_1472_);
lean_dec(v_w_1470_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(lean_object* v_f_1474_, lean_object* v_w_1475_, lean_object* v_indent_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1478_; uint8_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1478_ = lean_box(1);
v___x_1479_ = 0;
v___x_1480_ = lean_nat_to_int(v_indent_1476_);
v___x_1481_ = lean_unsigned_to_nat(0u);
v___x_1482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1482_, 0, v_f_1474_);
lean_ctor_set(v___x_1482_, 1, v___x_1480_);
lean_ctor_set(v___x_1482_, 2, v___x_1481_);
v___x_1483_ = lean_box(0);
v___x_1484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1482_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1485_, 0, v___x_1478_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*2, v___x_1479_);
v___x_1486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
lean_ctor_set(v___x_1486_, 1, v___x_1483_);
v___x_1487_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_1475_, v___x_1486_, v___y_1477_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0___boxed(lean_object* v_f_1488_, lean_object* v_w_1489_, lean_object* v_indent_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(v_f_1488_, v_w_1489_, v_indent_1490_, v___y_1491_);
lean_dec(v_w_1489_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty(lean_object* v_f_1493_, lean_object* v_width_1494_, lean_object* v_indent_1495_, lean_object* v_column_1496_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v_snd_1500_; lean_object* v_out_1501_; 
v___x_1497_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
lean_ctor_set(v___x_1498_, 1, v_column_1496_);
v___x_1499_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(v_f_1493_, v_width_1494_, v_indent_1495_, v___x_1498_);
v_snd_1500_ = lean_ctor_get(v___x_1499_, 1);
lean_inc(v_snd_1500_);
lean_dec_ref(v___x_1499_);
v_out_1501_ = lean_ctor_get(v_snd_1500_, 0);
lean_inc_ref(v_out_1501_);
lean_dec(v_snd_1500_);
return v_out_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty___boxed(lean_object* v_f_1502_, lean_object* v_width_1503_, lean_object* v_indent_1504_, lean_object* v_column_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Std_Format_pretty(v_f_1502_, v_width_1503_, v_indent_1504_, v_column_1505_);
lean_dec(v_width_1503_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0(lean_object* v_f_1507_){
_start:
{
lean_inc(v_f_1507_);
return v_f_1507_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object* v_f_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Std_instToFormatFormat___lam__0(v_f_1508_);
lean_dec(v_f_1508_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatString___lam__0(lean_object* v_s_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1513_, 0, v_s_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg___lam__0(lean_object* v_x_1516_, lean_object* v_inst_1517_, lean_object* v_x1_1518_, lean_object* v_x2_1519_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1520_, 0, v_x1_1518_);
lean_ctor_set(v___x_1520_, 1, v_x_1516_);
v___x_1521_ = lean_apply_1(v_inst_1517_, v_x2_1519_);
v___x_1522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1520_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg(lean_object* v_inst_1523_, lean_object* v_x_1524_, lean_object* v_x_1525_){
_start:
{
if (lean_obj_tag(v_x_1524_) == 0)
{
lean_object* v___x_1526_; 
lean_dec(v_x_1525_);
lean_dec_ref(v_inst_1523_);
v___x_1526_ = lean_box(0);
return v___x_1526_;
}
else
{
lean_object* v_tail_1527_; 
v_tail_1527_ = lean_ctor_get(v_x_1524_, 1);
if (lean_obj_tag(v_tail_1527_) == 0)
{
lean_object* v_head_1528_; lean_object* v___x_1529_; 
lean_dec(v_x_1525_);
v_head_1528_ = lean_ctor_get(v_x_1524_, 0);
lean_inc(v_head_1528_);
lean_dec_ref_known(v_x_1524_, 2);
v___x_1529_ = lean_apply_1(v_inst_1523_, v_head_1528_);
return v___x_1529_;
}
else
{
lean_object* v_head_1530_; lean_object* v___f_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_inc(v_tail_1527_);
v_head_1530_ = lean_ctor_get(v_x_1524_, 0);
lean_inc(v_head_1530_);
lean_dec_ref_known(v_x_1524_, 2);
lean_inc_ref(v_inst_1523_);
v___f_1531_ = lean_alloc_closure((void*)(l_Std_Format_joinSep___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1531_, 0, v_x_1525_);
lean_closure_set(v___f_1531_, 1, v_inst_1523_);
v___x_1532_ = lean_apply_1(v_inst_1523_, v_head_1530_);
v___x_1533_ = l_List_foldl___redArg(v___f_1531_, v___x_1532_, v_tail_1527_);
return v___x_1533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep(lean_object* v_00_u03b1_1534_, lean_object* v_inst_1535_, lean_object* v_x_1536_, lean_object* v_x_1537_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Std_Format_joinSep___redArg(v_inst_1535_, v_x_1536_, v_x_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg___lam__0(lean_object* v_pre_1539_, lean_object* v_inst_1540_, lean_object* v_x1_1541_, lean_object* v_x2_1542_){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1543_, 0, v_x1_1541_);
lean_ctor_set(v___x_1543_, 1, v_pre_1539_);
v___x_1544_ = lean_apply_1(v_inst_1540_, v_x2_1542_);
v___x_1545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg(lean_object* v_inst_1546_, lean_object* v_pre_1547_, lean_object* v_x_1548_){
_start:
{
if (lean_obj_tag(v_x_1548_) == 0)
{
lean_object* v___x_1549_; 
lean_dec(v_pre_1547_);
lean_dec_ref(v_inst_1546_);
v___x_1549_ = lean_box(0);
return v___x_1549_;
}
else
{
lean_object* v_head_1550_; lean_object* v_tail_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1561_; 
v_head_1550_ = lean_ctor_get(v_x_1548_, 0);
v_tail_1551_ = lean_ctor_get(v_x_1548_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_x_1548_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1553_ = v_x_1548_;
v_isShared_1554_ = v_isSharedCheck_1561_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_tail_1551_);
lean_inc(v_head_1550_);
lean_dec(v_x_1548_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1561_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___f_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
lean_inc_ref(v_inst_1546_);
lean_inc(v_pre_1547_);
v___f_1555_ = lean_alloc_closure((void*)(l_Std_Format_prefixJoin___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1555_, 0, v_pre_1547_);
lean_closure_set(v___f_1555_, 1, v_inst_1546_);
v___x_1556_ = lean_apply_1(v_inst_1546_, v_head_1550_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set_tag(v___x_1553_, 5);
lean_ctor_set(v___x_1553_, 1, v___x_1556_);
lean_ctor_set(v___x_1553_, 0, v_pre_1547_);
v___x_1558_ = v___x_1553_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_pre_1547_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_List_foldl___redArg(v___f_1555_, v___x_1558_, v_tail_1551_);
return v___x_1559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin(lean_object* v_00_u03b1_1562_, lean_object* v_inst_1563_, lean_object* v_pre_1564_, lean_object* v_x_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Std_Format_prefixJoin___redArg(v_inst_1563_, v_pre_1564_, v_x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg___lam__0(lean_object* v_inst_1567_, lean_object* v_x_1568_, lean_object* v_x1_1569_, lean_object* v_x2_1570_){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = lean_apply_1(v_inst_1567_, v_x2_1570_);
v___x_1572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_x1_1569_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
lean_ctor_set(v___x_1573_, 1, v_x_1568_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg(lean_object* v_inst_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_){
_start:
{
if (lean_obj_tag(v_x_1575_) == 0)
{
lean_object* v___x_1577_; 
lean_dec(v_x_1576_);
lean_dec_ref(v_inst_1574_);
v___x_1577_ = lean_box(0);
return v___x_1577_;
}
else
{
lean_object* v_head_1578_; lean_object* v_tail_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1589_; 
v_head_1578_ = lean_ctor_get(v_x_1575_, 0);
v_tail_1579_ = lean_ctor_get(v_x_1575_, 1);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_x_1575_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1581_ = v_x_1575_;
v_isShared_1582_ = v_isSharedCheck_1589_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_tail_1579_);
lean_inc(v_head_1578_);
lean_dec(v_x_1575_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1589_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___f_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; 
lean_inc(v_x_1576_);
lean_inc_ref(v_inst_1574_);
v___f_1583_ = lean_alloc_closure((void*)(l_Std_Format_joinSuffix___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1583_, 0, v_inst_1574_);
lean_closure_set(v___f_1583_, 1, v_x_1576_);
v___x_1584_ = lean_apply_1(v_inst_1574_, v_head_1578_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set_tag(v___x_1581_, 5);
lean_ctor_set(v___x_1581_, 1, v_x_1576_);
lean_ctor_set(v___x_1581_, 0, v___x_1584_);
v___x_1586_ = v___x_1581_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_x_1576_);
v___x_1586_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_List_foldl___redArg(v___f_1583_, v___x_1586_, v_tail_1579_);
return v___x_1587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix(lean_object* v_00_u03b1_1590_, lean_object* v_inst_1591_, lean_object* v_x_1592_, lean_object* v_x_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Std_Format_joinSuffix___redArg(v_inst_1591_, v_x_1592_, v_x_1593_);
return v___x_1594_;
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
