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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Format_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_Format_FlattenBehavior_ctorIdx___impl(v_x_4__boxed_5_);
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
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_52_ = lean_box(v_x_50_);
v___x_53_ = lean_obj_tag_nat(v___x_52_);
lean_dec(v___x_52_);
v___x_54_ = lean_box(v_y_51_);
v___x_55_ = lean_obj_tag_nat(v___x_54_);
lean_dec(v___x_54_);
v___x_56_ = lean_nat_dec_eq(v___x_53_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_instBEqFlattenBehavior_beq___boxed(lean_object* v_x_57_, lean_object* v_y_58_){
_start:
{
uint8_t v_x_24__boxed_59_; uint8_t v_y_25__boxed_60_; uint8_t v_res_61_; lean_object* v_r_62_; 
v_x_24__boxed_59_ = lean_unbox(v_x_57_);
v_y_25__boxed_60_ = lean_unbox(v_y_58_);
v_res_61_ = l_Std_Format_instBEqFlattenBehavior_beq(v_x_24__boxed_59_, v_y_25__boxed_60_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorIdx___impl(lean_object* v_x_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_obj_tag_nat(v_x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorIdx___impl___boxed(lean_object* v_x_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Std_Format_ctorIdx___impl(v_x_67_);
lean_dec(v_x_67_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorElim___redArg(lean_object* v_t_69_, lean_object* v_k_70_){
_start:
{
switch(lean_obj_tag(v_t_69_))
{
case 2:
{
uint8_t v_force_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_force_71_ = lean_ctor_get_uint8(v_t_69_, 0);
lean_dec_ref_known(v_t_69_, 0);
v___x_72_ = lean_box(v_force_71_);
v___x_73_ = lean_apply_1(v_k_70_, v___x_72_);
return v___x_73_;
}
case 3:
{
lean_object* v_a_74_; lean_object* v___x_75_; 
v_a_74_ = lean_ctor_get(v_t_69_, 0);
lean_inc_ref(v_a_74_);
lean_dec_ref_known(v_t_69_, 1);
v___x_75_ = lean_apply_1(v_k_70_, v_a_74_);
return v___x_75_;
}
case 4:
{
lean_object* v_indent_76_; lean_object* v_f_77_; lean_object* v___x_78_; 
v_indent_76_ = lean_ctor_get(v_t_69_, 0);
lean_inc(v_indent_76_);
v_f_77_ = lean_ctor_get(v_t_69_, 1);
lean_inc(v_f_77_);
lean_dec_ref_known(v_t_69_, 2);
v___x_78_ = lean_apply_2(v_k_70_, v_indent_76_, v_f_77_);
return v___x_78_;
}
case 5:
{
lean_object* v_a_79_; lean_object* v_a_80_; lean_object* v___x_81_; 
v_a_79_ = lean_ctor_get(v_t_69_, 0);
lean_inc(v_a_79_);
v_a_80_ = lean_ctor_get(v_t_69_, 1);
lean_inc(v_a_80_);
lean_dec_ref_known(v_t_69_, 2);
v___x_81_ = lean_apply_2(v_k_70_, v_a_79_, v_a_80_);
return v___x_81_;
}
case 6:
{
lean_object* v_a_82_; uint8_t v_behavior_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v_a_82_ = lean_ctor_get(v_t_69_, 0);
lean_inc(v_a_82_);
v_behavior_83_ = lean_ctor_get_uint8(v_t_69_, sizeof(void*)*1);
lean_dec_ref_known(v_t_69_, 1);
v___x_84_ = lean_box(v_behavior_83_);
v___x_85_ = lean_apply_2(v_k_70_, v_a_82_, v___x_84_);
return v___x_85_;
}
case 7:
{
lean_object* v_a_86_; lean_object* v_a_87_; lean_object* v___x_88_; 
v_a_86_ = lean_ctor_get(v_t_69_, 0);
lean_inc(v_a_86_);
v_a_87_ = lean_ctor_get(v_t_69_, 1);
lean_inc(v_a_87_);
lean_dec_ref_known(v_t_69_, 2);
v___x_88_ = lean_apply_2(v_k_70_, v_a_86_, v_a_87_);
return v___x_88_;
}
default: 
{
lean_dec(v_t_69_);
return v_k_70_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorElim(lean_object* v_motive_89_, lean_object* v_ctorIdx_90_, lean_object* v_t_91_, lean_object* v_h_92_, lean_object* v_k_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Std_Format_ctorElim___redArg(v_t_91_, v_k_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorElim___boxed(lean_object* v_motive_95_, lean_object* v_ctorIdx_96_, lean_object* v_t_97_, lean_object* v_h_98_, lean_object* v_k_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_Format_ctorElim(v_motive_95_, v_ctorIdx_96_, v_t_97_, v_h_98_, v_k_99_);
lean_dec(v_ctorIdx_96_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nil_elim___redArg(lean_object* v_t_101_, lean_object* v_nil_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Std_Format_ctorElim___redArg(v_t_101_, v_nil_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nil_elim(lean_object* v_motive_104_, lean_object* v_t_105_, lean_object* v_h_106_, lean_object* v_nil_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Std_Format_ctorElim___redArg(v_t_105_, v_nil_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_line_elim___redArg(lean_object* v_t_109_, lean_object* v_line_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Std_Format_ctorElim___redArg(v_t_109_, v_line_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_line_elim(lean_object* v_motive_112_, lean_object* v_t_113_, lean_object* v_h_114_, lean_object* v_line_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Std_Format_ctorElim___redArg(v_t_113_, v_line_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_align_elim___redArg(lean_object* v_t_117_, lean_object* v_align_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Std_Format_ctorElim___redArg(v_t_117_, v_align_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_align_elim(lean_object* v_motive_120_, lean_object* v_t_121_, lean_object* v_h_122_, lean_object* v_align_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Std_Format_ctorElim___redArg(v_t_121_, v_align_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_text_elim___redArg(lean_object* v_t_125_, lean_object* v_text_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Std_Format_ctorElim___redArg(v_t_125_, v_text_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_text_elim(lean_object* v_motive_128_, lean_object* v_t_129_, lean_object* v_h_130_, lean_object* v_text_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Std_Format_ctorElim___redArg(v_t_129_, v_text_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nest_elim___redArg(lean_object* v_t_133_, lean_object* v_nest_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Std_Format_ctorElim___redArg(v_t_133_, v_nest_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nest_elim(lean_object* v_motive_136_, lean_object* v_t_137_, lean_object* v_h_138_, lean_object* v_nest_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Std_Format_ctorElim___redArg(v_t_137_, v_nest_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_append_elim___redArg(lean_object* v_t_141_, lean_object* v_append_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Std_Format_ctorElim___redArg(v_t_141_, v_append_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_append_elim(lean_object* v_motive_144_, lean_object* v_t_145_, lean_object* v_h_146_, lean_object* v_append_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Std_Format_ctorElim___redArg(v_t_145_, v_append_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_group_elim___redArg(lean_object* v_t_149_, lean_object* v_group_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Std_Format_ctorElim___redArg(v_t_149_, v_group_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_group_elim(lean_object* v_motive_152_, lean_object* v_t_153_, lean_object* v_h_154_, lean_object* v_group_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_Format_ctorElim___redArg(v_t_153_, v_group_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_tag_elim___redArg(lean_object* v_t_157_, lean_object* v_tag_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Std_Format_ctorElim___redArg(v_t_157_, v_tag_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_tag_elim(lean_object* v_motive_160_, lean_object* v_t_161_, lean_object* v_h_162_, lean_object* v_tag_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_Format_ctorElim___redArg(v_t_161_, v_tag_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Std_instInhabitedFormat_default(void){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_box(0);
return v___x_165_;
}
}
static lean_object* _init_l_Std_instInhabitedFormat(void){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_box(0);
return v___x_166_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_isEmpty(lean_object* v_x_168_){
_start:
{
switch(lean_obj_tag(v_x_168_))
{
case 1:
{
uint8_t v___x_169_; 
v___x_169_ = 0;
return v___x_169_;
}
case 3:
{
lean_object* v_a_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v_a_170_ = lean_ctor_get(v_x_168_, 0);
v___x_171_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_172_ = lean_string_dec_eq(v_a_170_, v___x_171_);
return v___x_172_;
}
case 4:
{
lean_object* v_f_173_; 
v_f_173_ = lean_ctor_get(v_x_168_, 1);
v_x_168_ = v_f_173_;
goto _start;
}
case 5:
{
lean_object* v_a_175_; lean_object* v_a_176_; uint8_t v___x_177_; 
v_a_175_ = lean_ctor_get(v_x_168_, 0);
v_a_176_ = lean_ctor_get(v_x_168_, 1);
v___x_177_ = l_Std_Format_isEmpty(v_a_175_);
if (v___x_177_ == 0)
{
return v___x_177_;
}
else
{
v_x_168_ = v_a_176_;
goto _start;
}
}
case 6:
{
lean_object* v_a_179_; 
v_a_179_ = lean_ctor_get(v_x_168_, 0);
v_x_168_ = v_a_179_;
goto _start;
}
case 7:
{
lean_object* v_a_181_; 
v_a_181_ = lean_ctor_get(v_x_168_, 1);
v_x_168_ = v_a_181_;
goto _start;
}
default: 
{
uint8_t v___x_183_; 
v___x_183_ = 1;
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_isEmpty___boxed(lean_object* v_x_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Std_Format_isEmpty(v_x_184_);
lean_dec(v_x_184_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_fill(lean_object* v_f_187_){
_start:
{
uint8_t v___x_188_; lean_object* v___x_189_; 
v___x_188_ = 1;
v___x_189_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_189_, 0, v_f_187_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*1, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_instAppend___lam__0(lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v_a_190_);
lean_ctor_set(v___x_192_, 1, v_a_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_instCoeString___lam__0(lean_object* v_a_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_196_, 0, v_a_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_join_spec__0(lean_object* v_x_199_, lean_object* v_x_200_){
_start:
{
if (lean_obj_tag(v_x_200_) == 0)
{
return v_x_199_;
}
else
{
lean_object* v_head_201_; lean_object* v_tail_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_210_; 
v_head_201_ = lean_ctor_get(v_x_200_, 0);
v_tail_202_ = lean_ctor_get(v_x_200_, 1);
v_isSharedCheck_210_ = !lean_is_exclusive(v_x_200_);
if (v_isSharedCheck_210_ == 0)
{
v___x_204_ = v_x_200_;
v_isShared_205_ = v_isSharedCheck_210_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_tail_202_);
lean_inc(v_head_201_);
lean_dec(v_x_200_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_210_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 5);
lean_ctor_set(v___x_204_, 1, v_head_201_);
lean_ctor_set(v___x_204_, 0, v_x_199_);
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_x_199_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_head_201_);
v___x_207_ = v_reuseFailAlloc_209_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
v_x_199_ = v___x_207_;
v_x_200_ = v_tail_202_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_join(lean_object* v_xs_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = ((lean_object*)(l_Std_Format_join___closed__0));
v___x_215_ = l_List_foldl___at___00Std_Format_join_spec__0(v___x_214_, v_xs_213_);
return v___x_215_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_isNil(lean_object* v_x_216_){
_start:
{
if (lean_obj_tag(v_x_216_) == 0)
{
uint8_t v___x_217_; 
v___x_217_ = 1;
return v___x_217_;
}
else
{
uint8_t v___x_218_; 
v___x_218_ = 0;
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_isNil___boxed(lean_object* v_x_219_){
_start:
{
uint8_t v_res_220_; lean_object* v_r_221_; 
v_res_220_ = l_Std_Format_isNil(v_x_219_);
lean_dec(v_x_219_);
v_r_221_ = lean_box(v_res_220_);
return v_r_221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_merge(lean_object* v_w_227_, lean_object* v_r_u2081_228_, lean_object* v_r_u2082_229_){
_start:
{
uint8_t v_foundLine_230_; lean_object* v_space_231_; uint8_t v___x_232_; 
v_foundLine_230_ = lean_ctor_get_uint8(v_r_u2081_228_, sizeof(void*)*1);
v_space_231_ = lean_ctor_get(v_r_u2081_228_, 0);
v___x_232_ = lean_nat_dec_lt(v_w_227_, v_space_231_);
if (v___x_232_ == 0)
{
if (v_foundLine_230_ == 0)
{
lean_object* v___x_233_; lean_object* v_r_u2082_234_; uint8_t v_foundLine_235_; uint8_t v_foundFlattenedHardLine_236_; lean_object* v_space_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_245_; 
v___x_233_ = lean_nat_sub(v_w_227_, v_space_231_);
v_r_u2082_234_ = lean_apply_1(v_r_u2082_229_, v___x_233_);
v_foundLine_235_ = lean_ctor_get_uint8(v_r_u2082_234_, sizeof(void*)*1);
v_foundFlattenedHardLine_236_ = lean_ctor_get_uint8(v_r_u2082_234_, sizeof(void*)*1 + 1);
v_space_237_ = lean_ctor_get(v_r_u2082_234_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v_r_u2082_234_);
if (v_isSharedCheck_245_ == 0)
{
v___x_239_ = v_r_u2082_234_;
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_space_237_);
lean_dec(v_r_u2082_234_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_241_ = lean_nat_add(v_space_231_, v_space_237_);
lean_dec(v_space_237_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_241_);
v___x_243_ = v___x_239_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
lean_ctor_set_uint8(v_reuseFailAlloc_244_, sizeof(void*)*1, v_foundLine_235_);
lean_ctor_set_uint8(v_reuseFailAlloc_244_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_236_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
else
{
lean_dec_ref(v_r_u2082_229_);
lean_inc_ref(v_r_u2081_228_);
return v_r_u2081_228_;
}
}
else
{
lean_dec_ref(v_r_u2082_229_);
lean_inc_ref(v_r_u2081_228_);
return v_r_u2081_228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_merge___boxed(lean_object* v_w_246_, lean_object* v_r_u2081_247_, lean_object* v_r_u2082_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Init_Data_Format_Basic_0__Std_Format_merge(v_w_246_, v_r_u2081_247_, v_r_u2082_248_);
lean_dec_ref(v_r_u2081_247_);
lean_dec(v_w_246_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_spec__0(lean_object* v_a_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = lean_nat_to_int(v_a_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(lean_object* v_x_255_, uint8_t v_x_256_, lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
uint8_t v___y_260_; 
switch(lean_obj_tag(v_x_255_))
{
case 0:
{
lean_object* v___x_269_; 
lean_dec(v_x_258_);
lean_dec(v_x_257_);
v___x_269_ = ((lean_object*)(l_Std_Format_instInhabitedSpaceResult_default___closed__0));
return v___x_269_;
}
case 1:
{
lean_dec(v_x_258_);
lean_dec(v_x_257_);
if (v_x_256_ == 0)
{
uint8_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = 1;
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*1, v___x_270_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*1 + 1, v_x_256_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; 
v___x_273_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___closed__0));
return v___x_273_;
}
}
case 2:
{
if (v_x_256_ == 0)
{
lean_dec_ref_known(v_x_255_, 0);
v___y_260_ = v_x_256_;
goto v___jp_259_;
}
else
{
uint8_t v_force_274_; 
v_force_274_ = lean_ctor_get_uint8(v_x_255_, 0);
lean_dec_ref_known(v_x_255_, 0);
if (v_force_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec(v_x_258_);
lean_dec(v_x_257_);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*1, v_force_274_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*1 + 1, v_force_274_);
return v___x_276_;
}
else
{
uint8_t v___x_277_; 
v___x_277_ = 0;
v___y_260_ = v___x_277_;
goto v___jp_259_;
}
}
}
case 3:
{
lean_object* v_a_278_; uint32_t v___x_279_; lean_object* v_p_280_; lean_object* v_off_281_; uint8_t v___y_283_; lean_object* v___x_286_; uint8_t v_decide_287_; 
lean_dec(v_x_258_);
lean_dec(v_x_257_);
v_a_278_ = lean_ctor_get(v_x_255_, 0);
lean_inc_ref_n(v_a_278_, 3);
lean_dec_ref_known(v_x_255_, 1);
v___x_279_ = 10;
v_p_280_ = lean_string_posof(v_a_278_, v___x_279_);
lean_inc(v_p_280_);
v_off_281_ = lean_string_offsetofpos(v_a_278_, v_p_280_);
v___x_286_ = lean_string_utf8_byte_size(v_a_278_);
lean_dec_ref(v_a_278_);
v_decide_287_ = lean_nat_dec_eq(v_p_280_, v___x_286_);
lean_dec(v_p_280_);
if (v_decide_287_ == 0)
{
uint8_t v___x_288_; 
v___x_288_ = 1;
v___y_283_ = v___x_288_;
goto v___jp_282_;
}
else
{
uint8_t v___x_289_; 
v___x_289_ = 0;
v___y_283_ = v___x_289_;
goto v___jp_282_;
}
v___jp_282_:
{
if (v_x_256_ == 0)
{
lean_object* v___x_284_; 
v___x_284_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_284_, 0, v_off_281_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*1, v___y_283_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*1 + 1, v_x_256_);
return v___x_284_;
}
else
{
lean_object* v___x_285_; 
v___x_285_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_285_, 0, v_off_281_);
lean_ctor_set_uint8(v___x_285_, sizeof(void*)*1, v___y_283_);
lean_ctor_set_uint8(v___x_285_, sizeof(void*)*1 + 1, v___y_283_);
return v___x_285_;
}
}
}
case 4:
{
lean_object* v_indent_290_; lean_object* v_f_291_; lean_object* v___x_292_; 
v_indent_290_ = lean_ctor_get(v_x_255_, 0);
lean_inc(v_indent_290_);
v_f_291_ = lean_ctor_get(v_x_255_, 1);
lean_inc(v_f_291_);
lean_dec_ref_known(v_x_255_, 2);
v___x_292_ = lean_int_sub(v_x_257_, v_indent_290_);
lean_dec(v_indent_290_);
lean_dec(v_x_257_);
v_x_255_ = v_f_291_;
v_x_257_ = v___x_292_;
goto _start;
}
case 5:
{
lean_object* v_a_294_; lean_object* v_a_295_; lean_object* v___x_296_; uint8_t v_foundLine_297_; lean_object* v_space_298_; uint8_t v___x_299_; 
v_a_294_ = lean_ctor_get(v_x_255_, 0);
lean_inc(v_a_294_);
v_a_295_ = lean_ctor_get(v_x_255_, 1);
lean_inc(v_a_295_);
lean_dec_ref_known(v_x_255_, 2);
lean_inc(v_x_258_);
lean_inc(v_x_257_);
v___x_296_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_a_294_, v_x_256_, v_x_257_, v_x_258_);
v_foundLine_297_ = lean_ctor_get_uint8(v___x_296_, sizeof(void*)*1);
v_space_298_ = lean_ctor_get(v___x_296_, 0);
v___x_299_ = lean_nat_dec_lt(v_x_258_, v_space_298_);
if (v___x_299_ == 0)
{
if (v_foundLine_297_ == 0)
{
lean_object* v___x_300_; lean_object* v_r_u2082_301_; uint8_t v_foundLine_302_; uint8_t v_foundFlattenedHardLine_303_; lean_object* v_space_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_312_; 
lean_inc(v_space_298_);
lean_dec_ref(v___x_296_);
v___x_300_ = lean_nat_sub(v_x_258_, v_space_298_);
lean_dec(v_x_258_);
v_r_u2082_301_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_a_295_, v_x_256_, v_x_257_, v___x_300_);
v_foundLine_302_ = lean_ctor_get_uint8(v_r_u2082_301_, sizeof(void*)*1);
v_foundFlattenedHardLine_303_ = lean_ctor_get_uint8(v_r_u2082_301_, sizeof(void*)*1 + 1);
v_space_304_ = lean_ctor_get(v_r_u2082_301_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v_r_u2082_301_);
if (v_isSharedCheck_312_ == 0)
{
v___x_306_ = v_r_u2082_301_;
v_isShared_307_ = v_isSharedCheck_312_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_space_304_);
lean_dec(v_r_u2082_301_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_312_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_308_ = lean_nat_add(v_space_298_, v_space_304_);
lean_dec(v_space_304_);
lean_dec(v_space_298_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_308_);
v___x_310_ = v___x_306_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
lean_ctor_set_uint8(v_reuseFailAlloc_311_, sizeof(void*)*1, v_foundLine_302_);
lean_ctor_set_uint8(v_reuseFailAlloc_311_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_303_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
else
{
lean_dec(v_a_295_);
lean_dec(v_x_258_);
lean_dec(v_x_257_);
return v___x_296_;
}
}
else
{
lean_dec(v_a_295_);
lean_dec(v_x_258_);
lean_dec(v_x_257_);
return v___x_296_;
}
}
case 6:
{
lean_object* v_a_313_; uint8_t v___x_314_; 
v_a_313_ = lean_ctor_get(v_x_255_, 0);
lean_inc(v_a_313_);
lean_dec_ref_known(v_x_255_, 1);
v___x_314_ = 1;
v_x_255_ = v_a_313_;
v_x_256_ = v___x_314_;
goto _start;
}
default: 
{
lean_object* v_a_316_; 
v_a_316_ = lean_ctor_get(v_x_255_, 1);
lean_inc(v_a_316_);
lean_dec_ref_known(v_x_255_, 2);
v_x_255_ = v_a_316_;
goto _start;
}
}
v___jp_259_:
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = lean_nat_to_int(v_x_258_);
v___x_262_ = lean_int_dec_lt(v___x_261_, v_x_257_);
if (v___x_262_ == 0)
{
uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v___x_261_);
lean_dec(v_x_257_);
v___x_263_ = 1;
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*1, v___x_263_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*1 + 1, v___x_262_);
return v___x_265_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_int_sub(v_x_257_, v___x_261_);
lean_dec(v___x_261_);
lean_dec(v_x_257_);
v___x_267_ = l_Int_toNat(v___x_266_);
lean_dec(v___x_266_);
v___x_268_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*1, v___y_260_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*1 + 1, v___y_260_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___boxed(lean_object* v_x_318_, lean_object* v_x_319_, lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
uint8_t v_x_399__boxed_322_; lean_object* v_res_323_; 
v_x_399__boxed_322_ = lean_unbox(v_x_319_);
v_res_323_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_x_318_, v_x_399__boxed_322_, v_x_320_, v_x_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx___impl(lean_object* v_x_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lean_obj_tag_nat(v_x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx___impl___boxed(lean_object* v_x_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Std_Format_FlattenAllowability_ctorIdx___impl(v_x_326_);
lean_dec(v_x_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___redArg(lean_object* v_t_328_, lean_object* v_k_329_){
_start:
{
if (lean_obj_tag(v_t_328_) == 0)
{
uint8_t v_fits_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_fits_330_ = lean_ctor_get_uint8(v_t_328_, 0);
v___x_331_ = lean_box(v_fits_330_);
v___x_332_ = lean_apply_1(v_k_329_, v___x_331_);
return v___x_332_;
}
else
{
return v_k_329_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___redArg___boxed(lean_object* v_t_333_, lean_object* v_k_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_333_, v_k_334_);
lean_dec(v_t_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim(lean_object* v_motive_336_, lean_object* v_ctorIdx_337_, lean_object* v_t_338_, lean_object* v_h_339_, lean_object* v_k_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_338_, v_k_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___boxed(lean_object* v_motive_342_, lean_object* v_ctorIdx_343_, lean_object* v_t_344_, lean_object* v_h_345_, lean_object* v_k_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Std_Format_FlattenAllowability_ctorElim(v_motive_342_, v_ctorIdx_343_, v_t_344_, v_h_345_, v_k_346_);
lean_dec(v_t_344_);
lean_dec(v_ctorIdx_343_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___redArg(lean_object* v_t_348_, lean_object* v_allow_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_348_, v_allow_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___redArg___boxed(lean_object* v_t_351_, lean_object* v_allow_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_Format_FlattenAllowability_allow_elim___redArg(v_t_351_, v_allow_352_);
lean_dec(v_t_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim(lean_object* v_motive_354_, lean_object* v_t_355_, lean_object* v_h_356_, lean_object* v_allow_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_355_, v_allow_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___boxed(lean_object* v_motive_359_, lean_object* v_t_360_, lean_object* v_h_361_, lean_object* v_allow_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Std_Format_FlattenAllowability_allow_elim(v_motive_359_, v_t_360_, v_h_361_, v_allow_362_);
lean_dec(v_t_360_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___redArg(lean_object* v_t_364_, lean_object* v_disallow_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_364_, v_disallow_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___redArg___boxed(lean_object* v_t_367_, lean_object* v_disallow_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Std_Format_FlattenAllowability_disallow_elim___redArg(v_t_367_, v_disallow_368_);
lean_dec(v_t_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim(lean_object* v_motive_370_, lean_object* v_t_371_, lean_object* v_h_372_, lean_object* v_disallow_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_371_, v_disallow_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___boxed(lean_object* v_motive_375_, lean_object* v_t_376_, lean_object* v_h_377_, lean_object* v_disallow_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Std_Format_FlattenAllowability_disallow_elim(v_motive_375_, v_t_376_, v_h_377_, v_disallow_378_);
lean_dec(v_t_376_);
return v_res_379_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_instBEqFlattenAllowability_beq(lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_380_) == 0)
{
if (lean_obj_tag(v_x_381_) == 0)
{
uint8_t v_fits_382_; 
v_fits_382_ = lean_ctor_get_uint8(v_x_381_, 0);
if (v_fits_382_ == 0)
{
uint8_t v_fits_383_; 
v_fits_383_ = lean_ctor_get_uint8(v_x_380_, 0);
if (v_fits_383_ == 0)
{
uint8_t v___x_384_; 
v___x_384_ = 1;
return v___x_384_;
}
else
{
return v_fits_382_;
}
}
else
{
uint8_t v_fits_385_; 
v_fits_385_ = lean_ctor_get_uint8(v_x_380_, 0);
return v_fits_385_;
}
}
else
{
uint8_t v___x_386_; 
v___x_386_ = 0;
return v___x_386_;
}
}
else
{
if (lean_obj_tag(v_x_381_) == 1)
{
uint8_t v___x_387_; 
v___x_387_ = 1;
return v___x_387_;
}
else
{
uint8_t v___x_388_; 
v___x_388_ = 0;
return v___x_388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_instBEqFlattenAllowability_beq___boxed(lean_object* v_x_389_, lean_object* v_x_390_){
_start:
{
uint8_t v_res_391_; lean_object* v_r_392_; 
v_res_391_ = l_Std_Format_instBEqFlattenAllowability_beq(v_x_389_, v_x_390_);
lean_dec(v_x_390_);
lean_dec(v_x_389_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
LEAN_EXPORT uint8_t l_Std_Format_FlattenAllowability_shouldFlatten(lean_object* v_x_395_){
_start:
{
if (lean_obj_tag(v_x_395_) == 0)
{
uint8_t v_fits_396_; 
v_fits_396_ = lean_ctor_get_uint8(v_x_395_, 0);
if (v_fits_396_ == 1)
{
return v_fits_396_;
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
uint8_t v___x_398_; 
v___x_398_ = 0;
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_shouldFlatten___boxed(lean_object* v_x_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_x_399_);
lean_dec(v_x_399_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
if (lean_obj_tag(v_x_402_) == 0)
{
lean_object* v___x_405_; 
lean_dec(v_x_404_);
lean_dec(v_x_403_);
v___x_405_ = ((lean_object*)(l_Std_Format_instInhabitedSpaceResult_default___closed__0));
return v___x_405_;
}
else
{
lean_object* v_head_406_; lean_object* v_items_407_; 
v_head_406_ = lean_ctor_get(v_x_402_, 0);
lean_inc(v_head_406_);
v_items_407_ = lean_ctor_get(v_head_406_, 1);
lean_inc(v_items_407_);
if (lean_obj_tag(v_items_407_) == 0)
{
lean_object* v_tail_408_; 
lean_dec(v_head_406_);
v_tail_408_ = lean_ctor_get(v_x_402_, 1);
lean_inc(v_tail_408_);
lean_dec_ref_known(v_x_402_, 2);
v_x_402_ = v_tail_408_;
goto _start;
}
else
{
lean_object* v_head_410_; lean_object* v_tail_411_; lean_object* v_fla_412_; uint8_t v_flb_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_453_; 
v_head_410_ = lean_ctor_get(v_items_407_, 0);
lean_inc(v_head_410_);
v_tail_411_ = lean_ctor_get(v_x_402_, 1);
lean_inc(v_tail_411_);
lean_dec_ref_known(v_x_402_, 2);
v_fla_412_ = lean_ctor_get(v_head_406_, 0);
v_flb_413_ = lean_ctor_get_uint8(v_head_406_, sizeof(void*)*2);
v_isSharedCheck_453_ = !lean_is_exclusive(v_head_406_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; 
v_unused_454_ = lean_ctor_get(v_head_406_, 1);
lean_dec(v_unused_454_);
v___x_415_ = v_head_406_;
v_isShared_416_ = v_isSharedCheck_453_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_fla_412_);
lean_dec(v_head_406_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_453_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v_tail_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_451_; 
v_tail_417_ = lean_ctor_get(v_items_407_, 1);
v_isSharedCheck_451_ = !lean_is_exclusive(v_items_407_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; 
v_unused_452_ = lean_ctor_get(v_items_407_, 0);
lean_dec(v_unused_452_);
v___x_419_ = v_items_407_;
v_isShared_420_ = v_isSharedCheck_451_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_tail_417_);
lean_dec(v_items_407_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_451_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v_f_421_; lean_object* v_indent_422_; uint8_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v_foundLine_429_; lean_object* v_space_430_; uint8_t v___x_431_; 
v_f_421_ = lean_ctor_get(v_head_410_, 0);
lean_inc(v_f_421_);
v_indent_422_ = lean_ctor_get(v_head_410_, 1);
lean_inc(v_indent_422_);
lean_dec(v_head_410_);
v___x_423_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_412_);
lean_inc_n(v_x_404_, 2);
v___x_424_ = lean_nat_to_int(v_x_404_);
lean_inc(v_x_403_);
v___x_425_ = lean_nat_to_int(v_x_403_);
v___x_426_ = lean_int_add(v___x_424_, v___x_425_);
lean_dec(v___x_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_int_sub(v___x_426_, v_indent_422_);
lean_dec(v_indent_422_);
lean_dec(v___x_426_);
v___x_428_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_f_421_, v___x_423_, v___x_427_, v_x_404_);
v_foundLine_429_ = lean_ctor_get_uint8(v___x_428_, sizeof(void*)*1);
v_space_430_ = lean_ctor_get(v___x_428_, 0);
v___x_431_ = lean_nat_dec_lt(v_x_404_, v_space_430_);
if (v___x_431_ == 0)
{
if (v_foundLine_429_ == 0)
{
lean_object* v___x_433_; 
lean_inc(v_space_430_);
lean_dec_ref(v___x_428_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v_tail_417_);
v___x_433_ = v___x_415_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_fla_412_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_tail_417_);
lean_ctor_set_uint8(v_reuseFailAlloc_450_, sizeof(void*)*2, v_flb_413_);
v___x_433_ = v_reuseFailAlloc_450_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_435_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 1, v_tail_411_);
lean_ctor_set(v___x_419_, 0, v___x_433_);
v___x_435_ = v___x_419_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_tail_411_);
v___x_435_ = v_reuseFailAlloc_449_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v_r_u2082_437_; uint8_t v_foundLine_438_; uint8_t v_foundFlattenedHardLine_439_; lean_object* v_space_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_448_; 
v___x_436_ = lean_nat_sub(v_x_404_, v_space_430_);
lean_dec(v_x_404_);
v_r_u2082_437_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_435_, v_x_403_, v___x_436_);
v_foundLine_438_ = lean_ctor_get_uint8(v_r_u2082_437_, sizeof(void*)*1);
v_foundFlattenedHardLine_439_ = lean_ctor_get_uint8(v_r_u2082_437_, sizeof(void*)*1 + 1);
v_space_440_ = lean_ctor_get(v_r_u2082_437_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v_r_u2082_437_);
if (v_isSharedCheck_448_ == 0)
{
v___x_442_ = v_r_u2082_437_;
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_space_440_);
lean_dec(v_r_u2082_437_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = lean_nat_add(v_space_430_, v_space_440_);
lean_dec(v_space_440_);
lean_dec(v_space_430_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_444_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
lean_ctor_set_uint8(v_reuseFailAlloc_447_, sizeof(void*)*1, v_foundLine_438_);
lean_ctor_set_uint8(v_reuseFailAlloc_447_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_439_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
else
{
lean_del_object(v___x_419_);
lean_dec(v_tail_417_);
lean_del_object(v___x_415_);
lean_dec(v_fla_412_);
lean_dec(v_tail_411_);
lean_dec(v_x_404_);
lean_dec(v_x_403_);
return v___x_428_;
}
}
else
{
lean_del_object(v___x_419_);
lean_dec(v_tail_417_);
lean_del_object(v___x_415_);
lean_dec(v_fla_412_);
lean_dec(v_tail_411_);
lean_dec(v_x_404_);
lean_dec(v_x_403_);
return v___x_428_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(uint8_t v_flb_455_, lean_object* v_items_456_, lean_object* v_w_457_, lean_object* v_gs_458_, lean_object* v_toPure_459_, lean_object* v_k_460_){
_start:
{
uint8_t v___y_462_; uint8_t v___x_467_; uint8_t v___x_468_; lean_object* v___x_469_; lean_object* v_g_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v_r_474_; lean_object* v___y_476_; uint8_t v_foundLine_481_; lean_object* v_space_482_; uint8_t v___x_483_; 
v___x_467_ = 0;
v___x_468_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_455_, v___x_467_);
v___x_469_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_469_, 0, v___x_468_);
lean_inc(v_items_456_);
v_g_470_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_470_, 0, v___x_469_);
lean_ctor_set(v_g_470_, 1, v_items_456_);
lean_ctor_set_uint8(v_g_470_, sizeof(void*)*2, v_flb_455_);
v___x_471_ = lean_box(0);
v___x_472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_472_, 0, v_g_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = lean_nat_sub(v_w_457_, v_k_460_);
lean_inc(v___x_473_);
lean_inc(v_k_460_);
v_r_474_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_472_, v_k_460_, v___x_473_);
v_foundLine_481_ = lean_ctor_get_uint8(v_r_474_, sizeof(void*)*1);
v_space_482_ = lean_ctor_get(v_r_474_, 0);
v___x_483_ = lean_nat_dec_lt(v___x_473_, v_space_482_);
if (v___x_483_ == 0)
{
if (v_foundLine_481_ == 0)
{
lean_object* v___x_484_; lean_object* v_r_u2082_485_; uint8_t v_foundLine_486_; uint8_t v_foundFlattenedHardLine_487_; lean_object* v_space_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_496_; 
v___x_484_ = lean_nat_sub(v___x_473_, v_space_482_);
lean_inc(v_gs_458_);
v_r_u2082_485_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_458_, v_k_460_, v___x_484_);
v_foundLine_486_ = lean_ctor_get_uint8(v_r_u2082_485_, sizeof(void*)*1);
v_foundFlattenedHardLine_487_ = lean_ctor_get_uint8(v_r_u2082_485_, sizeof(void*)*1 + 1);
v_space_488_ = lean_ctor_get(v_r_u2082_485_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v_r_u2082_485_);
if (v_isSharedCheck_496_ == 0)
{
v___x_490_ = v_r_u2082_485_;
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_space_488_);
lean_dec(v_r_u2082_485_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_492_ = lean_nat_add(v_space_482_, v_space_488_);
lean_dec(v_space_488_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_492_);
v___x_494_ = v___x_490_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_495_, sizeof(void*)*1, v_foundLine_486_);
lean_ctor_set_uint8(v_reuseFailAlloc_495_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_487_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
v___y_476_ = v___x_494_;
goto v___jp_475_;
}
}
}
else
{
lean_dec(v_k_460_);
lean_inc_ref(v_r_474_);
v___y_476_ = v_r_474_;
goto v___jp_475_;
}
}
else
{
lean_dec(v_k_460_);
lean_inc_ref(v_r_474_);
v___y_476_ = v_r_474_;
goto v___jp_475_;
}
v___jp_461_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_463_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_463_, 0, v___y_462_);
v___x_464_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v_items_456_);
lean_ctor_set_uint8(v___x_464_, sizeof(void*)*2, v_flb_455_);
v___x_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v_gs_458_);
v___x_466_ = lean_apply_2(v_toPure_459_, lean_box(0), v___x_465_);
return v___x_466_;
}
v___jp_475_:
{
uint8_t v_foundFlattenedHardLine_477_; 
v_foundFlattenedHardLine_477_ = lean_ctor_get_uint8(v_r_474_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_474_);
if (v_foundFlattenedHardLine_477_ == 0)
{
lean_object* v_space_478_; uint8_t v___x_479_; 
v_space_478_ = lean_ctor_get(v___y_476_, 0);
lean_inc(v_space_478_);
lean_dec_ref(v___y_476_);
v___x_479_ = lean_nat_dec_le(v_space_478_, v___x_473_);
lean_dec(v___x_473_);
lean_dec(v_space_478_);
v___y_462_ = v___x_479_;
goto v___jp_461_;
}
else
{
uint8_t v___x_480_; 
lean_dec_ref(v___y_476_);
lean_dec(v___x_473_);
v___x_480_ = 0;
v___y_462_ = v___x_480_;
goto v___jp_461_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed(lean_object* v_flb_497_, lean_object* v_items_498_, lean_object* v_w_499_, lean_object* v_gs_500_, lean_object* v_toPure_501_, lean_object* v_k_502_){
_start:
{
uint8_t v_flb_boxed_503_; lean_object* v_res_504_; 
v_flb_boxed_503_ = lean_unbox(v_flb_497_);
v_res_504_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(v_flb_boxed_503_, v_items_498_, v_w_499_, v_gs_500_, v_toPure_501_, v_k_502_);
lean_dec(v_w_499_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(uint8_t v_flb_505_, lean_object* v_items_506_, lean_object* v_gs_507_, lean_object* v_w_508_, lean_object* v_inst_509_, lean_object* v_inst_510_){
_start:
{
lean_object* v_toApplicative_511_; lean_object* v_toBind_512_; lean_object* v_currColumn_513_; lean_object* v_toPure_514_; lean_object* v___x_515_; lean_object* v___f_516_; lean_object* v___x_517_; 
v_toApplicative_511_ = lean_ctor_get(v_inst_509_, 0);
lean_inc_ref(v_toApplicative_511_);
v_toBind_512_ = lean_ctor_get(v_inst_509_, 1);
lean_inc(v_toBind_512_);
lean_dec_ref(v_inst_509_);
v_currColumn_513_ = lean_ctor_get(v_inst_510_, 2);
lean_inc(v_currColumn_513_);
lean_dec_ref(v_inst_510_);
v_toPure_514_ = lean_ctor_get(v_toApplicative_511_, 1);
lean_inc(v_toPure_514_);
lean_dec_ref(v_toApplicative_511_);
v___x_515_ = lean_box(v_flb_505_);
v___f_516_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_516_, 0, v___x_515_);
lean_closure_set(v___f_516_, 1, v_items_506_);
lean_closure_set(v___f_516_, 2, v_w_508_);
lean_closure_set(v___f_516_, 3, v_gs_507_);
lean_closure_set(v___f_516_, 4, v_toPure_514_);
v___x_517_ = lean_apply_4(v_toBind_512_, lean_box(0), lean_box(0), v_currColumn_513_, v___f_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___boxed(lean_object* v_flb_518_, lean_object* v_items_519_, lean_object* v_gs_520_, lean_object* v_w_521_, lean_object* v_inst_522_, lean_object* v_inst_523_){
_start:
{
uint8_t v_flb_boxed_524_; lean_object* v_res_525_; 
v_flb_boxed_524_ = lean_unbox(v_flb_518_);
v_res_525_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_boxed_524_, v_items_519_, v_gs_520_, v_w_521_, v_inst_522_, v_inst_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(lean_object* v_m_526_, uint8_t v_flb_527_, lean_object* v_items_528_, lean_object* v_gs_529_, lean_object* v_w_530_, lean_object* v_inst_531_, lean_object* v_inst_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_527_, v_items_528_, v_gs_529_, v_w_530_, v_inst_531_, v_inst_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___boxed(lean_object* v_m_534_, lean_object* v_flb_535_, lean_object* v_items_536_, lean_object* v_gs_537_, lean_object* v_w_538_, lean_object* v_inst_539_, lean_object* v_inst_540_){
_start:
{
uint8_t v_flb_boxed_541_; lean_object* v_res_542_; 
v_flb_boxed_541_ = lean_unbox(v_flb_535_);
v_res_542_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(v_m_534_, v_flb_boxed_541_, v_items_536_, v_gs_537_, v_w_538_, v_inst_539_, v_inst_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(lean_object* v_fla_543_, uint8_t v_flb_544_, lean_object* v_tail_545_, lean_object* v_is_x27_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_547_, 0, v_fla_543_);
lean_ctor_set(v___x_547_, 1, v_is_x27_546_);
lean_ctor_set_uint8(v___x_547_, sizeof(void*)*2, v_flb_544_);
v___x_548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_tail_545_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed(lean_object* v_fla_549_, lean_object* v_flb_550_, lean_object* v_tail_551_, lean_object* v_is_x27_552_){
_start:
{
uint8_t v_flb_1440__boxed_553_; lean_object* v_res_554_; 
v_flb_1440__boxed_553_ = lean_unbox(v_flb_550_);
v_res_554_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_549_, v_flb_1440__boxed_553_, v_tail_551_, v_is_x27_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3(lean_object* v_endTags_555_, lean_object* v_activeTags_556_, lean_object* v_toBind_557_, lean_object* v___f_558_, lean_object* v_____r_559_){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_apply_1(v_endTags_555_, v_activeTags_556_);
v___x_561_ = lean_apply_4(v_toBind_557_, lean_box(0), lean_box(0), v___x_560_, v___f_558_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(lean_object* v_indent_562_, lean_object* v_pushNewline_563_, lean_object* v_toBind_564_, lean_object* v___f_565_, lean_object* v_____r_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = l_Int_toNat(v_indent_562_);
v___x_568_ = lean_apply_1(v_pushNewline_563_, v___x_567_);
v___x_569_ = lean_apply_4(v_toBind_564_, lean_box(0), lean_box(0), v___x_568_, v___f_565_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed(lean_object* v_indent_570_, lean_object* v_pushNewline_571_, lean_object* v_toBind_572_, lean_object* v___f_573_, lean_object* v_____r_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(v_indent_570_, v_pushNewline_571_, v_toBind_572_, v___f_573_, v_____r_574_);
lean_dec(v_indent_570_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(lean_object* v_indent_576_, lean_object* v_inst_577_, lean_object* v_toBind_578_, lean_object* v___f_579_, lean_object* v___f_580_, lean_object* v_k_581_){
_start:
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_nat_to_int(v_k_581_);
v___x_583_ = lean_int_dec_lt(v___x_582_, v_indent_576_);
if (v___x_583_ == 0)
{
lean_object* v_pushNewline_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v___x_582_);
lean_dec(v___f_580_);
v_pushNewline_584_ = lean_ctor_get(v_inst_577_, 1);
lean_inc(v_pushNewline_584_);
lean_dec_ref(v_inst_577_);
v___x_585_ = l_Int_toNat(v_indent_576_);
v___x_586_ = lean_apply_1(v_pushNewline_584_, v___x_585_);
v___x_587_ = lean_apply_4(v_toBind_578_, lean_box(0), lean_box(0), v___x_586_, v___f_579_);
return v___x_587_;
}
else
{
lean_object* v_pushOutput_588_; lean_object* v___x_589_; uint32_t v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec(v___f_579_);
v_pushOutput_588_ = lean_ctor_get(v_inst_577_, 0);
lean_inc(v_pushOutput_588_);
lean_dec_ref(v_inst_577_);
v___x_589_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_590_ = 32;
v___x_591_ = lean_int_sub(v_indent_576_, v___x_582_);
lean_dec(v___x_582_);
v___x_592_ = l_Int_toNat(v___x_591_);
lean_dec(v___x_591_);
v___x_593_ = lean_string_pushn(v___x_589_, v___x_590_, v___x_592_);
v___x_594_ = lean_apply_1(v_pushOutput_588_, v___x_593_);
v___x_595_ = lean_apply_4(v_toBind_578_, lean_box(0), lean_box(0), v___x_594_, v___f_580_);
return v___x_595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed(lean_object* v_indent_596_, lean_object* v_inst_597_, lean_object* v_toBind_598_, lean_object* v___f_599_, lean_object* v___f_600_, lean_object* v_k_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(v_indent_596_, v_inst_597_, v_toBind_598_, v___f_599_, v___f_600_, v_k_601_);
lean_dec(v_indent_596_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9(lean_object* v_inst_603_, lean_object* v_activeTags_604_, lean_object* v_toBind_605_, lean_object* v___f_606_, lean_object* v_____r_607_){
_start:
{
lean_object* v_endTags_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_endTags_608_ = lean_ctor_get(v_inst_603_, 4);
lean_inc(v_endTags_608_);
lean_dec_ref(v_inst_603_);
v___x_609_ = lean_apply_1(v_endTags_608_, v_activeTags_604_);
v___x_610_ = lean_apply_4(v_toBind_605_, lean_box(0), lean_box(0), v___x_609_, v___f_606_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1(lean_object* v_gs_x27_611_, lean_object* v_tail_612_, lean_object* v_w_613_, lean_object* v_inst_614_, lean_object* v_inst_615_, lean_object* v_____r_616_){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_apply_1(v_gs_x27_611_, v_tail_612_);
v___x_618_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_613_, v_inst_614_, v_inst_615_, v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(uint8_t v_flb_620_, lean_object* v_tail_621_, lean_object* v_tail_622_, lean_object* v_w_623_, lean_object* v_inst_624_, lean_object* v_inst_625_, lean_object* v_toBind_626_, lean_object* v_____r_627_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
lean_inc_ref(v_inst_625_);
lean_inc_ref(v_inst_624_);
lean_inc(v_w_623_);
v___x_628_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_620_, v_tail_621_, v_tail_622_, v_w_623_, v_inst_624_, v_inst_625_);
v___x_629_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_629_, 0, v_w_623_);
lean_closure_set(v___x_629_, 1, v_inst_624_);
lean_closure_set(v___x_629_, 2, v_inst_625_);
v___x_630_ = lean_apply_4(v_toBind_626_, lean_box(0), lean_box(0), v___x_628_, v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed(lean_object* v_flb_631_, lean_object* v_tail_632_, lean_object* v_tail_633_, lean_object* v_w_634_, lean_object* v_inst_635_, lean_object* v_inst_636_, lean_object* v_toBind_637_, lean_object* v_____r_638_){
_start:
{
uint8_t v_flb_1532__boxed_639_; lean_object* v_res_640_; 
v_flb_1532__boxed_639_ = lean_unbox(v_flb_631_);
v_res_640_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(v_flb_1532__boxed_639_, v_tail_632_, v_tail_633_, v_w_634_, v_inst_635_, v_inst_636_, v_toBind_637_, v_____r_638_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(lean_object* v_breakHere_642_, lean_object* v_w_643_, lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_endTags_646_, lean_object* v_activeTags_647_, lean_object* v_toBind_648_, lean_object* v_pushOutput_649_, lean_object* v___x_650_, lean_object* v___x_651_, lean_object* v_____x_652_){
_start:
{
if (lean_obj_tag(v_____x_652_) == 1)
{
lean_object* v_head_653_; lean_object* v_fla_654_; uint8_t v___x_655_; 
v_head_653_ = lean_ctor_get(v_____x_652_, 0);
v_fla_654_ = lean_ctor_get(v_head_653_, 0);
v___x_655_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_654_);
if (v___x_655_ == 0)
{
lean_dec_ref_known(v_____x_652_, 2);
lean_dec_ref(v___x_650_);
lean_dec(v_pushOutput_649_);
lean_dec(v_toBind_648_);
lean_dec(v_activeTags_647_);
lean_dec(v_endTags_646_);
lean_dec_ref(v_inst_645_);
lean_dec_ref(v_inst_644_);
lean_dec(v_w_643_);
lean_inc(v_breakHere_642_);
return v_breakHere_642_;
}
else
{
lean_object* v___f_656_; lean_object* v___f_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___f_656_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4), 5, 4);
lean_closure_set(v___f_656_, 0, v_w_643_);
lean_closure_set(v___f_656_, 1, v_inst_644_);
lean_closure_set(v___f_656_, 2, v_inst_645_);
lean_closure_set(v___f_656_, 3, v_____x_652_);
lean_inc(v_toBind_648_);
v___f_657_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_657_, 0, v_endTags_646_);
lean_closure_set(v___f_657_, 1, v_activeTags_647_);
lean_closure_set(v___f_657_, 2, v_toBind_648_);
lean_closure_set(v___f_657_, 3, v___f_656_);
v___x_658_ = lean_apply_1(v_pushOutput_649_, v___x_650_);
v___x_659_ = lean_apply_4(v_toBind_648_, lean_box(0), lean_box(0), v___x_658_, v___f_657_);
return v___x_659_;
}
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec(v_____x_652_);
lean_dec_ref(v___x_650_);
lean_dec(v_pushOutput_649_);
lean_dec(v_toBind_648_);
lean_dec(v_activeTags_647_);
lean_dec(v_endTags_646_);
lean_dec_ref(v_inst_645_);
lean_dec_ref(v_inst_644_);
lean_dec(v_w_643_);
v___x_660_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0));
v___x_661_ = l_panic___redArg(v___x_651_, v___x_660_);
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed(lean_object* v_breakHere_662_, lean_object* v_w_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_endTags_666_, lean_object* v_activeTags_667_, lean_object* v_toBind_668_, lean_object* v_pushOutput_669_, lean_object* v___x_670_, lean_object* v___x_671_, lean_object* v_____x_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(v_breakHere_662_, v_w_663_, v_inst_664_, v_inst_665_, v_endTags_666_, v_activeTags_667_, v_toBind_668_, v_pushOutput_669_, v___x_670_, v___x_671_, v_____x_672_);
lean_dec(v___x_671_);
lean_dec(v_breakHere_662_);
return v_res_673_;
}
}
static lean_object* _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_675_ = lean_string_length(v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(lean_object* v_a_676_, lean_object* v_p_677_, lean_object* v___x_678_, lean_object* v_indent_679_, lean_object* v_activeTags_680_, lean_object* v_tail_681_, lean_object* v_fla_682_, uint8_t v_flb_683_, lean_object* v_tail_684_, lean_object* v_w_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_toBind_688_, lean_object* v_gs_x27_689_, lean_object* v_____r_690_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v_is_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_691_ = lean_string_utf8_next(v_a_676_, v_p_677_);
v___x_692_ = lean_string_utf8_extract(v_a_676_, v___x_691_, v___x_678_);
lean_dec(v___x_691_);
v___x_693_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
v___x_694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v_indent_679_);
lean_ctor_set(v___x_694_, 2, v_activeTags_680_);
v_is_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_is_695_, 0, v___x_694_);
lean_ctor_set(v_is_695_, 1, v_tail_681_);
v___x_696_ = lean_box(1);
v___x_697_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_682_, v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
lean_dec_ref(v_gs_x27_689_);
lean_inc_ref(v_inst_687_);
lean_inc_ref(v_inst_686_);
lean_inc(v_w_685_);
v___x_698_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_683_, v_is_695_, v_tail_684_, v_w_685_, v_inst_686_, v_inst_687_);
v___x_699_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_699_, 0, v_w_685_);
lean_closure_set(v___x_699_, 1, v_inst_686_);
lean_closure_set(v___x_699_, 2, v_inst_687_);
v___x_700_ = lean_apply_4(v_toBind_688_, lean_box(0), lean_box(0), v___x_698_, v___x_699_);
return v___x_700_;
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; 
lean_dec(v_toBind_688_);
lean_dec(v_tail_684_);
v___x_701_ = lean_apply_1(v_gs_x27_689_, v_is_695_);
v___x_702_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_685_, v_inst_686_, v_inst_687_, v___x_701_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed(lean_object* v_a_703_, lean_object* v_p_704_, lean_object* v___x_705_, lean_object* v_indent_706_, lean_object* v_activeTags_707_, lean_object* v_tail_708_, lean_object* v_fla_709_, lean_object* v_flb_710_, lean_object* v_tail_711_, lean_object* v_w_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_toBind_715_, lean_object* v_gs_x27_716_, lean_object* v_____r_717_){
_start:
{
uint8_t v_flb_1556__boxed_718_; lean_object* v_res_719_; 
v_flb_1556__boxed_718_ = lean_unbox(v_flb_710_);
v_res_719_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(v_a_703_, v_p_704_, v___x_705_, v_indent_706_, v_activeTags_707_, v_tail_708_, v_fla_709_, v_flb_1556__boxed_718_, v_tail_711_, v_w_712_, v_inst_713_, v_inst_714_, v_toBind_715_, v_gs_x27_716_, v_____r_717_);
lean_dec(v_fla_709_);
lean_dec(v___x_705_);
lean_dec(v_p_704_);
lean_dec_ref(v_a_703_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(lean_object* v_activeTags_720_, lean_object* v_a_721_, lean_object* v_indent_722_, lean_object* v_tail_723_, lean_object* v_gs_x27_724_, lean_object* v_w_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_____r_728_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_729_ = lean_unsigned_to_nat(1u);
v___x_730_ = lean_nat_add(v_activeTags_720_, v___x_729_);
v___x_731_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_731_, 0, v_a_721_);
lean_ctor_set(v___x_731_, 1, v_indent_722_);
lean_ctor_set(v___x_731_, 2, v___x_730_);
v___x_732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v_tail_723_);
v___x_733_ = lean_apply_1(v_gs_x27_724_, v___x_732_);
v___x_734_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_725_, v_inst_726_, v_inst_727_, v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed(lean_object* v_activeTags_735_, lean_object* v_a_736_, lean_object* v_indent_737_, lean_object* v_tail_738_, lean_object* v_gs_x27_739_, lean_object* v_w_740_, lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_____r_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(v_activeTags_735_, v_a_736_, v_indent_737_, v_tail_738_, v_gs_x27_739_, v_w_740_, v_inst_741_, v_inst_742_, v_____r_743_);
lean_dec(v_activeTags_735_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(lean_object* v_w_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_x_748_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
lean_object* v_toApplicative_749_; lean_object* v_toPure_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_toApplicative_749_ = lean_ctor_get(v_inst_746_, 0);
lean_inc_ref(v_toApplicative_749_);
lean_dec_ref(v_inst_747_);
lean_dec_ref(v_inst_746_);
lean_dec(v_w_745_);
v_toPure_750_ = lean_ctor_get(v_toApplicative_749_, 1);
lean_inc(v_toPure_750_);
lean_dec_ref(v_toApplicative_749_);
v___x_751_ = lean_box(0);
v___x_752_ = lean_apply_2(v_toPure_750_, lean_box(0), v___x_751_);
return v___x_752_;
}
else
{
lean_object* v_head_753_; lean_object* v_items_754_; 
v_head_753_ = lean_ctor_get(v_x_748_, 0);
v_items_754_ = lean_ctor_get(v_head_753_, 1);
lean_inc(v_items_754_);
if (lean_obj_tag(v_items_754_) == 0)
{
lean_object* v_tail_755_; 
v_tail_755_ = lean_ctor_get(v_x_748_, 1);
lean_inc(v_tail_755_);
lean_dec_ref_known(v_x_748_, 2);
v_x_748_ = v_tail_755_;
goto _start;
}
else
{
lean_object* v_head_757_; lean_object* v_toBind_758_; lean_object* v_tail_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_904_; 
lean_inc(v_head_753_);
v_head_757_ = lean_ctor_get(v_items_754_, 0);
lean_inc(v_head_757_);
v_toBind_758_ = lean_ctor_get(v_inst_746_, 1);
v_tail_759_ = lean_ctor_get(v_x_748_, 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v_x_748_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; 
v_unused_905_ = lean_ctor_get(v_x_748_, 0);
lean_dec(v_unused_905_);
v___x_761_ = v_x_748_;
v_isShared_762_ = v_isSharedCheck_904_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_tail_759_);
lean_dec(v_x_748_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_904_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_fla_763_; uint8_t v_flb_764_; lean_object* v_tail_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_902_; 
v_fla_763_ = lean_ctor_get(v_head_753_, 0);
lean_inc(v_fla_763_);
v_flb_764_ = lean_ctor_get_uint8(v_head_753_, sizeof(void*)*2);
lean_dec(v_head_753_);
v_tail_765_ = lean_ctor_get(v_items_754_, 1);
v_isSharedCheck_902_ = !lean_is_exclusive(v_items_754_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v_items_754_, 0);
lean_dec(v_unused_903_);
v___x_767_ = v_items_754_;
v_isShared_768_ = v_isSharedCheck_902_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_tail_765_);
lean_dec(v_items_754_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_902_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v_f_769_; lean_object* v_indent_770_; lean_object* v_activeTags_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_901_; 
v_f_769_ = lean_ctor_get(v_head_757_, 0);
v_indent_770_ = lean_ctor_get(v_head_757_, 1);
v_activeTags_771_ = lean_ctor_get(v_head_757_, 2);
v_isSharedCheck_901_ = !lean_is_exclusive(v_head_757_);
if (v_isSharedCheck_901_ == 0)
{
v___x_773_ = v_head_757_;
v_isShared_774_ = v_isSharedCheck_901_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_activeTags_771_);
lean_inc(v_indent_770_);
lean_inc(v_f_769_);
lean_dec(v_head_757_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_901_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v_gs_x27_776_; 
v___x_775_ = lean_box(v_flb_764_);
lean_inc(v_tail_759_);
lean_inc(v_fla_763_);
v_gs_x27_776_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v_gs_x27_776_, 0, v_fla_763_);
lean_closure_set(v_gs_x27_776_, 1, v___x_775_);
lean_closure_set(v_gs_x27_776_, 2, v_tail_759_);
switch(lean_obj_tag(v_f_769_))
{
case 0:
{
lean_object* v_endTags_777_; lean_object* v___f_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
lean_inc(v_toBind_758_);
lean_del_object(v___x_773_);
lean_dec(v_indent_770_);
lean_del_object(v___x_767_);
lean_dec(v_fla_763_);
lean_del_object(v___x_761_);
lean_dec(v_tail_759_);
v_endTags_777_ = lean_ctor_get(v_inst_747_, 4);
lean_inc(v_endTags_777_);
v___f_778_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_778_, 0, v_gs_x27_776_);
lean_closure_set(v___f_778_, 1, v_tail_765_);
lean_closure_set(v___f_778_, 2, v_w_745_);
lean_closure_set(v___f_778_, 3, v_inst_746_);
lean_closure_set(v___f_778_, 4, v_inst_747_);
v___x_779_ = lean_apply_1(v_endTags_777_, v_activeTags_771_);
v___x_780_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_779_, v___f_778_);
return v___x_780_;
}
case 1:
{
lean_inc(v_toBind_758_);
lean_del_object(v___x_773_);
lean_del_object(v___x_767_);
lean_del_object(v___x_761_);
if (v_flb_764_ == 0)
{
uint8_t v___x_781_; 
lean_dec(v_tail_759_);
v___x_781_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_763_);
lean_dec(v_fla_763_);
if (v___x_781_ == 0)
{
lean_object* v_pushNewline_782_; lean_object* v_endTags_783_; lean_object* v___f_784_; lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_pushNewline_782_ = lean_ctor_get(v_inst_747_, 1);
lean_inc(v_pushNewline_782_);
v_endTags_783_ = lean_ctor_get(v_inst_747_, 4);
lean_inc(v_endTags_783_);
v___f_784_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_784_, 0, v_gs_x27_776_);
lean_closure_set(v___f_784_, 1, v_tail_765_);
lean_closure_set(v___f_784_, 2, v_w_745_);
lean_closure_set(v___f_784_, 3, v_inst_746_);
lean_closure_set(v___f_784_, 4, v_inst_747_);
lean_inc(v_toBind_758_);
v___f_785_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_785_, 0, v_endTags_783_);
lean_closure_set(v___f_785_, 1, v_activeTags_771_);
lean_closure_set(v___f_785_, 2, v_toBind_758_);
lean_closure_set(v___f_785_, 3, v___f_784_);
v___x_786_ = l_Int_toNat(v_indent_770_);
lean_dec(v_indent_770_);
v___x_787_ = lean_apply_1(v_pushNewline_782_, v___x_786_);
v___x_788_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_787_, v___f_785_);
return v___x_788_;
}
else
{
lean_object* v_pushOutput_789_; lean_object* v_endTags_790_; lean_object* v___f_791_; lean_object* v___f_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec(v_indent_770_);
v_pushOutput_789_ = lean_ctor_get(v_inst_747_, 0);
lean_inc(v_pushOutput_789_);
v_endTags_790_ = lean_ctor_get(v_inst_747_, 4);
lean_inc(v_endTags_790_);
v___f_791_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_791_, 0, v_gs_x27_776_);
lean_closure_set(v___f_791_, 1, v_tail_765_);
lean_closure_set(v___f_791_, 2, v_w_745_);
lean_closure_set(v___f_791_, 3, v_inst_746_);
lean_closure_set(v___f_791_, 4, v_inst_747_);
lean_inc(v_toBind_758_);
v___f_792_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_792_, 0, v_endTags_790_);
lean_closure_set(v___f_792_, 1, v_activeTags_771_);
lean_closure_set(v___f_792_, 2, v_toBind_758_);
lean_closure_set(v___f_792_, 3, v___f_791_);
v___x_793_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_794_ = lean_apply_1(v_pushOutput_789_, v___x_793_);
v___x_795_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_794_, v___f_792_);
return v___x_795_;
}
}
else
{
lean_object* v_pushOutput_796_; lean_object* v_pushNewline_797_; lean_object* v_endTags_798_; lean_object* v___x_799_; lean_object* v___f_800_; lean_object* v___f_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v_breakHere_804_; uint8_t v___x_805_; 
lean_dec_ref(v_gs_x27_776_);
v_pushOutput_796_ = lean_ctor_get(v_inst_747_, 0);
v_pushNewline_797_ = lean_ctor_get(v_inst_747_, 1);
v_endTags_798_ = lean_ctor_get(v_inst_747_, 4);
v___x_799_ = lean_box(v_flb_764_);
lean_inc_n(v_toBind_758_, 3);
lean_inc_ref(v_inst_747_);
lean_inc_ref(v_inst_746_);
lean_inc(v_w_745_);
lean_inc(v_tail_759_);
lean_inc(v_tail_765_);
v___f_800_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_800_, 0, v___x_799_);
lean_closure_set(v___f_800_, 1, v_tail_765_);
lean_closure_set(v___f_800_, 2, v_tail_759_);
lean_closure_set(v___f_800_, 3, v_w_745_);
lean_closure_set(v___f_800_, 4, v_inst_746_);
lean_closure_set(v___f_800_, 5, v_inst_747_);
lean_closure_set(v___f_800_, 6, v_toBind_758_);
lean_inc(v_activeTags_771_);
lean_inc(v_endTags_798_);
v___f_801_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_801_, 0, v_endTags_798_);
lean_closure_set(v___f_801_, 1, v_activeTags_771_);
lean_closure_set(v___f_801_, 2, v_toBind_758_);
lean_closure_set(v___f_801_, 3, v___f_800_);
v___x_802_ = l_Int_toNat(v_indent_770_);
lean_dec(v_indent_770_);
lean_inc(v_pushNewline_797_);
v___x_803_ = lean_apply_1(v_pushNewline_797_, v___x_802_);
v_breakHere_804_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_803_, v___f_801_);
v___x_805_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_763_);
lean_dec(v_fla_763_);
if (v___x_805_ == 0)
{
lean_dec(v_activeTags_771_);
lean_dec(v_tail_765_);
lean_dec(v_tail_759_);
lean_dec(v_toBind_758_);
lean_dec_ref(v_inst_747_);
lean_dec_ref(v_inst_746_);
lean_dec(v_w_745_);
return v_breakHere_804_;
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___f_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_806_ = lean_box(0);
lean_inc_ref_n(v_inst_746_, 2);
v___x_807_ = l_instInhabitedOfMonad___redArg(v_inst_746_, v___x_806_);
v___x_808_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
lean_inc(v_pushOutput_796_);
lean_inc(v_toBind_758_);
lean_inc(v_endTags_798_);
lean_inc_ref(v_inst_747_);
lean_inc(v_w_745_);
v___f_809_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed), 11, 10);
lean_closure_set(v___f_809_, 0, v_breakHere_804_);
lean_closure_set(v___f_809_, 1, v_w_745_);
lean_closure_set(v___f_809_, 2, v_inst_746_);
lean_closure_set(v___f_809_, 3, v_inst_747_);
lean_closure_set(v___f_809_, 4, v_endTags_798_);
lean_closure_set(v___f_809_, 5, v_activeTags_771_);
lean_closure_set(v___f_809_, 6, v_toBind_758_);
lean_closure_set(v___f_809_, 7, v_pushOutput_796_);
lean_closure_set(v___f_809_, 8, v___x_808_);
lean_closure_set(v___f_809_, 9, v___x_807_);
v___x_810_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_811_ = lean_nat_sub(v_w_745_, v___x_810_);
lean_dec(v_w_745_);
v___x_812_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_764_, v_tail_765_, v_tail_759_, v___x_811_, v_inst_746_, v_inst_747_);
v___x_813_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_812_, v___f_809_);
return v___x_813_;
}
}
}
case 2:
{
uint8_t v_force_814_; lean_object* v___f_815_; lean_object* v___f_816_; lean_object* v___f_817_; uint8_t v___y_822_; uint8_t v___x_826_; 
lean_inc_n(v_toBind_758_, 3);
lean_del_object(v___x_773_);
lean_del_object(v___x_767_);
lean_del_object(v___x_761_);
lean_dec(v_tail_759_);
v_force_814_ = lean_ctor_get_uint8(v_f_769_, 0);
lean_dec_ref_known(v_f_769_, 0);
lean_inc_ref_n(v_inst_747_, 3);
v___f_815_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_815_, 0, v_gs_x27_776_);
lean_closure_set(v___f_815_, 1, v_tail_765_);
lean_closure_set(v___f_815_, 2, v_w_745_);
lean_closure_set(v___f_815_, 3, v_inst_746_);
lean_closure_set(v___f_815_, 4, v_inst_747_);
lean_inc_ref(v___f_815_);
lean_inc(v_activeTags_771_);
v___f_816_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9), 5, 4);
lean_closure_set(v___f_816_, 0, v_inst_747_);
lean_closure_set(v___f_816_, 1, v_activeTags_771_);
lean_closure_set(v___f_816_, 2, v_toBind_758_);
lean_closure_set(v___f_816_, 3, v___f_815_);
lean_inc_ref(v___f_816_);
v___f_817_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_817_, 0, v_indent_770_);
lean_closure_set(v___f_817_, 1, v_inst_747_);
lean_closure_set(v___f_817_, 2, v_toBind_758_);
lean_closure_set(v___f_817_, 3, v___f_816_);
lean_closure_set(v___f_817_, 4, v___f_816_);
v___x_826_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_763_);
lean_dec(v_fla_763_);
if (v___x_826_ == 0)
{
v___y_822_ = v___x_826_;
goto v___jp_821_;
}
else
{
if (v_force_814_ == 0)
{
v___y_822_ = v___x_826_;
goto v___jp_821_;
}
else
{
lean_dec_ref(v___f_815_);
lean_dec(v_activeTags_771_);
goto v___jp_818_;
}
}
v___jp_818_:
{
lean_object* v_currColumn_819_; lean_object* v___x_820_; 
v_currColumn_819_ = lean_ctor_get(v_inst_747_, 2);
lean_inc(v_currColumn_819_);
lean_dec_ref(v_inst_747_);
v___x_820_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v_currColumn_819_, v___f_817_);
return v___x_820_;
}
v___jp_821_:
{
if (v___y_822_ == 0)
{
lean_dec_ref(v___f_815_);
lean_dec(v_activeTags_771_);
goto v___jp_818_;
}
else
{
lean_object* v_endTags_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec_ref(v___f_817_);
v_endTags_823_ = lean_ctor_get(v_inst_747_, 4);
lean_inc(v_endTags_823_);
lean_dec_ref(v_inst_747_);
v___x_824_ = lean_apply_1(v_endTags_823_, v_activeTags_771_);
v___x_825_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_824_, v___f_815_);
return v___x_825_;
}
}
}
case 3:
{
lean_object* v_a_827_; uint32_t v___x_828_; lean_object* v_p_829_; lean_object* v___x_830_; uint8_t v_decide_831_; 
lean_inc(v_toBind_758_);
lean_del_object(v___x_773_);
lean_del_object(v___x_767_);
lean_del_object(v___x_761_);
v_a_827_ = lean_ctor_get(v_f_769_, 0);
lean_inc_ref_n(v_a_827_, 2);
lean_dec_ref_known(v_f_769_, 1);
v___x_828_ = 10;
v_p_829_ = lean_string_posof(v_a_827_, v___x_828_);
v___x_830_ = lean_string_utf8_byte_size(v_a_827_);
v_decide_831_ = lean_nat_dec_eq(v_p_829_, v___x_830_);
if (v_decide_831_ == 0)
{
lean_object* v_pushOutput_832_; lean_object* v_pushNewline_833_; lean_object* v___x_834_; lean_object* v___f_835_; lean_object* v___f_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_pushOutput_832_ = lean_ctor_get(v_inst_747_, 0);
lean_inc(v_pushOutput_832_);
v_pushNewline_833_ = lean_ctor_get(v_inst_747_, 1);
lean_inc(v_pushNewline_833_);
v___x_834_ = lean_box(v_flb_764_);
lean_inc_n(v_toBind_758_, 2);
lean_inc(v_indent_770_);
lean_inc(v_p_829_);
lean_inc_ref(v_a_827_);
v___f_835_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed), 15, 14);
lean_closure_set(v___f_835_, 0, v_a_827_);
lean_closure_set(v___f_835_, 1, v_p_829_);
lean_closure_set(v___f_835_, 2, v___x_830_);
lean_closure_set(v___f_835_, 3, v_indent_770_);
lean_closure_set(v___f_835_, 4, v_activeTags_771_);
lean_closure_set(v___f_835_, 5, v_tail_765_);
lean_closure_set(v___f_835_, 6, v_fla_763_);
lean_closure_set(v___f_835_, 7, v___x_834_);
lean_closure_set(v___f_835_, 8, v_tail_759_);
lean_closure_set(v___f_835_, 9, v_w_745_);
lean_closure_set(v___f_835_, 10, v_inst_746_);
lean_closure_set(v___f_835_, 11, v_inst_747_);
lean_closure_set(v___f_835_, 12, v_toBind_758_);
lean_closure_set(v___f_835_, 13, v_gs_x27_776_);
v___f_836_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_836_, 0, v_indent_770_);
lean_closure_set(v___f_836_, 1, v_pushNewline_833_);
lean_closure_set(v___f_836_, 2, v_toBind_758_);
lean_closure_set(v___f_836_, 3, v___f_835_);
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = lean_string_utf8_extract(v_a_827_, v___x_837_, v_p_829_);
lean_dec(v_p_829_);
lean_dec_ref(v_a_827_);
v___x_839_ = lean_apply_1(v_pushOutput_832_, v___x_838_);
v___x_840_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_839_, v___f_836_);
return v___x_840_;
}
else
{
lean_object* v_pushOutput_841_; lean_object* v_endTags_842_; lean_object* v___f_843_; lean_object* v___f_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
lean_dec(v_p_829_);
lean_dec(v_indent_770_);
lean_dec(v_fla_763_);
lean_dec(v_tail_759_);
v_pushOutput_841_ = lean_ctor_get(v_inst_747_, 0);
lean_inc(v_pushOutput_841_);
v_endTags_842_ = lean_ctor_get(v_inst_747_, 4);
lean_inc(v_endTags_842_);
v___f_843_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_843_, 0, v_gs_x27_776_);
lean_closure_set(v___f_843_, 1, v_tail_765_);
lean_closure_set(v___f_843_, 2, v_w_745_);
lean_closure_set(v___f_843_, 3, v_inst_746_);
lean_closure_set(v___f_843_, 4, v_inst_747_);
lean_inc(v_toBind_758_);
v___f_844_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_844_, 0, v_endTags_842_);
lean_closure_set(v___f_844_, 1, v_activeTags_771_);
lean_closure_set(v___f_844_, 2, v_toBind_758_);
lean_closure_set(v___f_844_, 3, v___f_843_);
v___x_845_ = lean_apply_1(v_pushOutput_841_, v_a_827_);
v___x_846_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_845_, v___f_844_);
return v___x_846_;
}
}
case 4:
{
lean_object* v_indent_847_; lean_object* v_f_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
lean_dec_ref(v_gs_x27_776_);
lean_del_object(v___x_761_);
v_indent_847_ = lean_ctor_get(v_f_769_, 0);
lean_inc(v_indent_847_);
v_f_848_ = lean_ctor_get(v_f_769_, 1);
lean_inc(v_f_848_);
lean_dec_ref_known(v_f_769_, 2);
v___x_849_ = lean_int_add(v_indent_770_, v_indent_847_);
lean_dec(v_indent_847_);
lean_dec(v_indent_770_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_849_);
lean_ctor_set(v___x_773_, 0, v_f_848_);
v___x_851_ = v___x_773_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_f_848_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v_activeTags_771_);
v___x_851_ = v_reuseFailAlloc_857_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_853_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_851_);
v___x_853_ = v___x_767_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_tail_765_);
v___x_853_ = v_reuseFailAlloc_856_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; 
v___x_854_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_763_, v_flb_764_, v_tail_759_, v___x_853_);
v_x_748_ = v___x_854_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_858_; lean_object* v_a_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
lean_dec_ref(v_gs_x27_776_);
v_a_858_ = lean_ctor_get(v_f_769_, 0);
lean_inc(v_a_858_);
v_a_859_ = lean_ctor_get(v_f_769_, 1);
lean_inc(v_a_859_);
lean_dec_ref_known(v_f_769_, 2);
v___x_860_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_770_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 2, v___x_860_);
lean_ctor_set(v___x_773_, 0, v_a_858_);
v___x_862_ = v___x_773_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_858_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_indent_770_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v___x_860_);
v___x_862_ = v_reuseFailAlloc_872_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_863_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_863_, 0, v_a_859_);
lean_ctor_set(v___x_863_, 1, v_indent_770_);
lean_ctor_set(v___x_863_, 2, v_activeTags_771_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_863_);
v___x_865_ = v___x_767_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_tail_765_);
v___x_865_ = v_reuseFailAlloc_871_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_867_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v___x_865_);
lean_ctor_set(v___x_761_, 0, v___x_862_);
v___x_867_ = v___x_761_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v___x_865_);
v___x_867_ = v_reuseFailAlloc_870_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; 
v___x_868_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_763_, v_flb_764_, v_tail_759_, v___x_867_);
v_x_748_ = v___x_868_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_873_; uint8_t v_behavior_874_; uint8_t v___x_875_; 
lean_dec_ref(v_gs_x27_776_);
lean_del_object(v___x_761_);
v_a_873_ = lean_ctor_get(v_f_769_, 0);
lean_inc(v_a_873_);
v_behavior_874_ = lean_ctor_get_uint8(v_f_769_, sizeof(void*)*1);
lean_dec_ref_known(v_f_769_, 1);
v___x_875_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_763_);
if (v___x_875_ == 0)
{
lean_object* v___x_877_; 
lean_inc(v_toBind_758_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v_a_873_);
v___x_877_ = v___x_773_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_873_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_indent_770_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_activeTags_771_);
v___x_877_ = v_reuseFailAlloc_886_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_878_ = lean_box(0);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v___x_878_);
lean_ctor_set(v___x_767_, 0, v___x_877_);
v___x_880_ = v___x_767_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_878_);
v___x_880_ = v_reuseFailAlloc_885_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_881_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_763_, v_flb_764_, v_tail_759_, v_tail_765_);
lean_inc_ref(v_inst_747_);
lean_inc_ref(v_inst_746_);
lean_inc(v_w_745_);
v___x_882_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_behavior_874_, v___x_880_, v___x_881_, v_w_745_, v_inst_746_, v_inst_747_);
v___x_883_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_883_, 0, v_w_745_);
lean_closure_set(v___x_883_, 1, v_inst_746_);
lean_closure_set(v___x_883_, 2, v_inst_747_);
v___x_884_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_882_, v___x_883_);
return v___x_884_;
}
}
}
else
{
lean_object* v___x_888_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v_a_873_);
v___x_888_ = v___x_773_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_873_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_indent_770_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_activeTags_771_);
v___x_888_ = v_reuseFailAlloc_894_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_890_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_888_);
v___x_890_ = v___x_767_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_tail_765_);
v___x_890_ = v_reuseFailAlloc_893_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; 
v___x_891_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_763_, v_flb_764_, v_tail_759_, v___x_890_);
v_x_748_ = v___x_891_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_895_; lean_object* v_a_896_; lean_object* v_startTag_897_; lean_object* v___f_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
lean_inc(v_toBind_758_);
lean_del_object(v___x_773_);
lean_del_object(v___x_767_);
lean_dec(v_fla_763_);
lean_del_object(v___x_761_);
lean_dec(v_tail_759_);
v_a_895_ = lean_ctor_get(v_f_769_, 0);
lean_inc(v_a_895_);
v_a_896_ = lean_ctor_get(v_f_769_, 1);
lean_inc(v_a_896_);
lean_dec_ref_known(v_f_769_, 2);
v_startTag_897_ = lean_ctor_get(v_inst_747_, 3);
lean_inc(v_startTag_897_);
v___f_898_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed), 9, 8);
lean_closure_set(v___f_898_, 0, v_activeTags_771_);
lean_closure_set(v___f_898_, 1, v_a_896_);
lean_closure_set(v___f_898_, 2, v_indent_770_);
lean_closure_set(v___f_898_, 3, v_tail_765_);
lean_closure_set(v___f_898_, 4, v_gs_x27_776_);
lean_closure_set(v___f_898_, 5, v_w_745_);
lean_closure_set(v___f_898_, 6, v_inst_746_);
lean_closure_set(v___f_898_, 7, v_inst_747_);
v___x_899_ = lean_apply_1(v_startTag_897_, v_a_895_);
v___x_900_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_899_, v___f_898_);
return v___x_900_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4(lean_object* v_w_906_, lean_object* v_inst_907_, lean_object* v_inst_908_, lean_object* v_____x_909_, lean_object* v_____r_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_906_, v_inst_907_, v_inst_908_, v_____x_909_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be(lean_object* v_m_912_, lean_object* v_w_913_, lean_object* v_inst_914_, lean_object* v_inst_915_, lean_object* v_x_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_913_, v_inst_914_, v_inst_915_, v_x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___redArg(lean_object* v_f_918_, lean_object* v_w_919_, lean_object* v_indent_920_, lean_object* v_inst_921_, lean_object* v_inst_922_){
_start:
{
lean_object* v___x_923_; uint8_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_923_ = lean_box(1);
v___x_924_ = 0;
v___x_925_ = lean_nat_to_int(v_indent_920_);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_927_, 0, v_f_918_);
lean_ctor_set(v___x_927_, 1, v___x_925_);
lean_ctor_set(v___x_927_, 2, v___x_926_);
v___x_928_ = lean_box(0);
v___x_929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_930_, 0, v___x_923_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
lean_ctor_set_uint8(v___x_930_, sizeof(void*)*2, v___x_924_);
v___x_931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set(v___x_931_, 1, v___x_928_);
v___x_932_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_919_, v_inst_921_, v_inst_922_, v___x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM(lean_object* v_m_933_, lean_object* v_f_934_, lean_object* v_w_935_, lean_object* v_indent_936_, lean_object* v_inst_937_, lean_object* v_inst_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Std_Format_prettyM___redArg(v_f_934_, v_w_935_, v_indent_936_, v_inst_937_, v_inst_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_bracket(lean_object* v_l_940_, lean_object* v_f_941_, lean_object* v_r_942_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; uint8_t v___x_950_; lean_object* v___x_951_; 
v___x_943_ = lean_string_length(v_l_940_);
v___x_944_ = lean_nat_to_int(v___x_943_);
v___x_945_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_945_, 0, v_l_940_);
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v_f_941_);
v___x_947_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_947_, 0, v_r_942_);
v___x_948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_944_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = 0;
v___x_951_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_951_, 0, v___x_949_);
lean_ctor_set_uint8(v___x_951_, sizeof(void*)*1, v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l_Std_Format_paren___closed__2(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = ((lean_object*)(l_Std_Format_paren___closed__0));
v___x_955_ = lean_string_length(v___x_954_);
return v___x_955_;
}
}
static lean_object* _init_l_Std_Format_paren___closed__3(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_obj_once(&l_Std_Format_paren___closed__2, &l_Std_Format_paren___closed__2_once, _init_l_Std_Format_paren___closed__2);
v___x_957_ = lean_nat_to_int(v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_paren(lean_object* v_f_962_){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; lean_object* v___x_970_; 
v___x_963_ = lean_obj_once(&l_Std_Format_paren___closed__3, &l_Std_Format_paren___closed__3_once, _init_l_Std_Format_paren___closed__3);
v___x_964_ = ((lean_object*)(l_Std_Format_paren___closed__4));
v___x_965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v_f_962_);
v___x_966_ = ((lean_object*)(l_Std_Format_paren___closed__5));
v___x_967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_963_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = 0;
v___x_970_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set_uint8(v___x_970_, sizeof(void*)*1, v___x_969_);
return v___x_970_;
}
}
static lean_object* _init_l_Std_Format_sbracket___closed__2(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l_Std_Format_sbracket___closed__0));
v___x_974_ = lean_string_length(v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l_Std_Format_sbracket___closed__3(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_obj_once(&l_Std_Format_sbracket___closed__2, &l_Std_Format_sbracket___closed__2_once, _init_l_Std_Format_sbracket___closed__2);
v___x_976_ = lean_nat_to_int(v___x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_sbracket(lean_object* v_f_981_){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; lean_object* v___x_989_; 
v___x_982_ = lean_obj_once(&l_Std_Format_sbracket___closed__3, &l_Std_Format_sbracket___closed__3_once, _init_l_Std_Format_sbracket___closed__3);
v___x_983_ = ((lean_object*)(l_Std_Format_sbracket___closed__4));
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v_f_981_);
v___x_985_ = ((lean_object*)(l_Std_Format_sbracket___closed__5));
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_982_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = 0;
v___x_989_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set_uint8(v___x_989_, sizeof(void*)*1, v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_bracketFill(lean_object* v_l_990_, lean_object* v_f_991_, lean_object* v_r_992_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_993_ = lean_string_length(v_l_990_);
v___x_994_ = lean_nat_to_int(v___x_993_);
v___x_995_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_995_, 0, v_l_990_);
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v_f_991_);
v___x_997_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_997_, 0, v_r_992_);
v___x_998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_994_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = l_Std_Format_fill(v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l_Std_Format_defIndent(void){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_unsigned_to_nat(2u);
return v___x_1001_;
}
}
static uint8_t _init_l_Std_Format_defUnicode(void){
_start:
{
uint8_t v___x_1002_; 
v___x_1002_ = 1;
return v___x_1002_;
}
}
static lean_object* _init_l_Std_Format_defWidth(void){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_unsigned_to_nat(120u);
return v___x_1003_;
}
}
static lean_object* _init_l_Std_Format_nestD___closed__0(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_unsigned_to_nat(2u);
v___x_1005_ = lean_nat_to_int(v___x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nestD(lean_object* v_f_1006_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_obj_once(&l_Std_Format_nestD___closed__0, &l_Std_Format_nestD___closed__0_once, _init_l_Std_Format_nestD___closed__0);
v___x_1008_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v_f_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_indentD(lean_object* v_f_1009_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_box(1);
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v_f_1009_);
v___x_1012_ = l_Std_Format_nestD(v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(lean_object* v_s_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_out_1015_; lean_object* v_column_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1028_; 
v_out_1015_ = lean_ctor_get(v___y_1014_, 0);
v_column_1016_ = lean_ctor_get(v___y_1014_, 1);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___y_1014_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1018_ = v___y_1014_;
v_isShared_1019_ = v_isSharedCheck_1028_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_column_1016_);
lean_inc(v_out_1015_);
lean_dec(v___y_1014_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1028_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___x_1020_ = lean_box(0);
v___x_1021_ = lean_string_append(v_out_1015_, v_s_1013_);
v___x_1022_ = lean_string_length(v_s_1013_);
v___x_1023_ = lean_nat_add(v_column_1016_, v___x_1022_);
lean_dec(v___x_1022_);
lean_dec(v_column_1016_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v___x_1023_);
lean_ctor_set(v___x_1018_, 0, v___x_1021_);
v___x_1025_ = v___x_1018_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1020_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
return v___x_1026_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0___boxed(lean_object* v_s_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(v_s_1029_, v___y_1030_);
lean_dec_ref(v_s_1029_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1(lean_object* v_indent_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_out_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1048_; 
v_out_1035_ = lean_ctor_get(v___y_1034_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___y_1034_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v___y_1034_, 1);
lean_dec(v_unused_1049_);
v___x_1037_ = v___y_1034_;
v_isShared_1038_ = v_isSharedCheck_1048_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_out_1035_);
lean_dec(v___y_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1048_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; uint32_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1039_ = lean_box(0);
v___x_1040_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1041_ = 32;
lean_inc(v_indent_1033_);
v___x_1042_ = lean_string_pushn(v___x_1040_, v___x_1041_, v_indent_1033_);
v___x_1043_ = lean_string_append(v_out_1035_, v___x_1042_);
lean_dec_ref(v___x_1042_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v_indent_1033_);
lean_ctor_set(v___x_1037_, 0, v___x_1043_);
v___x_1045_ = v___x_1037_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_indent_1033_);
v___x_1045_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1039_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
return v___x_1046_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__2(lean_object* v_____do__lift_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_column_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v_column_1052_ = lean_ctor_get(v_____do__lift_1050_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_____do__lift_1050_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; 
v_unused_1060_ = lean_ctor_get(v_____do__lift_1050_, 0);
lean_dec(v_unused_1060_);
v___x_1054_ = v_____do__lift_1050_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_column_1052_);
lean_dec(v_____do__lift_1050_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v___y_1051_);
lean_ctor_set(v___x_1054_, 0, v_column_1052_);
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_column_1052_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v___y_1051_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(lean_object* v_x_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_box(0);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v___y_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3___boxed(lean_object* v_x_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(v_x_1065_, v___y_1066_);
lean_dec(v_x_1065_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(uint8_t v_flb_1103_, lean_object* v_items_1104_, lean_object* v_gs_1105_, lean_object* v_w_1106_, lean_object* v___y_1107_){
_start:
{
uint8_t v___y_1109_; lean_object* v_column_1114_; uint8_t v___x_1115_; uint8_t v___x_1116_; lean_object* v___x_1117_; lean_object* v_g_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v_r_1122_; lean_object* v___y_1124_; uint8_t v_foundLine_1129_; lean_object* v_space_1130_; uint8_t v___x_1131_; 
v_column_1114_ = lean_ctor_get(v___y_1107_, 1);
v___x_1115_ = 0;
v___x_1116_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_1103_, v___x_1115_);
v___x_1117_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1117_, 0, v___x_1116_);
lean_inc(v_items_1104_);
v_g_1118_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_1118_, 0, v___x_1117_);
lean_ctor_set(v_g_1118_, 1, v_items_1104_);
lean_ctor_set_uint8(v_g_1118_, sizeof(void*)*2, v_flb_1103_);
v___x_1119_ = lean_box(0);
v___x_1120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1120_, 0, v_g_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = lean_nat_sub(v_w_1106_, v_column_1114_);
lean_inc(v___x_1121_);
lean_inc(v_column_1114_);
v_r_1122_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_1120_, v_column_1114_, v___x_1121_);
v_foundLine_1129_ = lean_ctor_get_uint8(v_r_1122_, sizeof(void*)*1);
v_space_1130_ = lean_ctor_get(v_r_1122_, 0);
v___x_1131_ = lean_nat_dec_lt(v___x_1121_, v_space_1130_);
if (v___x_1131_ == 0)
{
if (v_foundLine_1129_ == 0)
{
lean_object* v___x_1132_; lean_object* v_r_u2082_1133_; uint8_t v_foundLine_1134_; uint8_t v_foundFlattenedHardLine_1135_; lean_object* v_space_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1144_; 
v___x_1132_ = lean_nat_sub(v___x_1121_, v_space_1130_);
lean_inc(v_column_1114_);
lean_inc(v_gs_1105_);
v_r_u2082_1133_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_1105_, v_column_1114_, v___x_1132_);
v_foundLine_1134_ = lean_ctor_get_uint8(v_r_u2082_1133_, sizeof(void*)*1);
v_foundFlattenedHardLine_1135_ = lean_ctor_get_uint8(v_r_u2082_1133_, sizeof(void*)*1 + 1);
v_space_1136_ = lean_ctor_get(v_r_u2082_1133_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_r_u2082_1133_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1138_ = v_r_u2082_1133_;
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_space_1136_);
lean_dec(v_r_u2082_1133_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = lean_nat_add(v_space_1130_, v_space_1136_);
lean_dec(v_space_1136_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1140_);
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1143_, sizeof(void*)*1, v_foundLine_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1143_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_1135_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
v___y_1124_ = v___x_1142_;
goto v___jp_1123_;
}
}
}
else
{
lean_inc_ref(v_r_1122_);
v___y_1124_ = v_r_1122_;
goto v___jp_1123_;
}
}
else
{
lean_inc_ref(v_r_1122_);
v___y_1124_ = v_r_1122_;
goto v___jp_1123_;
}
v___jp_1108_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1110_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1110_, 0, v___y_1109_);
v___x_1111_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v_items_1104_);
lean_ctor_set_uint8(v___x_1111_, sizeof(void*)*2, v_flb_1103_);
v___x_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
lean_ctor_set(v___x_1112_, 1, v_gs_1105_);
v___x_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set(v___x_1113_, 1, v___y_1107_);
return v___x_1113_;
}
v___jp_1123_:
{
uint8_t v_foundFlattenedHardLine_1125_; 
v_foundFlattenedHardLine_1125_ = lean_ctor_get_uint8(v_r_1122_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_1122_);
if (v_foundFlattenedHardLine_1125_ == 0)
{
lean_object* v_space_1126_; uint8_t v___x_1127_; 
v_space_1126_ = lean_ctor_get(v___y_1124_, 0);
lean_inc(v_space_1126_);
lean_dec_ref(v___y_1124_);
v___x_1127_ = lean_nat_dec_le(v_space_1126_, v___x_1121_);
lean_dec(v___x_1121_);
lean_dec(v_space_1126_);
v___y_1109_ = v___x_1127_;
goto v___jp_1108_;
}
else
{
uint8_t v___x_1128_; 
lean_dec_ref(v___y_1124_);
lean_dec(v___x_1121_);
v___x_1128_ = 0;
v___y_1109_ = v___x_1128_;
goto v___jp_1108_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1___boxed(lean_object* v_flb_1145_, lean_object* v_items_1146_, lean_object* v_gs_1147_, lean_object* v_w_1148_, lean_object* v___y_1149_){
_start:
{
uint8_t v_flb_boxed_1150_; lean_object* v_res_1151_; 
v_flb_boxed_1150_ = lean_unbox(v_flb_1145_);
v_res_1151_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_boxed_1150_, v_items_1146_, v_gs_1147_, v_w_1148_, v___y_1149_);
lean_dec(v_w_1148_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(lean_object* v_msg_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___f_1168_; lean_object* v___f_1169_; lean_object* v___f_1170_; lean_object* v___f_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_4910__overap_1180_; lean_object* v___x_1181_; 
v___f_1168_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0));
v___f_1169_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1));
v___f_1170_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2));
v___f_1171_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3));
v___x_1172_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4));
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v___f_1168_);
v___x_1174_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5));
v___x_1175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
lean_ctor_set(v___x_1175_, 2, v___f_1169_);
lean_ctor_set(v___x_1175_, 3, v___f_1170_);
lean_ctor_set(v___x_1175_, 4, v___f_1171_);
v___x_1176_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6));
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = lean_box(0);
v___x_1179_ = l_instInhabitedOfMonad___redArg(v___x_1177_, v___x_1178_);
v___x_4910__overap_1180_ = lean_panic_fn_borrowed(v___x_1179_, v_msg_1166_);
lean_dec(v___x_1179_);
v___x_1181_ = lean_apply_1(v___x_4910__overap_1180_, v___y_1167_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(lean_object* v_w_1182_, lean_object* v_x_1183_, lean_object* v___y_1184_){
_start:
{
if (lean_obj_tag(v_x_1183_) == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set(v___x_1186_, 1, v___y_1184_);
return v___x_1186_;
}
else
{
lean_object* v_head_1187_; lean_object* v_items_1188_; 
v_head_1187_ = lean_ctor_get(v_x_1183_, 0);
v_items_1188_ = lean_ctor_get(v_head_1187_, 1);
lean_inc(v_items_1188_);
if (lean_obj_tag(v_items_1188_) == 0)
{
lean_object* v_tail_1189_; 
v_tail_1189_ = lean_ctor_get(v_x_1183_, 1);
lean_inc(v_tail_1189_);
lean_dec_ref_known(v_x_1183_, 2);
v_x_1183_ = v_tail_1189_;
goto _start;
}
else
{
lean_object* v_head_1191_; lean_object* v_tail_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1462_; 
lean_inc(v_head_1187_);
v_head_1191_ = lean_ctor_get(v_items_1188_, 0);
lean_inc(v_head_1191_);
v_tail_1192_ = lean_ctor_get(v_x_1183_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_x_1183_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v_x_1183_, 0);
lean_dec(v_unused_1463_);
v___x_1194_ = v_x_1183_;
v_isShared_1195_ = v_isSharedCheck_1462_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_tail_1192_);
lean_dec(v_x_1183_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1462_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v_fla_1196_; uint8_t v_flb_1197_; lean_object* v_tail_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1460_; 
v_fla_1196_ = lean_ctor_get(v_head_1187_, 0);
lean_inc(v_fla_1196_);
v_flb_1197_ = lean_ctor_get_uint8(v_head_1187_, sizeof(void*)*2);
lean_dec(v_head_1187_);
v_tail_1198_ = lean_ctor_get(v_items_1188_, 1);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_items_1188_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; 
v_unused_1461_ = lean_ctor_get(v_items_1188_, 0);
lean_dec(v_unused_1461_);
v___x_1200_ = v_items_1188_;
v_isShared_1201_ = v_isSharedCheck_1460_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_tail_1198_);
lean_dec(v_items_1188_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1460_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v_f_1202_; lean_object* v_indent_1203_; lean_object* v_activeTags_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1459_; 
v_f_1202_ = lean_ctor_get(v_head_1191_, 0);
v_indent_1203_ = lean_ctor_get(v_head_1191_, 1);
v_activeTags_1204_ = lean_ctor_get(v_head_1191_, 2);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_head_1191_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1206_ = v_head_1191_;
v_isShared_1207_ = v_isSharedCheck_1459_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_activeTags_1204_);
lean_inc(v_indent_1203_);
lean_inc(v_f_1202_);
lean_dec(v_head_1191_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1459_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
uint8_t v___y_1241_; 
switch(lean_obj_tag(v_f_1202_))
{
case 0:
{
lean_object* v___x_1244_; 
lean_del_object(v___x_1206_);
lean_dec(v_activeTags_1204_);
lean_dec(v_indent_1203_);
lean_del_object(v___x_1200_);
lean_del_object(v___x_1194_);
v___x_1244_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1196_, v_flb_1197_, v_tail_1192_, v_tail_1198_);
v_x_1183_ = v___x_1244_;
goto _start;
}
case 1:
{
lean_del_object(v___x_1206_);
lean_dec(v_activeTags_1204_);
lean_del_object(v___x_1200_);
lean_del_object(v___x_1194_);
if (v_flb_1197_ == 0)
{
uint8_t v___x_1246_; 
v___x_1246_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1196_);
if (v___x_1246_ == 0)
{
lean_object* v_out_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1261_; 
v_out_1247_ = lean_ctor_get(v___y_1184_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___y_1184_);
if (v_isSharedCheck_1261_ == 0)
{
lean_object* v_unused_1262_; 
v_unused_1262_ = lean_ctor_get(v___y_1184_, 1);
lean_dec(v_unused_1262_);
v___x_1249_ = v___y_1184_;
v_isShared_1250_ = v_isSharedCheck_1261_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_out_1247_);
lean_dec(v___y_1184_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1261_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; uint32_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1251_ = l_Int_toNat(v_indent_1203_);
lean_dec(v_indent_1203_);
v___x_1252_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1253_ = 32;
lean_inc(v___x_1251_);
v___x_1254_ = lean_string_pushn(v___x_1252_, v___x_1253_, v___x_1251_);
v___x_1255_ = lean_string_append(v_out_1247_, v___x_1254_);
lean_dec_ref(v___x_1254_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 1, v___x_1251_);
lean_ctor_set(v___x_1249_, 0, v___x_1255_);
v___x_1257_ = v___x_1249_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___x_1251_);
v___x_1257_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1258_; 
v___x_1258_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1196_, v_flb_1197_, v_tail_1192_, v_tail_1198_);
v_x_1183_ = v___x_1258_;
v___y_1184_ = v___x_1257_;
goto _start;
}
}
}
else
{
lean_object* v_out_1263_; lean_object* v_column_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1277_; 
lean_dec(v_indent_1203_);
v_out_1263_ = lean_ctor_get(v___y_1184_, 0);
v_column_1264_ = lean_ctor_get(v___y_1184_, 1);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___y_1184_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1266_ = v___y_1184_;
v_isShared_1267_ = v_isSharedCheck_1277_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_column_1264_);
lean_inc(v_out_1263_);
lean_dec(v___y_1184_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1277_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1268_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_1269_ = lean_string_append(v_out_1263_, v___x_1268_);
v___x_1270_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_1271_ = lean_nat_add(v_column_1264_, v___x_1270_);
lean_dec(v_column_1264_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v___x_1271_);
lean_ctor_set(v___x_1266_, 0, v___x_1269_);
v___x_1273_ = v___x_1266_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; 
v___x_1274_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1196_, v_flb_1197_, v_tail_1192_, v_tail_1198_);
v_x_1183_ = v___x_1274_;
v___y_1184_ = v___x_1273_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1278_ = l_Int_toNat(v_indent_1203_);
lean_dec(v_indent_1203_);
v___x_1279_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1196_);
lean_dec(v_fla_1196_);
if (v___x_1279_ == 0)
{
lean_object* v_out_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1295_; 
v_out_1280_ = lean_ctor_get(v___y_1184_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___y_1184_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; 
v_unused_1296_ = lean_ctor_get(v___y_1184_, 1);
lean_dec(v_unused_1296_);
v___x_1282_ = v___y_1184_;
v_isShared_1283_ = v_isSharedCheck_1295_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_out_1280_);
lean_dec(v___y_1184_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1295_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; uint32_t v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1284_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1285_ = 32;
lean_inc(v___x_1278_);
v___x_1286_ = lean_string_pushn(v___x_1284_, v___x_1285_, v___x_1278_);
v___x_1287_ = lean_string_append(v_out_1280_, v___x_1286_);
lean_dec_ref(v___x_1286_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 1, v___x_1278_);
lean_ctor_set(v___x_1282_, 0, v___x_1287_);
v___x_1289_ = v___x_1282_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v___x_1278_);
v___x_1289_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1290_; lean_object* v_fst_1291_; lean_object* v_snd_1292_; 
v___x_1290_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1197_, v_tail_1198_, v_tail_1192_, v_w_1182_, v___x_1289_);
v_fst_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_fst_1291_);
v_snd_1292_ = lean_ctor_get(v___x_1290_, 1);
lean_inc(v_snd_1292_);
lean_dec_ref(v___x_1290_);
v_x_1183_ = v_fst_1291_;
v___y_1184_ = v_snd_1292_;
goto _start;
}
}
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v_fst_1301_; 
v___x_1297_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_1298_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_1299_ = lean_nat_sub(v_w_1182_, v___x_1298_);
lean_inc(v_tail_1192_);
lean_inc(v_tail_1198_);
v___x_1300_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1197_, v_tail_1198_, v_tail_1192_, v___x_1299_, v___y_1184_);
lean_dec(v___x_1299_);
v_fst_1301_ = lean_ctor_get(v___x_1300_, 0);
if (lean_obj_tag(v_fst_1301_) == 1)
{
lean_object* v_head_1302_; lean_object* v_snd_1303_; lean_object* v_fla_1304_; uint8_t v___x_1305_; 
lean_inc_ref(v_fst_1301_);
v_head_1302_ = lean_ctor_get(v_fst_1301_, 0);
v_snd_1303_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_snd_1303_);
lean_dec_ref(v___x_1300_);
v_fla_1304_ = lean_ctor_get(v_head_1302_, 0);
v___x_1305_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1304_);
if (v___x_1305_ == 0)
{
lean_object* v_out_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1321_; 
lean_dec_ref_known(v_fst_1301_, 2);
v_out_1306_ = lean_ctor_get(v_snd_1303_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_snd_1303_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; 
v_unused_1322_ = lean_ctor_get(v_snd_1303_, 1);
lean_dec(v_unused_1322_);
v___x_1308_ = v_snd_1303_;
v_isShared_1309_ = v_isSharedCheck_1321_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_out_1306_);
lean_dec(v_snd_1303_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1321_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; uint32_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1310_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1311_ = 32;
lean_inc(v___x_1278_);
v___x_1312_ = lean_string_pushn(v___x_1310_, v___x_1311_, v___x_1278_);
v___x_1313_ = lean_string_append(v_out_1306_, v___x_1312_);
lean_dec_ref(v___x_1312_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 1, v___x_1278_);
lean_ctor_set(v___x_1308_, 0, v___x_1313_);
v___x_1315_ = v___x_1308_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v___x_1278_);
v___x_1315_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; lean_object* v_fst_1317_; lean_object* v_snd_1318_; 
v___x_1316_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1197_, v_tail_1198_, v_tail_1192_, v_w_1182_, v___x_1315_);
v_fst_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_fst_1317_);
v_snd_1318_ = lean_ctor_get(v___x_1316_, 1);
lean_inc(v_snd_1318_);
lean_dec_ref(v___x_1316_);
v_x_1183_ = v_fst_1317_;
v___y_1184_ = v_snd_1318_;
goto _start;
}
}
}
else
{
lean_object* v_out_1323_; lean_object* v_column_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v___x_1278_);
lean_dec(v_tail_1198_);
lean_dec(v_tail_1192_);
v_out_1323_ = lean_ctor_get(v_snd_1303_, 0);
v_column_1324_ = lean_ctor_get(v_snd_1303_, 1);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_snd_1303_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1326_ = v_snd_1303_;
v_isShared_1327_ = v_isSharedCheck_1334_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_column_1324_);
lean_inc(v_out_1323_);
lean_dec(v_snd_1303_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1334_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1328_ = lean_string_append(v_out_1323_, v___x_1297_);
v___x_1329_ = lean_nat_add(v_column_1324_, v___x_1298_);
lean_dec(v_column_1324_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 1, v___x_1329_);
lean_ctor_set(v___x_1326_, 0, v___x_1328_);
v___x_1331_ = v___x_1326_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
v_x_1183_ = v_fst_1301_;
v___y_1184_ = v___x_1331_;
goto _start;
}
}
}
}
else
{
lean_object* v_snd_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec(v___x_1278_);
lean_dec(v_tail_1198_);
lean_dec(v_tail_1192_);
v_snd_1335_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_snd_1335_);
lean_dec_ref(v___x_1300_);
v___x_1336_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0));
v___x_1337_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(v___x_1336_, v_snd_1335_);
return v___x_1337_;
}
}
}
}
case 2:
{
uint8_t v_force_1338_; uint8_t v___x_1339_; 
lean_del_object(v___x_1206_);
lean_dec(v_activeTags_1204_);
lean_del_object(v___x_1200_);
lean_del_object(v___x_1194_);
v_force_1338_ = lean_ctor_get_uint8(v_f_1202_, 0);
lean_dec_ref_known(v_f_1202_, 0);
v___x_1339_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1196_);
if (v___x_1339_ == 0)
{
v___y_1241_ = v___x_1339_;
goto v___jp_1240_;
}
else
{
if (v_force_1338_ == 0)
{
v___y_1241_ = v___x_1339_;
goto v___jp_1240_;
}
else
{
goto v___jp_1208_;
}
}
}
case 3:
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1398_; 
lean_del_object(v___x_1194_);
v_a_1340_ = lean_ctor_get(v_f_1202_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_f_1202_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1342_ = v_f_1202_;
v_isShared_1343_ = v_isSharedCheck_1398_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v_f_1202_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1398_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
uint32_t v___x_1344_; lean_object* v_p_1345_; lean_object* v___x_1346_; uint8_t v_decide_1347_; 
v___x_1344_ = 10;
lean_inc_ref(v_a_1340_);
v_p_1345_ = lean_string_posof(v_a_1340_, v___x_1344_);
v___x_1346_ = lean_string_utf8_byte_size(v_a_1340_);
v_decide_1347_ = lean_nat_dec_eq(v_p_1345_, v___x_1346_);
if (v_decide_1347_ == 0)
{
lean_object* v_out_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1382_; 
v_out_1348_ = lean_ctor_get(v___y_1184_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___y_1184_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; 
v_unused_1383_ = lean_ctor_get(v___y_1184_, 1);
lean_dec(v_unused_1383_);
v___x_1350_ = v___y_1184_;
v_isShared_1351_ = v_isSharedCheck_1382_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_out_1348_);
lean_dec(v___y_1184_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1382_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; uint32_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1352_ = lean_unsigned_to_nat(0u);
v___x_1353_ = lean_string_utf8_extract(v_a_1340_, v___x_1352_, v_p_1345_);
v___x_1354_ = lean_string_append(v_out_1348_, v___x_1353_);
lean_dec_ref(v___x_1353_);
v___x_1355_ = l_Int_toNat(v_indent_1203_);
v___x_1356_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1357_ = 32;
lean_inc(v___x_1355_);
v___x_1358_ = lean_string_pushn(v___x_1356_, v___x_1357_, v___x_1355_);
v___x_1359_ = lean_string_append(v___x_1354_, v___x_1358_);
lean_dec_ref(v___x_1358_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v___x_1355_);
lean_ctor_set(v___x_1350_, 0, v___x_1359_);
v___x_1361_ = v___x_1350_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v___x_1355_);
v___x_1361_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1362_ = lean_string_utf8_next(v_a_1340_, v_p_1345_);
lean_dec(v_p_1345_);
v___x_1363_ = lean_string_utf8_extract(v_a_1340_, v___x_1362_, v___x_1346_);
lean_dec(v___x_1362_);
lean_dec_ref(v_a_1340_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1363_);
v___x_1365_ = v___x_1342_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1367_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1365_);
v___x_1367_ = v___x_1206_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_indent_1203_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v_activeTags_1204_);
v___x_1367_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v_is_1369_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1367_);
v_is_1369_ = v___x_1200_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_tail_1198_);
v_is_1369_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1370_ = lean_box(1);
v___x_1371_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_1196_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v_fst_1373_; lean_object* v_snd_1374_; 
lean_dec(v_fla_1196_);
v___x_1372_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1197_, v_is_1369_, v_tail_1192_, v_w_1182_, v___x_1361_);
v_fst_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_fst_1373_);
v_snd_1374_ = lean_ctor_get(v___x_1372_, 1);
lean_inc(v_snd_1374_);
lean_dec_ref(v___x_1372_);
v_x_1183_ = v_fst_1373_;
v___y_1184_ = v_snd_1374_;
goto _start;
}
else
{
lean_object* v___x_1376_; 
v___x_1376_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1196_, v_flb_1197_, v_tail_1192_, v_is_1369_);
v_x_1183_ = v___x_1376_;
v___y_1184_ = v___x_1361_;
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
lean_object* v_out_1384_; lean_object* v_column_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1397_; 
lean_dec(v_p_1345_);
lean_del_object(v___x_1342_);
lean_del_object(v___x_1206_);
lean_dec(v_activeTags_1204_);
lean_dec(v_indent_1203_);
lean_del_object(v___x_1200_);
v_out_1384_ = lean_ctor_get(v___y_1184_, 0);
v_column_1385_ = lean_ctor_get(v___y_1184_, 1);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___y_1184_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1387_ = v___y_1184_;
v_isShared_1388_ = v_isSharedCheck_1397_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_column_1385_);
lean_inc(v_out_1384_);
lean_dec(v___y_1184_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1397_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1389_ = lean_string_append(v_out_1384_, v_a_1340_);
v___x_1390_ = lean_string_length(v_a_1340_);
lean_dec_ref(v_a_1340_);
v___x_1391_ = lean_nat_add(v_column_1385_, v___x_1390_);
lean_dec(v___x_1390_);
lean_dec(v_column_1385_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 1, v___x_1391_);
lean_ctor_set(v___x_1387_, 0, v___x_1389_);
v___x_1393_ = v___x_1387_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1394_; 
v___x_1394_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1196_, v_flb_1197_, v_tail_1192_, v_tail_1198_);
v_x_1183_ = v___x_1394_;
v___y_1184_ = v___x_1393_;
goto _start;
}
}
}
}
}
case 4:
{
lean_object* v_indent_1399_; lean_object* v_f_1400_; lean_object* v___x_1401_; lean_object* v___x_1403_; 
lean_del_object(v___x_1194_);
v_indent_1399_ = lean_ctor_get(v_f_1202_, 0);
lean_inc(v_indent_1399_);
v_f_1400_ = lean_ctor_get(v_f_1202_, 1);
lean_inc(v_f_1400_);
lean_dec_ref_known(v_f_1202_, 2);
v___x_1401_ = lean_int_add(v_indent_1203_, v_indent_1399_);
lean_dec(v_indent_1399_);
lean_dec(v_indent_1203_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v___x_1401_);
lean_ctor_set(v___x_1206_, 0, v_f_1400_);
v___x_1403_ = v___x_1206_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_f_1400_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1409_, 2, v_activeTags_1204_);
v___x_1403_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1405_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1403_);
v___x_1405_ = v___x_1200_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_tail_1198_);
v___x_1405_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1406_; 
v___x_1406_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1196_, v_flb_1197_, v_tail_1192_, v___x_1405_);
v_x_1183_ = v___x_1406_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_1410_; lean_object* v_a_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
v_a_1410_ = lean_ctor_get(v_f_1202_, 0);
lean_inc(v_a_1410_);
v_a_1411_ = lean_ctor_get(v_f_1202_, 1);
lean_inc(v_a_1411_);
lean_dec_ref_known(v_f_1202_, 2);
v___x_1412_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_1203_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 2, v___x_1412_);
lean_ctor_set(v___x_1206_, 0, v_a_1410_);
v___x_1414_ = v___x_1206_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1410_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_indent_1203_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1415_, 0, v_a_1411_);
lean_ctor_set(v___x_1415_, 1, v_indent_1203_);
lean_ctor_set(v___x_1415_, 2, v_activeTags_1204_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1415_);
v___x_1417_ = v___x_1200_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_tail_1198_);
v___x_1417_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1419_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 1, v___x_1417_);
lean_ctor_set(v___x_1194_, 0, v___x_1414_);
v___x_1419_ = v___x_1194_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1420_; 
v___x_1420_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1196_, v_flb_1197_, v_tail_1192_, v___x_1419_);
v_x_1183_ = v___x_1420_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_1425_; uint8_t v_behavior_1426_; uint8_t v___x_1427_; 
lean_del_object(v___x_1194_);
v_a_1425_ = lean_ctor_get(v_f_1202_, 0);
lean_inc(v_a_1425_);
v_behavior_1426_ = lean_ctor_get_uint8(v_f_1202_, sizeof(void*)*1);
lean_dec_ref_known(v_f_1202_, 1);
v___x_1427_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1196_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1429_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v_a_1425_);
v___x_1429_ = v___x_1206_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1425_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_indent_1203_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v_activeTags_1204_);
v___x_1429_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1430_ = lean_box(0);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 1, v___x_1430_);
lean_ctor_set(v___x_1200_, 0, v___x_1429_);
v___x_1432_ = v___x_1200_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v_fst_1435_; lean_object* v_snd_1436_; 
v___x_1433_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1196_, v_flb_1197_, v_tail_1192_, v_tail_1198_);
v___x_1434_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_behavior_1426_, v___x_1432_, v___x_1433_, v_w_1182_, v___y_1184_);
v_fst_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_fst_1435_);
v_snd_1436_ = lean_ctor_get(v___x_1434_, 1);
lean_inc(v_snd_1436_);
lean_dec_ref(v___x_1434_);
v_x_1183_ = v_fst_1435_;
v___y_1184_ = v_snd_1436_;
goto _start;
}
}
}
else
{
lean_object* v___x_1441_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v_a_1425_);
v___x_1441_ = v___x_1206_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1425_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_indent_1203_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_activeTags_1204_);
v___x_1441_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1443_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1441_);
v___x_1443_ = v___x_1200_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_tail_1198_);
v___x_1443_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1444_; 
v___x_1444_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1196_, v_flb_1197_, v_tail_1192_, v___x_1443_);
v_x_1183_ = v___x_1444_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
lean_del_object(v___x_1194_);
v_a_1448_ = lean_ctor_get(v_f_1202_, 1);
lean_inc(v_a_1448_);
lean_dec_ref_known(v_f_1202_, 2);
v___x_1449_ = lean_unsigned_to_nat(1u);
v___x_1450_ = lean_nat_add(v_activeTags_1204_, v___x_1449_);
lean_dec(v_activeTags_1204_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 2, v___x_1450_);
lean_ctor_set(v___x_1206_, 0, v_a_1448_);
v___x_1452_ = v___x_1206_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1448_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_indent_1203_);
lean_ctor_set(v_reuseFailAlloc_1458_, 2, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1454_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1452_);
v___x_1454_ = v___x_1200_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1452_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_tail_1198_);
v___x_1454_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; 
v___x_1455_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1196_, v_flb_1197_, v_tail_1192_, v___x_1454_);
v_x_1183_ = v___x_1455_;
goto _start;
}
}
}
}
v___jp_1208_:
{
lean_object* v_out_1209_; lean_object* v_column_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1239_; 
v_out_1209_ = lean_ctor_get(v___y_1184_, 0);
v_column_1210_ = lean_ctor_get(v___y_1184_, 1);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___y_1184_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1212_ = v___y_1184_;
v_isShared_1213_ = v_isSharedCheck_1239_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_column_1210_);
lean_inc(v_out_1209_);
lean_dec(v___y_1184_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1239_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
lean_inc(v_column_1210_);
v___x_1214_ = lean_nat_to_int(v_column_1210_);
v___x_1215_ = lean_int_dec_lt(v___x_1214_, v_indent_1203_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; uint32_t v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1222_; 
lean_dec(v___x_1214_);
lean_dec(v_column_1210_);
v___x_1216_ = l_Int_toNat(v_indent_1203_);
lean_dec(v_indent_1203_);
v___x_1217_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1218_ = 32;
lean_inc(v___x_1216_);
v___x_1219_ = lean_string_pushn(v___x_1217_, v___x_1218_, v___x_1216_);
v___x_1220_ = lean_string_append(v_out_1209_, v___x_1219_);
lean_dec_ref(v___x_1219_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v___x_1216_);
lean_ctor_set(v___x_1212_, 0, v___x_1220_);
v___x_1222_ = v___x_1212_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v___x_1216_);
v___x_1222_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1223_; 
v___x_1223_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1196_, v_flb_1197_, v_tail_1192_, v_tail_1198_);
v_x_1183_ = v___x_1223_;
v___y_1184_ = v___x_1222_;
goto _start;
}
}
else
{
lean_object* v___x_1226_; uint32_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1226_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_1227_ = 32;
v___x_1228_ = lean_int_sub(v_indent_1203_, v___x_1214_);
lean_dec(v___x_1214_);
lean_dec(v_indent_1203_);
v___x_1229_ = l_Int_toNat(v___x_1228_);
lean_dec(v___x_1228_);
v___x_1230_ = lean_string_pushn(v___x_1226_, v___x_1227_, v___x_1229_);
v___x_1231_ = lean_string_append(v_out_1209_, v___x_1230_);
v___x_1232_ = lean_string_length(v___x_1230_);
lean_dec_ref(v___x_1230_);
v___x_1233_ = lean_nat_add(v_column_1210_, v___x_1232_);
lean_dec(v___x_1232_);
lean_dec(v_column_1210_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v___x_1233_);
lean_ctor_set(v___x_1212_, 0, v___x_1231_);
v___x_1235_ = v___x_1212_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; 
v___x_1236_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1196_, v_flb_1197_, v_tail_1192_, v_tail_1198_);
v_x_1183_ = v___x_1236_;
v___y_1184_ = v___x_1235_;
goto _start;
}
}
}
}
v___jp_1240_:
{
if (v___y_1241_ == 0)
{
goto v___jp_1208_;
}
else
{
lean_object* v___x_1242_; 
lean_dec(v_indent_1203_);
v___x_1242_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1196_, v_flb_1197_, v_tail_1192_, v_tail_1198_);
v_x_1183_ = v___x_1242_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0___boxed(lean_object* v_w_1464_, lean_object* v_x_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_1464_, v_x_1465_, v___y_1466_);
lean_dec(v_w_1464_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(lean_object* v_f_1468_, lean_object* v_w_1469_, lean_object* v_indent_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1472_ = lean_box(1);
v___x_1473_ = 0;
v___x_1474_ = lean_nat_to_int(v_indent_1470_);
v___x_1475_ = lean_unsigned_to_nat(0u);
v___x_1476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1476_, 0, v_f_1468_);
lean_ctor_set(v___x_1476_, 1, v___x_1474_);
lean_ctor_set(v___x_1476_, 2, v___x_1475_);
v___x_1477_ = lean_box(0);
v___x_1478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1476_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1479_, 0, v___x_1472_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
lean_ctor_set_uint8(v___x_1479_, sizeof(void*)*2, v___x_1473_);
v___x_1480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
lean_ctor_set(v___x_1480_, 1, v___x_1477_);
v___x_1481_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_1469_, v___x_1480_, v___y_1471_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0___boxed(lean_object* v_f_1482_, lean_object* v_w_1483_, lean_object* v_indent_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(v_f_1482_, v_w_1483_, v_indent_1484_, v___y_1485_);
lean_dec(v_w_1483_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty(lean_object* v_f_1487_, lean_object* v_width_1488_, lean_object* v_indent_1489_, lean_object* v_column_1490_){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v_snd_1494_; lean_object* v_out_1495_; 
v___x_1491_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
lean_ctor_set(v___x_1492_, 1, v_column_1490_);
v___x_1493_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(v_f_1487_, v_width_1488_, v_indent_1489_, v___x_1492_);
v_snd_1494_ = lean_ctor_get(v___x_1493_, 1);
lean_inc(v_snd_1494_);
lean_dec_ref(v___x_1493_);
v_out_1495_ = lean_ctor_get(v_snd_1494_, 0);
lean_inc_ref(v_out_1495_);
lean_dec(v_snd_1494_);
return v_out_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty___boxed(lean_object* v_f_1496_, lean_object* v_width_1497_, lean_object* v_indent_1498_, lean_object* v_column_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Std_Format_pretty(v_f_1496_, v_width_1497_, v_indent_1498_, v_column_1499_);
lean_dec(v_width_1497_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0(lean_object* v_f_1501_){
_start:
{
lean_inc(v_f_1501_);
return v_f_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object* v_f_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Std_instToFormatFormat___lam__0(v_f_1502_);
lean_dec(v_f_1502_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatString___lam__0(lean_object* v_s_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1507_, 0, v_s_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg___lam__0(lean_object* v_x_1510_, lean_object* v_inst_1511_, lean_object* v_x1_1512_, lean_object* v_x2_1513_){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_x1_1512_);
lean_ctor_set(v___x_1514_, 1, v_x_1510_);
v___x_1515_ = lean_apply_1(v_inst_1511_, v_x2_1513_);
v___x_1516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1514_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg(lean_object* v_inst_1517_, lean_object* v_x_1518_, lean_object* v_x_1519_){
_start:
{
if (lean_obj_tag(v_x_1518_) == 0)
{
lean_object* v___x_1520_; 
lean_dec(v_x_1519_);
lean_dec_ref(v_inst_1517_);
v___x_1520_ = lean_box(0);
return v___x_1520_;
}
else
{
lean_object* v_tail_1521_; 
v_tail_1521_ = lean_ctor_get(v_x_1518_, 1);
if (lean_obj_tag(v_tail_1521_) == 0)
{
lean_object* v_head_1522_; lean_object* v___x_1523_; 
lean_dec(v_x_1519_);
v_head_1522_ = lean_ctor_get(v_x_1518_, 0);
lean_inc(v_head_1522_);
lean_dec_ref_known(v_x_1518_, 2);
v___x_1523_ = lean_apply_1(v_inst_1517_, v_head_1522_);
return v___x_1523_;
}
else
{
lean_object* v_head_1524_; lean_object* v___f_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_inc(v_tail_1521_);
v_head_1524_ = lean_ctor_get(v_x_1518_, 0);
lean_inc(v_head_1524_);
lean_dec_ref_known(v_x_1518_, 2);
lean_inc_ref(v_inst_1517_);
v___f_1525_ = lean_alloc_closure((void*)(l_Std_Format_joinSep___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1525_, 0, v_x_1519_);
lean_closure_set(v___f_1525_, 1, v_inst_1517_);
v___x_1526_ = lean_apply_1(v_inst_1517_, v_head_1524_);
v___x_1527_ = l_List_foldl___redArg(v___f_1525_, v___x_1526_, v_tail_1521_);
return v___x_1527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep(lean_object* v_00_u03b1_1528_, lean_object* v_inst_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Std_Format_joinSep___redArg(v_inst_1529_, v_x_1530_, v_x_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg___lam__0(lean_object* v_pre_1533_, lean_object* v_inst_1534_, lean_object* v_x1_1535_, lean_object* v_x2_1536_){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1537_, 0, v_x1_1535_);
lean_ctor_set(v___x_1537_, 1, v_pre_1533_);
v___x_1538_ = lean_apply_1(v_inst_1534_, v_x2_1536_);
v___x_1539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg(lean_object* v_inst_1540_, lean_object* v_pre_1541_, lean_object* v_x_1542_){
_start:
{
if (lean_obj_tag(v_x_1542_) == 0)
{
lean_object* v___x_1543_; 
lean_dec(v_pre_1541_);
lean_dec_ref(v_inst_1540_);
v___x_1543_ = lean_box(0);
return v___x_1543_;
}
else
{
lean_object* v_head_1544_; lean_object* v_tail_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1555_; 
v_head_1544_ = lean_ctor_get(v_x_1542_, 0);
v_tail_1545_ = lean_ctor_get(v_x_1542_, 1);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_x_1542_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1547_ = v_x_1542_;
v_isShared_1548_ = v_isSharedCheck_1555_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_tail_1545_);
lean_inc(v_head_1544_);
lean_dec(v_x_1542_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1555_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___f_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
lean_inc_ref(v_inst_1540_);
lean_inc(v_pre_1541_);
v___f_1549_ = lean_alloc_closure((void*)(l_Std_Format_prefixJoin___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1549_, 0, v_pre_1541_);
lean_closure_set(v___f_1549_, 1, v_inst_1540_);
v___x_1550_ = lean_apply_1(v_inst_1540_, v_head_1544_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set_tag(v___x_1547_, 5);
lean_ctor_set(v___x_1547_, 1, v___x_1550_);
lean_ctor_set(v___x_1547_, 0, v_pre_1541_);
v___x_1552_ = v___x_1547_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_pre_1541_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_List_foldl___redArg(v___f_1549_, v___x_1552_, v_tail_1545_);
return v___x_1553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin(lean_object* v_00_u03b1_1556_, lean_object* v_inst_1557_, lean_object* v_pre_1558_, lean_object* v_x_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Std_Format_prefixJoin___redArg(v_inst_1557_, v_pre_1558_, v_x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg___lam__0(lean_object* v_inst_1561_, lean_object* v_x_1562_, lean_object* v_x1_1563_, lean_object* v_x2_1564_){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1565_ = lean_apply_1(v_inst_1561_, v_x2_1564_);
v___x_1566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1566_, 0, v_x1_1563_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
lean_ctor_set(v___x_1567_, 1, v_x_1562_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg(lean_object* v_inst_1568_, lean_object* v_x_1569_, lean_object* v_x_1570_){
_start:
{
if (lean_obj_tag(v_x_1569_) == 0)
{
lean_object* v___x_1571_; 
lean_dec(v_x_1570_);
lean_dec_ref(v_inst_1568_);
v___x_1571_ = lean_box(0);
return v___x_1571_;
}
else
{
lean_object* v_head_1572_; lean_object* v_tail_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1583_; 
v_head_1572_ = lean_ctor_get(v_x_1569_, 0);
v_tail_1573_ = lean_ctor_get(v_x_1569_, 1);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_x_1569_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1575_ = v_x_1569_;
v_isShared_1576_ = v_isSharedCheck_1583_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_tail_1573_);
lean_inc(v_head_1572_);
lean_dec(v_x_1569_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1583_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___f_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_inc(v_x_1570_);
lean_inc_ref(v_inst_1568_);
v___f_1577_ = lean_alloc_closure((void*)(l_Std_Format_joinSuffix___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1577_, 0, v_inst_1568_);
lean_closure_set(v___f_1577_, 1, v_x_1570_);
v___x_1578_ = lean_apply_1(v_inst_1568_, v_head_1572_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set_tag(v___x_1575_, 5);
lean_ctor_set(v___x_1575_, 1, v_x_1570_);
lean_ctor_set(v___x_1575_, 0, v___x_1578_);
v___x_1580_ = v___x_1575_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_x_1570_);
v___x_1580_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_List_foldl___redArg(v___f_1577_, v___x_1580_, v_tail_1573_);
return v___x_1581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix(lean_object* v_00_u03b1_1584_, lean_object* v_inst_1585_, lean_object* v_x_1586_, lean_object* v_x_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Std_Format_joinSuffix___redArg(v_inst_1585_, v_x_1586_, v_x_1587_);
return v___x_1588_;
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
