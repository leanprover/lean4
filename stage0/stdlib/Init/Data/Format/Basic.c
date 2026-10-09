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
lean_object* l_Std_Format_FlattenBehavior_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Std_Format_FlattenBehavior_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Std_Format_FlattenBehavior_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Std_Format_FlattenBehavior_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_Format_FlattenBehavior_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Std_Format_FlattenBehavior_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Std_Format_FlattenBehavior_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Std_Format_FlattenBehavior_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Std_Format_FlattenBehavior_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim___redArg(lean_object* v_allOrNone_24_){
_start:
{
lean_inc(v_allOrNone_24_);
return v_allOrNone_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim___redArg___boxed(lean_object* v_allOrNone_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Format_FlattenBehavior_allOrNone_elim___redArg(v_allOrNone_25_);
lean_dec(v_allOrNone_25_);
return v_res_26_;
}
}
lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_allOrNone_30_){
_start:
{
lean_inc(v_allOrNone_30_);
return v_allOrNone_30_;
}
}
LEAN_EXPORT void l_Std_Format_FlattenBehavior_allOrNone_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_allOrNone_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Std_Format_FlattenBehavior_allOrNone_elim(lean_box(0), v_t_28_, lean_box(0), v_allOrNone_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_allOrNone_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_allOrNone_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Std_Format_FlattenBehavior_allOrNone_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_allOrNone_35_);
lean_dec(v_allOrNone_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim___redArg(lean_object* v_fill_38_){
_start:
{
lean_inc(v_fill_38_);
return v_fill_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim___redArg___boxed(lean_object* v_fill_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Format_FlattenBehavior_fill_elim___redArg(v_fill_39_);
lean_dec(v_fill_39_);
return v_res_40_;
}
}
lean_object* l_Std_Format_FlattenBehavior_fill_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_fill_44_){
_start:
{
lean_inc(v_fill_44_);
return v_fill_44_;
}
}
LEAN_EXPORT void l_Std_Format_FlattenBehavior_fill_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_fill_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Std_Format_FlattenBehavior_fill_elim(lean_box(0), v_t_42_, lean_box(0), v_fill_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenBehavior_fill_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_fill_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Std_Format_FlattenBehavior_fill_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_fill_49_);
lean_dec(v_fill_49_);
return v_res_51_;
}
}
static uint8_t _init_l_Std_Format_instInhabitedFlattenBehavior_default(void){
_start:
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
}
static uint8_t _init_l_Std_Format_instInhabitedFlattenBehavior(void){
_start:
{
uint8_t v___x_53_; 
v___x_53_ = 0;
return v___x_53_;
}
}
uint8_t l_Std_Format_instBEqFlattenBehavior_beq(uint8_t v_x_54_, uint8_t v_y_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_56_ = lean_box(v_x_54_);
v___x_57_ = lean_obj_tag_nat(v___x_56_);
lean_dec(v___x_56_);
v___x_58_ = lean_box(v_y_55_);
v___x_59_ = lean_obj_tag_nat(v___x_58_);
lean_dec(v___x_58_);
v___x_60_ = lean_nat_dec_eq(v___x_57_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT void l_Std_Format_instBEqFlattenBehavior_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_54_ = stack[0].m_num;
uint8_t v_y_55_ = stack[1].m_num;
uint8_t v_res_61_;
v_res_61_ = l_Std_Format_instBEqFlattenBehavior_beq(v_x_54_, v_y_55_);
stack->m_num = v_res_61_;
}
LEAN_EXPORT lean_object* l_Std_Format_instBEqFlattenBehavior_beq___boxed(lean_object* v_x_62_, lean_object* v_y_63_){
_start:
{
uint8_t v_x_24__boxed_64_; uint8_t v_y_25__boxed_65_; uint8_t v_res_66_; lean_object* v_r_67_; 
v_x_24__boxed_64_ = lean_unbox(v_x_62_);
v_y_25__boxed_65_ = lean_unbox(v_y_63_);
v_res_66_ = l_Std_Format_instBEqFlattenBehavior_beq(v_x_24__boxed_64_, v_y_25__boxed_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorIdx___impl(lean_object* v_x_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_obj_tag_nat(v_x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_ctorIdx___impl___boxed(lean_object* v_x_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Std_Format_ctorIdx___impl(v_x_72_);
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
uint8_t l_Std_Format_isEmpty(lean_object* v_x_173_){
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
LEAN_EXPORT void l_Std_Format_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_173_ = stack[0].m_obj;
uint8_t v_res_189_;
v_res_189_ = l_Std_Format_isEmpty(v_x_173_);
stack->m_num = v_res_189_;
}
LEAN_EXPORT lean_object* l_Std_Format_isEmpty___boxed(lean_object* v_x_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Std_Format_isEmpty(v_x_190_);
lean_dec(v_x_190_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_fill(lean_object* v_f_193_){
_start:
{
uint8_t v___x_194_; lean_object* v___x_195_; 
v___x_194_ = 1;
v___x_195_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_195_, 0, v_f_193_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*1, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_instAppend___lam__0(lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v_a_196_);
lean_ctor_set(v___x_198_, 1, v_a_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_instCoeString___lam__0(lean_object* v_a_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_202_, 0, v_a_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_join_spec__0(lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
if (lean_obj_tag(v_x_206_) == 0)
{
return v_x_205_;
}
else
{
lean_object* v_head_207_; lean_object* v_tail_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_216_; 
v_head_207_ = lean_ctor_get(v_x_206_, 0);
v_tail_208_ = lean_ctor_get(v_x_206_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_x_206_);
if (v_isSharedCheck_216_ == 0)
{
v___x_210_ = v_x_206_;
v_isShared_211_ = v_isSharedCheck_216_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_tail_208_);
lean_inc(v_head_207_);
lean_dec(v_x_206_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_216_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set_tag(v___x_210_, 5);
lean_ctor_set(v___x_210_, 1, v_head_207_);
lean_ctor_set(v___x_210_, 0, v_x_205_);
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_x_205_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_head_207_);
v___x_213_ = v_reuseFailAlloc_215_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
v_x_205_ = v___x_213_;
v_x_206_ = v_tail_208_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_join(lean_object* v_xs_219_){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l_Std_Format_join___closed__0));
v___x_221_ = l_List_foldl___at___00Std_Format_join_spec__0(v___x_220_, v_xs_219_);
return v___x_221_;
}
}
uint8_t l_Std_Format_isNil(lean_object* v_x_222_){
_start:
{
if (lean_obj_tag(v_x_222_) == 0)
{
uint8_t v___x_223_; 
v___x_223_ = 1;
return v___x_223_;
}
else
{
uint8_t v___x_224_; 
v___x_224_ = 0;
return v___x_224_;
}
}
}
LEAN_EXPORT void l_Std_Format_isNil_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_222_ = stack[0].m_obj;
uint8_t v_res_225_;
v_res_225_ = l_Std_Format_isNil(v_x_222_);
stack->m_num = v_res_225_;
}
LEAN_EXPORT lean_object* l_Std_Format_isNil___boxed(lean_object* v_x_226_){
_start:
{
uint8_t v_res_227_; lean_object* v_r_228_; 
v_res_227_ = l_Std_Format_isNil(v_x_226_);
lean_dec(v_x_226_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_merge(lean_object* v_w_234_, lean_object* v_r_u2081_235_, lean_object* v_r_u2082_236_){
_start:
{
uint8_t v_foundLine_237_; lean_object* v_space_238_; uint8_t v___x_239_; 
v_foundLine_237_ = lean_ctor_get_uint8(v_r_u2081_235_, sizeof(void*)*1);
v_space_238_ = lean_ctor_get(v_r_u2081_235_, 0);
v___x_239_ = lean_nat_dec_lt(v_w_234_, v_space_238_);
if (v___x_239_ == 0)
{
if (v_foundLine_237_ == 0)
{
lean_object* v___x_240_; lean_object* v_r_u2082_241_; uint8_t v_foundLine_242_; uint8_t v_foundFlattenedHardLine_243_; lean_object* v_space_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_252_; 
v___x_240_ = lean_nat_sub(v_w_234_, v_space_238_);
v_r_u2082_241_ = lean_apply_1(v_r_u2082_236_, v___x_240_);
v_foundLine_242_ = lean_ctor_get_uint8(v_r_u2082_241_, sizeof(void*)*1);
v_foundFlattenedHardLine_243_ = lean_ctor_get_uint8(v_r_u2082_241_, sizeof(void*)*1 + 1);
v_space_244_ = lean_ctor_get(v_r_u2082_241_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v_r_u2082_241_);
if (v_isSharedCheck_252_ == 0)
{
v___x_246_ = v_r_u2082_241_;
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_space_244_);
lean_dec(v_r_u2082_241_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_248_ = lean_nat_add(v_space_238_, v_space_244_);
lean_dec(v_space_244_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_248_);
v___x_250_ = v___x_246_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
lean_ctor_set_uint8(v_reuseFailAlloc_251_, sizeof(void*)*1, v_foundLine_242_);
lean_ctor_set_uint8(v_reuseFailAlloc_251_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_243_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
else
{
lean_dec_ref(v_r_u2082_236_);
lean_inc_ref(v_r_u2081_235_);
return v_r_u2081_235_;
}
}
else
{
lean_dec_ref(v_r_u2082_236_);
lean_inc_ref(v_r_u2081_235_);
return v_r_u2081_235_;
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
lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(lean_object* v_x_262_, uint8_t v_x_263_, lean_object* v_x_264_, lean_object* v_x_265_){
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
lean_object* v_a_285_; uint32_t v___x_286_; lean_object* v_p_287_; lean_object* v_off_288_; uint8_t v___y_290_; lean_object* v___x_293_; uint8_t v_decide_294_; 
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
v_decide_294_ = lean_nat_dec_eq(v_p_287_, v___x_293_);
lean_dec(v_p_287_);
if (v_decide_294_ == 0)
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
lean_object* v_a_301_; lean_object* v_a_302_; lean_object* v___x_303_; uint8_t v_foundLine_304_; lean_object* v_space_305_; uint8_t v___x_306_; 
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
v___x_306_ = lean_nat_dec_lt(v_x_265_, v_space_305_);
if (v___x_306_ == 0)
{
if (v_foundLine_304_ == 0)
{
lean_object* v___x_307_; lean_object* v_r_u2082_308_; uint8_t v_foundLine_309_; uint8_t v_foundFlattenedHardLine_310_; lean_object* v_space_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_319_; 
lean_inc(v_space_305_);
lean_dec_ref(v___x_303_);
v___x_307_ = lean_nat_sub(v_x_265_, v_space_305_);
lean_dec(v_x_265_);
v_r_u2082_308_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_a_302_, v_x_263_, v_x_264_, v___x_307_);
v_foundLine_309_ = lean_ctor_get_uint8(v_r_u2082_308_, sizeof(void*)*1);
v_foundFlattenedHardLine_310_ = lean_ctor_get_uint8(v_r_u2082_308_, sizeof(void*)*1 + 1);
v_space_311_ = lean_ctor_get(v_r_u2082_308_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v_r_u2082_308_);
if (v_isSharedCheck_319_ == 0)
{
v___x_313_ = v_r_u2082_308_;
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_space_311_);
lean_dec(v_r_u2082_308_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_315_ = lean_nat_add(v_space_305_, v_space_311_);
lean_dec(v_space_311_);
lean_dec(v_space_305_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_315_);
v___x_317_ = v___x_313_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
lean_ctor_set_uint8(v_reuseFailAlloc_318_, sizeof(void*)*1, v_foundLine_309_);
lean_ctor_set_uint8(v_reuseFailAlloc_318_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_310_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
else
{
lean_dec(v_a_302_);
lean_dec(v_x_265_);
lean_dec(v_x_264_);
return v___x_303_;
}
}
else
{
lean_dec(v_a_302_);
lean_dec(v_x_265_);
lean_dec(v_x_264_);
return v___x_303_;
}
}
case 6:
{
lean_object* v_a_320_; uint8_t v___x_321_; 
v_a_320_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_a_320_);
lean_dec_ref_known(v_x_262_, 1);
v___x_321_ = 1;
v_x_262_ = v_a_320_;
v_x_263_ = v___x_321_;
goto _start;
}
default: 
{
lean_object* v_a_323_; 
v_a_323_ = lean_ctor_get(v_x_262_, 1);
lean_inc(v_a_323_);
lean_dec_ref_known(v_x_262_, 2);
v_x_262_ = v_a_323_;
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
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*1 + 1, v___x_269_);
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
LEAN_EXPORT void l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_262_ = stack[0].m_obj;
uint8_t v_x_263_ = stack[1].m_num;
lean_object* v_x_264_ = stack[2].m_obj;
lean_object* v_x_265_ = stack[3].m_obj;
lean_object* v_res_325_;
v_res_325_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_x_262_, v_x_263_, v_x_264_, v_x_265_);
stack->m_obj
 = v_res_325_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine___boxed(lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
uint8_t v_x_401__boxed_330_; lean_object* v_res_331_; 
v_x_401__boxed_330_ = lean_unbox(v_x_327_);
v_res_331_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine(v_x_326_, v_x_401__boxed_330_, v_x_328_, v_x_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx___impl(lean_object* v_x_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_obj_tag_nat(v_x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorIdx___impl___boxed(lean_object* v_x_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Std_Format_FlattenAllowability_ctorIdx___impl(v_x_334_);
lean_dec(v_x_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___redArg(lean_object* v_t_336_, lean_object* v_k_337_){
_start:
{
if (lean_obj_tag(v_t_336_) == 0)
{
uint8_t v_fits_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_fits_338_ = lean_ctor_get_uint8(v_t_336_, 0);
v___x_339_ = lean_box(v_fits_338_);
v___x_340_ = lean_apply_1(v_k_337_, v___x_339_);
return v___x_340_;
}
else
{
return v_k_337_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___redArg___boxed(lean_object* v_t_341_, lean_object* v_k_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_341_, v_k_342_);
lean_dec(v_t_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim(lean_object* v_motive_344_, lean_object* v_ctorIdx_345_, lean_object* v_t_346_, lean_object* v_h_347_, lean_object* v_k_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_346_, v_k_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_ctorElim___boxed(lean_object* v_motive_350_, lean_object* v_ctorIdx_351_, lean_object* v_t_352_, lean_object* v_h_353_, lean_object* v_k_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Std_Format_FlattenAllowability_ctorElim(v_motive_350_, v_ctorIdx_351_, v_t_352_, v_h_353_, v_k_354_);
lean_dec(v_t_352_);
lean_dec(v_ctorIdx_351_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___redArg(lean_object* v_t_356_, lean_object* v_allow_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_356_, v_allow_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___redArg___boxed(lean_object* v_t_359_, lean_object* v_allow_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_Format_FlattenAllowability_allow_elim___redArg(v_t_359_, v_allow_360_);
lean_dec(v_t_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim(lean_object* v_motive_362_, lean_object* v_t_363_, lean_object* v_h_364_, lean_object* v_allow_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_363_, v_allow_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_allow_elim___boxed(lean_object* v_motive_367_, lean_object* v_t_368_, lean_object* v_h_369_, lean_object* v_allow_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Std_Format_FlattenAllowability_allow_elim(v_motive_367_, v_t_368_, v_h_369_, v_allow_370_);
lean_dec(v_t_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___redArg(lean_object* v_t_372_, lean_object* v_disallow_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_372_, v_disallow_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___redArg___boxed(lean_object* v_t_375_, lean_object* v_disallow_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Std_Format_FlattenAllowability_disallow_elim___redArg(v_t_375_, v_disallow_376_);
lean_dec(v_t_375_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim(lean_object* v_motive_378_, lean_object* v_t_379_, lean_object* v_h_380_, lean_object* v_disallow_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Std_Format_FlattenAllowability_ctorElim___redArg(v_t_379_, v_disallow_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_FlattenAllowability_disallow_elim___boxed(lean_object* v_motive_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_disallow_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Std_Format_FlattenAllowability_disallow_elim(v_motive_383_, v_t_384_, v_h_385_, v_disallow_386_);
lean_dec(v_t_384_);
return v_res_387_;
}
}
uint8_t l_Std_Format_instBEqFlattenAllowability_beq(lean_object* v_x_388_, lean_object* v_x_389_){
_start:
{
if (lean_obj_tag(v_x_388_) == 0)
{
if (lean_obj_tag(v_x_389_) == 0)
{
uint8_t v_fits_390_; 
v_fits_390_ = lean_ctor_get_uint8(v_x_389_, 0);
if (v_fits_390_ == 0)
{
uint8_t v_fits_391_; 
v_fits_391_ = lean_ctor_get_uint8(v_x_388_, 0);
if (v_fits_391_ == 0)
{
uint8_t v___x_392_; 
v___x_392_ = 1;
return v___x_392_;
}
else
{
return v_fits_390_;
}
}
else
{
uint8_t v_fits_393_; 
v_fits_393_ = lean_ctor_get_uint8(v_x_388_, 0);
return v_fits_393_;
}
}
else
{
uint8_t v___x_394_; 
v___x_394_ = 0;
return v___x_394_;
}
}
else
{
if (lean_obj_tag(v_x_389_) == 1)
{
uint8_t v___x_395_; 
v___x_395_ = 1;
return v___x_395_;
}
else
{
uint8_t v___x_396_; 
v___x_396_ = 0;
return v___x_396_;
}
}
}
}
LEAN_EXPORT void l_Std_Format_instBEqFlattenAllowability_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_388_ = stack[0].m_obj;
lean_object* v_x_389_ = stack[1].m_obj;
uint8_t v_res_397_;
v_res_397_ = l_Std_Format_instBEqFlattenAllowability_beq(v_x_388_, v_x_389_);
stack->m_num = v_res_397_;
}
LEAN_EXPORT lean_object* l_Std_Format_instBEqFlattenAllowability_beq___boxed(lean_object* v_x_398_, lean_object* v_x_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l_Std_Format_instBEqFlattenAllowability_beq(v_x_398_, v_x_399_);
lean_dec(v_x_399_);
lean_dec(v_x_398_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
uint8_t l_Std_Format_FlattenAllowability_shouldFlatten(lean_object* v_x_404_){
_start:
{
if (lean_obj_tag(v_x_404_) == 0)
{
uint8_t v_fits_405_; 
v_fits_405_ = lean_ctor_get_uint8(v_x_404_, 0);
if (v_fits_405_ == 1)
{
return v_fits_405_;
}
else
{
uint8_t v___x_406_; 
v___x_406_ = 0;
return v___x_406_;
}
}
else
{
uint8_t v___x_407_; 
v___x_407_ = 0;
return v___x_407_;
}
}
}
LEAN_EXPORT void l_Std_Format_FlattenAllowability_shouldFlatten_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_404_ = stack[0].m_obj;
uint8_t v_res_408_;
v_res_408_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_x_404_);
stack->m_num = v_res_408_;
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
lean_object* v_head_420_; lean_object* v_tail_421_; lean_object* v_fla_422_; uint8_t v_flb_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_463_; 
v_head_420_ = lean_ctor_get(v_items_417_, 0);
lean_inc(v_head_420_);
v_tail_421_ = lean_ctor_get(v_x_412_, 1);
lean_inc(v_tail_421_);
lean_dec_ref_known(v_x_412_, 2);
v_fla_422_ = lean_ctor_get(v_head_416_, 0);
v_flb_423_ = lean_ctor_get_uint8(v_head_416_, sizeof(void*)*2);
v_isSharedCheck_463_ = !lean_is_exclusive(v_head_416_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; 
v_unused_464_ = lean_ctor_get(v_head_416_, 1);
lean_dec(v_unused_464_);
v___x_425_ = v_head_416_;
v_isShared_426_ = v_isSharedCheck_463_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_fla_422_);
lean_dec(v_head_416_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_463_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v_tail_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_461_; 
v_tail_427_ = lean_ctor_get(v_items_417_, 1);
v_isSharedCheck_461_ = !lean_is_exclusive(v_items_417_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; 
v_unused_462_ = lean_ctor_get(v_items_417_, 0);
lean_dec(v_unused_462_);
v___x_429_ = v_items_417_;
v_isShared_430_ = v_isSharedCheck_461_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_tail_427_);
lean_dec(v_items_417_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_461_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v_f_431_; lean_object* v_indent_432_; uint8_t v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v_foundLine_439_; lean_object* v_space_440_; uint8_t v___x_441_; 
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
v___x_441_ = lean_nat_dec_lt(v_x_414_, v_space_440_);
if (v___x_441_ == 0)
{
if (v_foundLine_439_ == 0)
{
lean_object* v___x_443_; 
lean_inc(v_space_440_);
lean_dec_ref(v___x_438_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 1, v_tail_427_);
v___x_443_ = v___x_425_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_fla_422_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_tail_427_);
lean_ctor_set_uint8(v_reuseFailAlloc_460_, sizeof(void*)*2, v_flb_423_);
v___x_443_ = v_reuseFailAlloc_460_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_445_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v_tail_421_);
lean_ctor_set(v___x_429_, 0, v___x_443_);
v___x_445_ = v___x_429_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_tail_421_);
v___x_445_ = v_reuseFailAlloc_459_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; lean_object* v_r_u2082_447_; uint8_t v_foundLine_448_; uint8_t v_foundFlattenedHardLine_449_; lean_object* v_space_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_458_; 
v___x_446_ = lean_nat_sub(v_x_414_, v_space_440_);
lean_dec(v_x_414_);
v_r_u2082_447_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_445_, v_x_413_, v___x_446_);
v_foundLine_448_ = lean_ctor_get_uint8(v_r_u2082_447_, sizeof(void*)*1);
v_foundFlattenedHardLine_449_ = lean_ctor_get_uint8(v_r_u2082_447_, sizeof(void*)*1 + 1);
v_space_450_ = lean_ctor_get(v_r_u2082_447_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v_r_u2082_447_);
if (v_isSharedCheck_458_ == 0)
{
v___x_452_ = v_r_u2082_447_;
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_space_450_);
lean_dec(v_r_u2082_447_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_454_ = lean_nat_add(v_space_440_, v_space_450_);
lean_dec(v_space_450_);
lean_dec(v_space_440_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_454_);
v___x_456_ = v___x_452_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*1, v_foundLine_448_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_449_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
else
{
lean_del_object(v___x_429_);
lean_dec(v_tail_427_);
lean_del_object(v___x_425_);
lean_dec(v_fla_422_);
lean_dec(v_tail_421_);
lean_dec(v_x_414_);
lean_dec(v_x_413_);
return v___x_438_;
}
}
else
{
lean_del_object(v___x_429_);
lean_dec(v_tail_427_);
lean_del_object(v___x_425_);
lean_dec(v_fla_422_);
lean_dec(v_tail_421_);
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
lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(uint8_t v_flb_465_, lean_object* v_items_466_, lean_object* v_w_467_, lean_object* v_gs_468_, lean_object* v_toPure_469_, lean_object* v_k_470_){
_start:
{
uint8_t v___y_472_; uint8_t v___x_477_; uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v_g_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v_r_484_; lean_object* v___y_486_; uint8_t v_foundLine_491_; lean_object* v_space_492_; uint8_t v___x_493_; 
v___x_477_ = 0;
v___x_478_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_465_, v___x_477_);
v___x_479_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_479_, 0, v___x_478_);
lean_inc(v_items_466_);
v_g_480_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_480_, 0, v___x_479_);
lean_ctor_set(v_g_480_, 1, v_items_466_);
lean_ctor_set_uint8(v_g_480_, sizeof(void*)*2, v_flb_465_);
v___x_481_ = lean_box(0);
v___x_482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_482_, 0, v_g_480_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = lean_nat_sub(v_w_467_, v_k_470_);
lean_inc(v___x_483_);
lean_inc(v_k_470_);
v_r_484_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_482_, v_k_470_, v___x_483_);
v_foundLine_491_ = lean_ctor_get_uint8(v_r_484_, sizeof(void*)*1);
v_space_492_ = lean_ctor_get(v_r_484_, 0);
v___x_493_ = lean_nat_dec_lt(v___x_483_, v_space_492_);
if (v___x_493_ == 0)
{
if (v_foundLine_491_ == 0)
{
lean_object* v___x_494_; lean_object* v_r_u2082_495_; uint8_t v_foundLine_496_; uint8_t v_foundFlattenedHardLine_497_; lean_object* v_space_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_506_; 
v___x_494_ = lean_nat_sub(v___x_483_, v_space_492_);
lean_inc(v_gs_468_);
v_r_u2082_495_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_468_, v_k_470_, v___x_494_);
v_foundLine_496_ = lean_ctor_get_uint8(v_r_u2082_495_, sizeof(void*)*1);
v_foundFlattenedHardLine_497_ = lean_ctor_get_uint8(v_r_u2082_495_, sizeof(void*)*1 + 1);
v_space_498_ = lean_ctor_get(v_r_u2082_495_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v_r_u2082_495_);
if (v_isSharedCheck_506_ == 0)
{
v___x_500_ = v_r_u2082_495_;
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_space_498_);
lean_dec(v_r_u2082_495_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = lean_nat_add(v_space_492_, v_space_498_);
lean_dec(v_space_498_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_502_);
v___x_504_ = v___x_500_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
lean_ctor_set_uint8(v_reuseFailAlloc_505_, sizeof(void*)*1, v_foundLine_496_);
lean_ctor_set_uint8(v_reuseFailAlloc_505_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_497_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
v___y_486_ = v___x_504_;
goto v___jp_485_;
}
}
}
else
{
lean_dec(v_k_470_);
lean_inc_ref(v_r_484_);
v___y_486_ = v_r_484_;
goto v___jp_485_;
}
}
else
{
lean_dec(v_k_470_);
lean_inc_ref(v_r_484_);
v___y_486_ = v_r_484_;
goto v___jp_485_;
}
v___jp_471_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_473_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_473_, 0, v___y_472_);
v___x_474_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v_items_466_);
lean_ctor_set_uint8(v___x_474_, sizeof(void*)*2, v_flb_465_);
v___x_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set(v___x_475_, 1, v_gs_468_);
v___x_476_ = lean_apply_2(v_toPure_469_, lean_box(0), v___x_475_);
return v___x_476_;
}
v___jp_485_:
{
uint8_t v_foundFlattenedHardLine_487_; 
v_foundFlattenedHardLine_487_ = lean_ctor_get_uint8(v_r_484_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_484_);
if (v_foundFlattenedHardLine_487_ == 0)
{
lean_object* v_space_488_; uint8_t v___x_489_; 
v_space_488_ = lean_ctor_get(v___y_486_, 0);
lean_inc(v_space_488_);
lean_dec_ref(v___y_486_);
v___x_489_ = lean_nat_dec_le(v_space_488_, v___x_483_);
lean_dec(v___x_483_);
lean_dec(v_space_488_);
v___y_472_ = v___x_489_;
goto v___jp_471_;
}
else
{
uint8_t v___x_490_; 
lean_dec_ref(v___y_486_);
lean_dec(v___x_483_);
v___x_490_ = 0;
v___y_472_ = v___x_490_;
goto v___jp_471_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_flb_465_ = stack[0].m_num;
lean_object* v_items_466_ = stack[1].m_obj;
lean_object* v_w_467_ = stack[2].m_obj;
lean_object* v_gs_468_ = stack[3].m_obj;
lean_object* v_toPure_469_ = stack[4].m_obj;
lean_object* v_k_470_ = stack[5].m_obj;
lean_object* v_res_507_;
v_res_507_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(v_flb_465_, v_items_466_, v_w_467_, v_gs_468_, v_toPure_469_, v_k_470_);
stack->m_obj
 = v_res_507_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed(lean_object* v_flb_508_, lean_object* v_items_509_, lean_object* v_w_510_, lean_object* v_gs_511_, lean_object* v_toPure_512_, lean_object* v_k_513_){
_start:
{
uint8_t v_flb_boxed_514_; lean_object* v_res_515_; 
v_flb_boxed_514_ = lean_unbox(v_flb_508_);
v_res_515_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0(v_flb_boxed_514_, v_items_509_, v_w_510_, v_gs_511_, v_toPure_512_, v_k_513_);
lean_dec(v_w_510_);
return v_res_515_;
}
}
lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(uint8_t v_flb_516_, lean_object* v_items_517_, lean_object* v_gs_518_, lean_object* v_w_519_, lean_object* v_inst_520_, lean_object* v_inst_521_){
_start:
{
lean_object* v_toApplicative_522_; lean_object* v_toBind_523_; lean_object* v_currColumn_524_; lean_object* v_toPure_525_; lean_object* v___x_526_; lean_object* v___f_527_; lean_object* v___x_528_; 
v_toApplicative_522_ = lean_ctor_get(v_inst_520_, 0);
lean_inc_ref(v_toApplicative_522_);
v_toBind_523_ = lean_ctor_get(v_inst_520_, 1);
lean_inc(v_toBind_523_);
lean_dec_ref(v_inst_520_);
v_currColumn_524_ = lean_ctor_get(v_inst_521_, 2);
lean_inc(v_currColumn_524_);
lean_dec_ref(v_inst_521_);
v_toPure_525_ = lean_ctor_get(v_toApplicative_522_, 1);
lean_inc(v_toPure_525_);
lean_dec_ref(v_toApplicative_522_);
v___x_526_ = lean_box(v_flb_516_);
v___f_527_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_527_, 0, v___x_526_);
lean_closure_set(v___f_527_, 1, v_items_517_);
lean_closure_set(v___f_527_, 2, v_w_519_);
lean_closure_set(v___f_527_, 3, v_gs_518_);
lean_closure_set(v___f_527_, 4, v_toPure_525_);
v___x_528_ = lean_apply_4(v_toBind_523_, lean_box(0), lean_box(0), v_currColumn_524_, v___f_527_);
return v___x_528_;
}
}
LEAN_EXPORT void l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_flb_516_ = stack[0].m_num;
lean_object* v_items_517_ = stack[1].m_obj;
lean_object* v_gs_518_ = stack[2].m_obj;
lean_object* v_w_519_ = stack[3].m_obj;
lean_object* v_inst_520_ = stack[4].m_obj;
lean_object* v_inst_521_ = stack[5].m_obj;
lean_object* v_res_529_;
v_res_529_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_516_, v_items_517_, v_gs_518_, v_w_519_, v_inst_520_, v_inst_521_);
stack->m_obj
 = v_res_529_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg___boxed(lean_object* v_flb_530_, lean_object* v_items_531_, lean_object* v_gs_532_, lean_object* v_w_533_, lean_object* v_inst_534_, lean_object* v_inst_535_){
_start:
{
uint8_t v_flb_boxed_536_; lean_object* v_res_537_; 
v_flb_boxed_536_ = lean_unbox(v_flb_530_);
v_res_537_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_boxed_536_, v_items_531_, v_gs_532_, v_w_533_, v_inst_534_, v_inst_535_);
return v_res_537_;
}
}
lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(lean_object* v_m_538_, uint8_t v_flb_539_, lean_object* v_items_540_, lean_object* v_gs_541_, lean_object* v_w_542_, lean_object* v_inst_543_, lean_object* v_inst_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_539_, v_items_540_, v_gs_541_, v_w_542_, v_inst_543_, v_inst_544_);
return v___x_545_;
}
}
LEAN_EXPORT void l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup_0interp(lean_interpreter_value* stack)
{
uint8_t v_flb_539_ = stack[1].m_num;
lean_object* v_items_540_ = stack[2].m_obj;
lean_object* v_gs_541_ = stack[3].m_obj;
lean_object* v_w_542_ = stack[4].m_obj;
lean_object* v_inst_543_ = stack[5].m_obj;
lean_object* v_inst_544_ = stack[6].m_obj;
lean_object* v_res_546_;
v_res_546_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(lean_box(0), v_flb_539_, v_items_540_, v_gs_541_, v_w_542_, v_inst_543_, v_inst_544_);
stack->m_obj
 = v_res_546_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___boxed(lean_object* v_m_547_, lean_object* v_flb_548_, lean_object* v_items_549_, lean_object* v_gs_550_, lean_object* v_w_551_, lean_object* v_inst_552_, lean_object* v_inst_553_){
_start:
{
uint8_t v_flb_boxed_554_; lean_object* v_res_555_; 
v_flb_boxed_554_ = lean_unbox(v_flb_548_);
v_res_555_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup(v_m_547_, v_flb_boxed_554_, v_items_549_, v_gs_550_, v_w_551_, v_inst_552_, v_inst_553_);
return v_res_555_;
}
}
lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(lean_object* v_fla_556_, uint8_t v_flb_557_, lean_object* v_tail_558_, lean_object* v_is_x27_559_){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_560_, 0, v_fla_556_);
lean_ctor_set(v___x_560_, 1, v_is_x27_559_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*2, v_flb_557_);
v___x_561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v_tail_558_);
return v___x_561_;
}
}
LEAN_EXPORT void l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fla_556_ = stack[0].m_obj;
uint8_t v_flb_557_ = stack[1].m_num;
lean_object* v_tail_558_ = stack[2].m_obj;
lean_object* v_is_x27_559_ = stack[3].m_obj;
lean_object* v_res_562_;
v_res_562_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_556_, v_flb_557_, v_tail_558_, v_is_x27_559_);
stack->m_obj
 = v_res_562_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed(lean_object* v_fla_563_, lean_object* v_flb_564_, lean_object* v_tail_565_, lean_object* v_is_x27_566_){
_start:
{
uint8_t v_flb_1440__boxed_567_; lean_object* v_res_568_; 
v_flb_1440__boxed_567_ = lean_unbox(v_flb_564_);
v_res_568_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_563_, v_flb_1440__boxed_567_, v_tail_565_, v_is_x27_566_);
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
lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(uint8_t v_flb_634_, lean_object* v_tail_635_, lean_object* v_tail_636_, lean_object* v_w_637_, lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_toBind_640_, lean_object* v_____r_641_){
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
LEAN_EXPORT void l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
uint8_t v_flb_634_ = stack[0].m_num;
lean_object* v_tail_635_ = stack[1].m_obj;
lean_object* v_tail_636_ = stack[2].m_obj;
lean_object* v_w_637_ = stack[3].m_obj;
lean_object* v_inst_638_ = stack[4].m_obj;
lean_object* v_inst_639_ = stack[5].m_obj;
lean_object* v_toBind_640_ = stack[6].m_obj;
lean_object* v_____r_641_ = stack[7].m_obj;
lean_object* v_res_645_;
v_res_645_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(v_flb_634_, v_tail_635_, v_tail_636_, v_w_637_, v_inst_638_, v_inst_639_, v_toBind_640_, v_____r_641_);
stack->m_obj
 = v_res_645_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed(lean_object* v_flb_646_, lean_object* v_tail_647_, lean_object* v_tail_648_, lean_object* v_w_649_, lean_object* v_inst_650_, lean_object* v_inst_651_, lean_object* v_toBind_652_, lean_object* v_____r_653_){
_start:
{
uint8_t v_flb_1574__boxed_654_; lean_object* v_res_655_; 
v_flb_1574__boxed_654_ = lean_unbox(v_flb_646_);
v_res_655_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(v_flb_1574__boxed_654_, v_tail_647_, v_tail_648_, v_w_649_, v_inst_650_, v_inst_651_, v_toBind_652_, v_____r_653_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(lean_object* v_breakHere_657_, lean_object* v_w_658_, lean_object* v_inst_659_, lean_object* v_inst_660_, lean_object* v_endTags_661_, lean_object* v_activeTags_662_, lean_object* v_toBind_663_, lean_object* v_pushOutput_664_, lean_object* v___x_665_, lean_object* v___x_666_, lean_object* v_____x_667_){
_start:
{
if (lean_obj_tag(v_____x_667_) == 1)
{
lean_object* v_head_668_; lean_object* v_fla_669_; uint8_t v___x_670_; 
v_head_668_ = lean_ctor_get(v_____x_667_, 0);
v_fla_669_ = lean_ctor_get(v_head_668_, 0);
v___x_670_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_669_);
if (v___x_670_ == 0)
{
lean_dec_ref_known(v_____x_667_, 2);
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
lean_object* v___f_671_; lean_object* v___f_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___f_671_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4), 5, 4);
lean_closure_set(v___f_671_, 0, v_w_658_);
lean_closure_set(v___f_671_, 1, v_inst_659_);
lean_closure_set(v___f_671_, 2, v_inst_660_);
lean_closure_set(v___f_671_, 3, v_____x_667_);
lean_inc(v_toBind_663_);
v___f_672_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_672_, 0, v_endTags_661_);
lean_closure_set(v___f_672_, 1, v_activeTags_662_);
lean_closure_set(v___f_672_, 2, v_toBind_663_);
lean_closure_set(v___f_672_, 3, v___f_671_);
v___x_673_ = lean_apply_1(v_pushOutput_664_, v___x_665_);
v___x_674_ = lean_apply_4(v_toBind_663_, lean_box(0), lean_box(0), v___x_673_, v___f_672_);
return v___x_674_;
}
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v_____x_667_);
lean_dec_ref(v___x_665_);
lean_dec(v_pushOutput_664_);
lean_dec(v_toBind_663_);
lean_dec(v_activeTags_662_);
lean_dec(v_endTags_661_);
lean_dec_ref(v_inst_660_);
lean_dec_ref(v_inst_659_);
lean_dec(v_w_658_);
v___x_675_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0));
v___x_676_ = l_panic___redArg(v___x_666_, v___x_675_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed(lean_object* v_breakHere_677_, lean_object* v_w_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_endTags_681_, lean_object* v_activeTags_682_, lean_object* v_toBind_683_, lean_object* v_pushOutput_684_, lean_object* v___x_685_, lean_object* v___x_686_, lean_object* v_____x_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6(v_breakHere_677_, v_w_678_, v_inst_679_, v_inst_680_, v_endTags_681_, v_activeTags_682_, v_toBind_683_, v_pushOutput_684_, v___x_685_, v___x_686_, v_____x_687_);
lean_dec(v___x_686_);
lean_dec(v_breakHere_677_);
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
lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(lean_object* v_a_691_, lean_object* v_p_692_, lean_object* v___x_693_, lean_object* v_indent_694_, lean_object* v_activeTags_695_, lean_object* v_tail_696_, lean_object* v_fla_697_, uint8_t v_flb_698_, lean_object* v_tail_699_, lean_object* v_w_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_toBind_703_, lean_object* v_gs_x27_704_, lean_object* v_____r_705_){
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
LEAN_EXPORT void l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_691_ = stack[0].m_obj;
lean_object* v_p_692_ = stack[1].m_obj;
lean_object* v___x_693_ = stack[2].m_obj;
lean_object* v_indent_694_ = stack[3].m_obj;
lean_object* v_activeTags_695_ = stack[4].m_obj;
lean_object* v_tail_696_ = stack[5].m_obj;
lean_object* v_fla_697_ = stack[6].m_obj;
uint8_t v_flb_698_ = stack[7].m_num;
lean_object* v_tail_699_ = stack[8].m_obj;
lean_object* v_w_700_ = stack[9].m_obj;
lean_object* v_inst_701_ = stack[10].m_obj;
lean_object* v_inst_702_ = stack[11].m_obj;
lean_object* v_toBind_703_ = stack[12].m_obj;
lean_object* v_gs_x27_704_ = stack[13].m_obj;
lean_object* v_____r_705_ = stack[14].m_obj;
lean_object* v_res_718_;
v_res_718_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(v_a_691_, v_p_692_, v___x_693_, v_indent_694_, v_activeTags_695_, v_tail_696_, v_fla_697_, v_flb_698_, v_tail_699_, v_w_700_, v_inst_701_, v_inst_702_, v_toBind_703_, v_gs_x27_704_, v_____r_705_);
stack->m_obj
 = v_res_718_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed(lean_object* v_a_719_, lean_object* v_p_720_, lean_object* v___x_721_, lean_object* v_indent_722_, lean_object* v_activeTags_723_, lean_object* v_tail_724_, lean_object* v_fla_725_, lean_object* v_flb_726_, lean_object* v_tail_727_, lean_object* v_w_728_, lean_object* v_inst_729_, lean_object* v_inst_730_, lean_object* v_toBind_731_, lean_object* v_gs_x27_732_, lean_object* v_____r_733_){
_start:
{
uint8_t v_flb_1598__boxed_734_; lean_object* v_res_735_; 
v_flb_1598__boxed_734_ = lean_unbox(v_flb_726_);
v_res_735_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(v_a_719_, v_p_720_, v___x_721_, v_indent_722_, v_activeTags_723_, v_tail_724_, v_fla_725_, v_flb_1598__boxed_734_, v_tail_727_, v_w_728_, v_inst_729_, v_inst_730_, v_toBind_731_, v_gs_x27_732_, v_____r_733_);
lean_dec(v_fla_725_);
lean_dec(v___x_721_);
lean_dec(v_p_720_);
lean_dec_ref(v_a_719_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(lean_object* v_activeTags_736_, lean_object* v_a_737_, lean_object* v_indent_738_, lean_object* v_tail_739_, lean_object* v_gs_x27_740_, lean_object* v_w_741_, lean_object* v_inst_742_, lean_object* v_inst_743_, lean_object* v_____r_744_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_745_ = lean_unsigned_to_nat(1u);
v___x_746_ = lean_nat_add(v_activeTags_736_, v___x_745_);
v___x_747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_747_, 0, v_a_737_);
lean_ctor_set(v___x_747_, 1, v_indent_738_);
lean_ctor_set(v___x_747_, 2, v___x_746_);
v___x_748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
lean_ctor_set(v___x_748_, 1, v_tail_739_);
v___x_749_ = lean_apply_1(v_gs_x27_740_, v___x_748_);
v___x_750_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_741_, v_inst_742_, v_inst_743_, v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed(lean_object* v_activeTags_751_, lean_object* v_a_752_, lean_object* v_indent_753_, lean_object* v_tail_754_, lean_object* v_gs_x27_755_, lean_object* v_w_756_, lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_____r_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12(v_activeTags_751_, v_a_752_, v_indent_753_, v_tail_754_, v_gs_x27_755_, v_w_756_, v_inst_757_, v_inst_758_, v_____r_759_);
lean_dec(v_activeTags_751_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(lean_object* v_w_761_, lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_x_764_){
_start:
{
if (lean_obj_tag(v_x_764_) == 0)
{
lean_object* v_toApplicative_765_; lean_object* v_toPure_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_toApplicative_765_ = lean_ctor_get(v_inst_762_, 0);
lean_inc_ref(v_toApplicative_765_);
lean_dec_ref(v_inst_763_);
lean_dec_ref(v_inst_762_);
lean_dec(v_w_761_);
v_toPure_766_ = lean_ctor_get(v_toApplicative_765_, 1);
lean_inc(v_toPure_766_);
lean_dec_ref(v_toApplicative_765_);
v___x_767_ = lean_box(0);
v___x_768_ = lean_apply_2(v_toPure_766_, lean_box(0), v___x_767_);
return v___x_768_;
}
else
{
lean_object* v_head_769_; lean_object* v_items_770_; 
v_head_769_ = lean_ctor_get(v_x_764_, 0);
v_items_770_ = lean_ctor_get(v_head_769_, 1);
lean_inc(v_items_770_);
if (lean_obj_tag(v_items_770_) == 0)
{
lean_object* v_tail_771_; 
v_tail_771_ = lean_ctor_get(v_x_764_, 1);
lean_inc(v_tail_771_);
lean_dec_ref_known(v_x_764_, 2);
v_x_764_ = v_tail_771_;
goto _start;
}
else
{
lean_object* v_head_773_; lean_object* v_toBind_774_; lean_object* v_tail_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_920_; 
lean_inc(v_head_769_);
v_head_773_ = lean_ctor_get(v_items_770_, 0);
lean_inc(v_head_773_);
v_toBind_774_ = lean_ctor_get(v_inst_762_, 1);
v_tail_775_ = lean_ctor_get(v_x_764_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_x_764_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v_x_764_, 0);
lean_dec(v_unused_921_);
v___x_777_ = v_x_764_;
v_isShared_778_ = v_isSharedCheck_920_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_tail_775_);
lean_dec(v_x_764_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_920_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_fla_779_; uint8_t v_flb_780_; lean_object* v_tail_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_918_; 
v_fla_779_ = lean_ctor_get(v_head_769_, 0);
lean_inc(v_fla_779_);
v_flb_780_ = lean_ctor_get_uint8(v_head_769_, sizeof(void*)*2);
lean_dec(v_head_769_);
v_tail_781_ = lean_ctor_get(v_items_770_, 1);
v_isSharedCheck_918_ = !lean_is_exclusive(v_items_770_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v_items_770_, 0);
lean_dec(v_unused_919_);
v___x_783_ = v_items_770_;
v_isShared_784_ = v_isSharedCheck_918_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_tail_781_);
lean_dec(v_items_770_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_918_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v_f_785_; lean_object* v_indent_786_; lean_object* v_activeTags_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_917_; 
v_f_785_ = lean_ctor_get(v_head_773_, 0);
v_indent_786_ = lean_ctor_get(v_head_773_, 1);
v_activeTags_787_ = lean_ctor_get(v_head_773_, 2);
v_isSharedCheck_917_ = !lean_is_exclusive(v_head_773_);
if (v_isSharedCheck_917_ == 0)
{
v___x_789_ = v_head_773_;
v_isShared_790_ = v_isSharedCheck_917_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_activeTags_787_);
lean_inc(v_indent_786_);
lean_inc(v_f_785_);
lean_dec(v_head_773_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_917_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v_gs_x27_792_; 
v___x_791_ = lean_box(v_flb_780_);
lean_inc(v_tail_775_);
lean_inc(v_fla_779_);
v_gs_x27_792_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v_gs_x27_792_, 0, v_fla_779_);
lean_closure_set(v_gs_x27_792_, 1, v___x_791_);
lean_closure_set(v_gs_x27_792_, 2, v_tail_775_);
switch(lean_obj_tag(v_f_785_))
{
case 0:
{
lean_object* v_endTags_793_; lean_object* v___f_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
lean_inc(v_toBind_774_);
lean_del_object(v___x_789_);
lean_dec(v_indent_786_);
lean_del_object(v___x_783_);
lean_dec(v_fla_779_);
lean_del_object(v___x_777_);
lean_dec(v_tail_775_);
v_endTags_793_ = lean_ctor_get(v_inst_763_, 4);
lean_inc(v_endTags_793_);
v___f_794_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_794_, 0, v_gs_x27_792_);
lean_closure_set(v___f_794_, 1, v_tail_781_);
lean_closure_set(v___f_794_, 2, v_w_761_);
lean_closure_set(v___f_794_, 3, v_inst_762_);
lean_closure_set(v___f_794_, 4, v_inst_763_);
v___x_795_ = lean_apply_1(v_endTags_793_, v_activeTags_787_);
v___x_796_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_795_, v___f_794_);
return v___x_796_;
}
case 1:
{
lean_inc(v_toBind_774_);
lean_del_object(v___x_789_);
lean_del_object(v___x_783_);
lean_del_object(v___x_777_);
if (v_flb_780_ == 0)
{
uint8_t v___x_797_; 
lean_dec(v_tail_775_);
v___x_797_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_779_);
lean_dec(v_fla_779_);
if (v___x_797_ == 0)
{
lean_object* v_pushNewline_798_; lean_object* v_endTags_799_; lean_object* v___f_800_; lean_object* v___f_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_pushNewline_798_ = lean_ctor_get(v_inst_763_, 1);
lean_inc(v_pushNewline_798_);
v_endTags_799_ = lean_ctor_get(v_inst_763_, 4);
lean_inc(v_endTags_799_);
v___f_800_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_800_, 0, v_gs_x27_792_);
lean_closure_set(v___f_800_, 1, v_tail_781_);
lean_closure_set(v___f_800_, 2, v_w_761_);
lean_closure_set(v___f_800_, 3, v_inst_762_);
lean_closure_set(v___f_800_, 4, v_inst_763_);
lean_inc(v_toBind_774_);
v___f_801_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_801_, 0, v_endTags_799_);
lean_closure_set(v___f_801_, 1, v_activeTags_787_);
lean_closure_set(v___f_801_, 2, v_toBind_774_);
lean_closure_set(v___f_801_, 3, v___f_800_);
v___x_802_ = l_Int_toNat(v_indent_786_);
lean_dec(v_indent_786_);
v___x_803_ = lean_apply_1(v_pushNewline_798_, v___x_802_);
v___x_804_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_803_, v___f_801_);
return v___x_804_;
}
else
{
lean_object* v_pushOutput_805_; lean_object* v_endTags_806_; lean_object* v___f_807_; lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec(v_indent_786_);
v_pushOutput_805_ = lean_ctor_get(v_inst_763_, 0);
lean_inc(v_pushOutput_805_);
v_endTags_806_ = lean_ctor_get(v_inst_763_, 4);
lean_inc(v_endTags_806_);
v___f_807_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_807_, 0, v_gs_x27_792_);
lean_closure_set(v___f_807_, 1, v_tail_781_);
lean_closure_set(v___f_807_, 2, v_w_761_);
lean_closure_set(v___f_807_, 3, v_inst_762_);
lean_closure_set(v___f_807_, 4, v_inst_763_);
lean_inc(v_toBind_774_);
v___f_808_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_808_, 0, v_endTags_806_);
lean_closure_set(v___f_808_, 1, v_activeTags_787_);
lean_closure_set(v___f_808_, 2, v_toBind_774_);
lean_closure_set(v___f_808_, 3, v___f_807_);
v___x_809_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_810_ = lean_apply_1(v_pushOutput_805_, v___x_809_);
v___x_811_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_810_, v___f_808_);
return v___x_811_;
}
}
else
{
lean_object* v_pushOutput_812_; lean_object* v_pushNewline_813_; lean_object* v_endTags_814_; lean_object* v___x_815_; lean_object* v___f_816_; lean_object* v___f_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_breakHere_820_; uint8_t v___x_821_; 
lean_dec_ref(v_gs_x27_792_);
v_pushOutput_812_ = lean_ctor_get(v_inst_763_, 0);
v_pushNewline_813_ = lean_ctor_get(v_inst_763_, 1);
v_endTags_814_ = lean_ctor_get(v_inst_763_, 4);
v___x_815_ = lean_box(v_flb_780_);
lean_inc_n(v_toBind_774_, 3);
lean_inc_ref(v_inst_763_);
lean_inc_ref(v_inst_762_);
lean_inc(v_w_761_);
lean_inc(v_tail_775_);
lean_inc(v_tail_781_);
v___f_816_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_816_, 0, v___x_815_);
lean_closure_set(v___f_816_, 1, v_tail_781_);
lean_closure_set(v___f_816_, 2, v_tail_775_);
lean_closure_set(v___f_816_, 3, v_w_761_);
lean_closure_set(v___f_816_, 4, v_inst_762_);
lean_closure_set(v___f_816_, 5, v_inst_763_);
lean_closure_set(v___f_816_, 6, v_toBind_774_);
lean_inc(v_activeTags_787_);
lean_inc(v_endTags_814_);
v___f_817_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_817_, 0, v_endTags_814_);
lean_closure_set(v___f_817_, 1, v_activeTags_787_);
lean_closure_set(v___f_817_, 2, v_toBind_774_);
lean_closure_set(v___f_817_, 3, v___f_816_);
v___x_818_ = l_Int_toNat(v_indent_786_);
lean_dec(v_indent_786_);
lean_inc(v_pushNewline_813_);
v___x_819_ = lean_apply_1(v_pushNewline_813_, v___x_818_);
v_breakHere_820_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_819_, v___f_817_);
v___x_821_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_779_);
lean_dec(v_fla_779_);
if (v___x_821_ == 0)
{
lean_dec(v_activeTags_787_);
lean_dec(v_tail_781_);
lean_dec(v_tail_775_);
lean_dec(v_toBind_774_);
lean_dec_ref(v_inst_763_);
lean_dec_ref(v_inst_762_);
lean_dec(v_w_761_);
return v_breakHere_820_;
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___f_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_822_ = lean_box(0);
lean_inc_ref_n(v_inst_762_, 2);
v___x_823_ = l_instInhabitedOfMonad___redArg(v_inst_762_, v___x_822_);
v___x_824_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
lean_inc(v_pushOutput_812_);
lean_inc(v_toBind_774_);
lean_inc(v_endTags_814_);
lean_inc_ref(v_inst_763_);
lean_inc(v_w_761_);
v___f_825_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___boxed), 11, 10);
lean_closure_set(v___f_825_, 0, v_breakHere_820_);
lean_closure_set(v___f_825_, 1, v_w_761_);
lean_closure_set(v___f_825_, 2, v_inst_762_);
lean_closure_set(v___f_825_, 3, v_inst_763_);
lean_closure_set(v___f_825_, 4, v_endTags_814_);
lean_closure_set(v___f_825_, 5, v_activeTags_787_);
lean_closure_set(v___f_825_, 6, v_toBind_774_);
lean_closure_set(v___f_825_, 7, v_pushOutput_812_);
lean_closure_set(v___f_825_, 8, v___x_824_);
lean_closure_set(v___f_825_, 9, v___x_823_);
v___x_826_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_827_ = lean_nat_sub(v_w_761_, v___x_826_);
lean_dec(v_w_761_);
v___x_828_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_flb_780_, v_tail_781_, v_tail_775_, v___x_827_, v_inst_762_, v_inst_763_);
v___x_829_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_828_, v___f_825_);
return v___x_829_;
}
}
}
case 2:
{
uint8_t v_force_830_; lean_object* v___f_831_; lean_object* v___f_832_; lean_object* v___f_833_; uint8_t v___y_838_; uint8_t v___x_842_; 
lean_inc_n(v_toBind_774_, 3);
lean_del_object(v___x_789_);
lean_del_object(v___x_783_);
lean_del_object(v___x_777_);
lean_dec(v_tail_775_);
v_force_830_ = lean_ctor_get_uint8(v_f_785_, 0);
lean_dec_ref_known(v_f_785_, 0);
lean_inc_ref_n(v_inst_763_, 3);
v___f_831_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_831_, 0, v_gs_x27_792_);
lean_closure_set(v___f_831_, 1, v_tail_781_);
lean_closure_set(v___f_831_, 2, v_w_761_);
lean_closure_set(v___f_831_, 3, v_inst_762_);
lean_closure_set(v___f_831_, 4, v_inst_763_);
lean_inc_ref(v___f_831_);
lean_inc(v_activeTags_787_);
v___f_832_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9), 5, 4);
lean_closure_set(v___f_832_, 0, v_inst_763_);
lean_closure_set(v___f_832_, 1, v_activeTags_787_);
lean_closure_set(v___f_832_, 2, v_toBind_774_);
lean_closure_set(v___f_832_, 3, v___f_831_);
lean_inc_ref(v___f_832_);
v___f_833_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed), 6, 5);
lean_closure_set(v___f_833_, 0, v_indent_786_);
lean_closure_set(v___f_833_, 1, v_inst_763_);
lean_closure_set(v___f_833_, 2, v_toBind_774_);
lean_closure_set(v___f_833_, 3, v___f_832_);
lean_closure_set(v___f_833_, 4, v___f_832_);
v___x_842_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_779_);
lean_dec(v_fla_779_);
if (v___x_842_ == 0)
{
v___y_838_ = v___x_842_;
goto v___jp_837_;
}
else
{
if (v_force_830_ == 0)
{
v___y_838_ = v___x_842_;
goto v___jp_837_;
}
else
{
lean_dec_ref(v___f_831_);
lean_dec(v_activeTags_787_);
goto v___jp_834_;
}
}
v___jp_834_:
{
lean_object* v_currColumn_835_; lean_object* v___x_836_; 
v_currColumn_835_ = lean_ctor_get(v_inst_763_, 2);
lean_inc(v_currColumn_835_);
lean_dec_ref(v_inst_763_);
v___x_836_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v_currColumn_835_, v___f_833_);
return v___x_836_;
}
v___jp_837_:
{
if (v___y_838_ == 0)
{
lean_dec_ref(v___f_831_);
lean_dec(v_activeTags_787_);
goto v___jp_834_;
}
else
{
lean_object* v_endTags_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec_ref(v___f_833_);
v_endTags_839_ = lean_ctor_get(v_inst_763_, 4);
lean_inc(v_endTags_839_);
lean_dec_ref(v_inst_763_);
v___x_840_ = lean_apply_1(v_endTags_839_, v_activeTags_787_);
v___x_841_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_840_, v___f_831_);
return v___x_841_;
}
}
}
case 3:
{
lean_object* v_a_843_; uint32_t v___x_844_; lean_object* v_p_845_; lean_object* v___x_846_; uint8_t v_decide_847_; 
lean_inc(v_toBind_774_);
lean_del_object(v___x_789_);
lean_del_object(v___x_783_);
lean_del_object(v___x_777_);
v_a_843_ = lean_ctor_get(v_f_785_, 0);
lean_inc_ref_n(v_a_843_, 2);
lean_dec_ref_known(v_f_785_, 1);
v___x_844_ = 10;
v_p_845_ = lean_string_posof(v_a_843_, v___x_844_);
v___x_846_ = lean_string_utf8_byte_size(v_a_843_);
v_decide_847_ = lean_nat_dec_eq(v_p_845_, v___x_846_);
if (v_decide_847_ == 0)
{
lean_object* v_pushOutput_848_; lean_object* v_pushNewline_849_; lean_object* v___x_850_; lean_object* v___f_851_; lean_object* v___f_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v_pushOutput_848_ = lean_ctor_get(v_inst_763_, 0);
lean_inc(v_pushOutput_848_);
v_pushNewline_849_ = lean_ctor_get(v_inst_763_, 1);
lean_inc(v_pushNewline_849_);
v___x_850_ = lean_box(v_flb_780_);
lean_inc_n(v_toBind_774_, 2);
lean_inc(v_indent_786_);
lean_inc(v_p_845_);
lean_inc_ref(v_a_843_);
v___f_851_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed), 15, 14);
lean_closure_set(v___f_851_, 0, v_a_843_);
lean_closure_set(v___f_851_, 1, v_p_845_);
lean_closure_set(v___f_851_, 2, v___x_846_);
lean_closure_set(v___f_851_, 3, v_indent_786_);
lean_closure_set(v___f_851_, 4, v_activeTags_787_);
lean_closure_set(v___f_851_, 5, v_tail_781_);
lean_closure_set(v___f_851_, 6, v_fla_779_);
lean_closure_set(v___f_851_, 7, v___x_850_);
lean_closure_set(v___f_851_, 8, v_tail_775_);
lean_closure_set(v___f_851_, 9, v_w_761_);
lean_closure_set(v___f_851_, 10, v_inst_762_);
lean_closure_set(v___f_851_, 11, v_inst_763_);
lean_closure_set(v___f_851_, 12, v_toBind_774_);
lean_closure_set(v___f_851_, 13, v_gs_x27_792_);
v___f_852_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_852_, 0, v_indent_786_);
lean_closure_set(v___f_852_, 1, v_pushNewline_849_);
lean_closure_set(v___f_852_, 2, v_toBind_774_);
lean_closure_set(v___f_852_, 3, v___f_851_);
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = lean_string_utf8_extract(v_a_843_, v___x_853_, v_p_845_);
lean_dec(v_p_845_);
lean_dec_ref(v_a_843_);
v___x_855_ = lean_apply_1(v_pushOutput_848_, v___x_854_);
v___x_856_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_855_, v___f_852_);
return v___x_856_;
}
else
{
lean_object* v_pushOutput_857_; lean_object* v_endTags_858_; lean_object* v___f_859_; lean_object* v___f_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
lean_dec(v_p_845_);
lean_dec(v_indent_786_);
lean_dec(v_fla_779_);
lean_dec(v_tail_775_);
v_pushOutput_857_ = lean_ctor_get(v_inst_763_, 0);
lean_inc(v_pushOutput_857_);
v_endTags_858_ = lean_ctor_get(v_inst_763_, 4);
lean_inc(v_endTags_858_);
v___f_859_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_859_, 0, v_gs_x27_792_);
lean_closure_set(v___f_859_, 1, v_tail_781_);
lean_closure_set(v___f_859_, 2, v_w_761_);
lean_closure_set(v___f_859_, 3, v_inst_762_);
lean_closure_set(v___f_859_, 4, v_inst_763_);
lean_inc(v_toBind_774_);
v___f_860_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_860_, 0, v_endTags_858_);
lean_closure_set(v___f_860_, 1, v_activeTags_787_);
lean_closure_set(v___f_860_, 2, v_toBind_774_);
lean_closure_set(v___f_860_, 3, v___f_859_);
v___x_861_ = lean_apply_1(v_pushOutput_857_, v_a_843_);
v___x_862_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_861_, v___f_860_);
return v___x_862_;
}
}
case 4:
{
lean_object* v_indent_863_; lean_object* v_f_864_; lean_object* v___x_865_; lean_object* v___x_867_; 
lean_dec_ref(v_gs_x27_792_);
lean_del_object(v___x_777_);
v_indent_863_ = lean_ctor_get(v_f_785_, 0);
lean_inc(v_indent_863_);
v_f_864_ = lean_ctor_get(v_f_785_, 1);
lean_inc(v_f_864_);
lean_dec_ref_known(v_f_785_, 2);
v___x_865_ = lean_int_add(v_indent_786_, v_indent_863_);
lean_dec(v_indent_863_);
lean_dec(v_indent_786_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 1, v___x_865_);
lean_ctor_set(v___x_789_, 0, v_f_864_);
v___x_867_ = v___x_789_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_f_864_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_873_, 2, v_activeTags_787_);
v___x_867_ = v_reuseFailAlloc_873_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_869_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_867_);
v___x_869_ = v___x_783_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_tail_781_);
v___x_869_ = v_reuseFailAlloc_872_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; 
v___x_870_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_779_, v_flb_780_, v_tail_775_, v___x_869_);
v_x_764_ = v___x_870_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_874_; lean_object* v_a_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
lean_dec_ref(v_gs_x27_792_);
v_a_874_ = lean_ctor_get(v_f_785_, 0);
lean_inc(v_a_874_);
v_a_875_ = lean_ctor_get(v_f_785_, 1);
lean_inc(v_a_875_);
lean_dec_ref_known(v_f_785_, 2);
v___x_876_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_786_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 2, v___x_876_);
lean_ctor_set(v___x_789_, 0, v_a_874_);
v___x_878_ = v___x_789_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_874_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_indent_786_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v___x_876_);
v___x_878_ = v_reuseFailAlloc_888_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_879_, 0, v_a_875_);
lean_ctor_set(v___x_879_, 1, v_indent_786_);
lean_ctor_set(v___x_879_, 2, v_activeTags_787_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_879_);
v___x_881_ = v___x_783_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_tail_781_);
v___x_881_ = v_reuseFailAlloc_887_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_883_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v___x_881_);
lean_ctor_set(v___x_777_, 0, v___x_878_);
v___x_883_ = v___x_777_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v___x_881_);
v___x_883_ = v_reuseFailAlloc_886_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; 
v___x_884_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_779_, v_flb_780_, v_tail_775_, v___x_883_);
v_x_764_ = v___x_884_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_889_; uint8_t v_behavior_890_; uint8_t v___x_891_; 
lean_dec_ref(v_gs_x27_792_);
lean_del_object(v___x_777_);
v_a_889_ = lean_ctor_get(v_f_785_, 0);
lean_inc(v_a_889_);
v_behavior_890_ = lean_ctor_get_uint8(v_f_785_, sizeof(void*)*1);
lean_dec_ref_known(v_f_785_, 1);
v___x_891_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_779_);
if (v___x_891_ == 0)
{
lean_object* v___x_893_; 
lean_inc(v_toBind_774_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v_a_889_);
v___x_893_ = v___x_789_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_889_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_indent_786_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_activeTags_787_);
v___x_893_ = v_reuseFailAlloc_902_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_894_ = lean_box(0);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v___x_894_);
lean_ctor_set(v___x_783_, 0, v___x_893_);
v___x_896_ = v___x_783_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v___x_894_);
v___x_896_ = v_reuseFailAlloc_901_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_897_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_779_, v_flb_780_, v_tail_775_, v_tail_781_);
lean_inc_ref(v_inst_763_);
lean_inc_ref(v_inst_762_);
lean_inc(v_w_761_);
v___x_898_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_behavior_890_, v___x_896_, v___x_897_, v_w_761_, v_inst_762_, v_inst_763_);
v___x_899_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_899_, 0, v_w_761_);
lean_closure_set(v___x_899_, 1, v_inst_762_);
lean_closure_set(v___x_899_, 2, v_inst_763_);
v___x_900_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_898_, v___x_899_);
return v___x_900_;
}
}
}
else
{
lean_object* v___x_904_; 
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v_a_889_);
v___x_904_ = v___x_789_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_889_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_indent_786_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_activeTags_787_);
v___x_904_ = v_reuseFailAlloc_910_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_906_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_904_);
v___x_906_ = v___x_783_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_tail_781_);
v___x_906_ = v_reuseFailAlloc_909_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; 
v___x_907_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_779_, v_flb_780_, v_tail_775_, v___x_906_);
v_x_764_ = v___x_907_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_911_; lean_object* v_a_912_; lean_object* v_startTag_913_; lean_object* v___f_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
lean_inc(v_toBind_774_);
lean_del_object(v___x_789_);
lean_del_object(v___x_783_);
lean_dec(v_fla_779_);
lean_del_object(v___x_777_);
lean_dec(v_tail_775_);
v_a_911_ = lean_ctor_get(v_f_785_, 0);
lean_inc(v_a_911_);
v_a_912_ = lean_ctor_get(v_f_785_, 1);
lean_inc(v_a_912_);
lean_dec_ref_known(v_f_785_, 2);
v_startTag_913_ = lean_ctor_get(v_inst_763_, 3);
lean_inc(v_startTag_913_);
v___f_914_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed), 9, 8);
lean_closure_set(v___f_914_, 0, v_activeTags_787_);
lean_closure_set(v___f_914_, 1, v_a_912_);
lean_closure_set(v___f_914_, 2, v_indent_786_);
lean_closure_set(v___f_914_, 3, v_tail_781_);
lean_closure_set(v___f_914_, 4, v_gs_x27_792_);
lean_closure_set(v___f_914_, 5, v_w_761_);
lean_closure_set(v___f_914_, 6, v_inst_762_);
lean_closure_set(v___f_914_, 7, v_inst_763_);
v___x_915_ = lean_apply_1(v_startTag_913_, v_a_911_);
v___x_916_ = lean_apply_4(v_toBind_774_, lean_box(0), lean_box(0), v___x_915_, v___f_914_);
return v___x_916_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4(lean_object* v_w_922_, lean_object* v_inst_923_, lean_object* v_inst_924_, lean_object* v_____x_925_, lean_object* v_____r_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_922_, v_inst_923_, v_inst_924_, v_____x_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be(lean_object* v_m_928_, lean_object* v_w_929_, lean_object* v_inst_930_, lean_object* v_inst_931_, lean_object* v_x_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_929_, v_inst_930_, v_inst_931_, v_x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___redArg(lean_object* v_f_934_, lean_object* v_w_935_, lean_object* v_indent_936_, lean_object* v_inst_937_, lean_object* v_inst_938_){
_start:
{
lean_object* v___x_939_; uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_939_ = lean_box(1);
v___x_940_ = 0;
v___x_941_ = lean_nat_to_int(v_indent_936_);
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_943_, 0, v_f_934_);
lean_ctor_set(v___x_943_, 1, v___x_941_);
lean_ctor_set(v___x_943_, 2, v___x_942_);
v___x_944_ = lean_box(0);
v___x_945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_946_, 0, v___x_939_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
lean_ctor_set_uint8(v___x_946_, sizeof(void*)*2, v___x_940_);
v___x_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v___x_944_);
v___x_948_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_935_, v_inst_937_, v_inst_938_, v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM(lean_object* v_m_949_, lean_object* v_f_950_, lean_object* v_w_951_, lean_object* v_indent_952_, lean_object* v_inst_953_, lean_object* v_inst_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_Format_prettyM___redArg(v_f_950_, v_w_951_, v_indent_952_, v_inst_953_, v_inst_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_bracket(lean_object* v_l_956_, lean_object* v_f_957_, lean_object* v_r_958_){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; lean_object* v___x_967_; 
v___x_959_ = lean_string_length(v_l_956_);
v___x_960_ = lean_nat_to_int(v___x_959_);
v___x_961_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_961_, 0, v_l_956_);
v___x_962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set(v___x_962_, 1, v_f_957_);
v___x_963_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_963_, 0, v_r_958_);
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_960_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = 0;
v___x_967_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set_uint8(v___x_967_, sizeof(void*)*1, v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_Std_Format_paren___closed__2(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l_Std_Format_paren___closed__0));
v___x_971_ = lean_string_length(v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l_Std_Format_paren___closed__3(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_obj_once(&l_Std_Format_paren___closed__2, &l_Std_Format_paren___closed__2_once, _init_l_Std_Format_paren___closed__2);
v___x_973_ = lean_nat_to_int(v___x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_paren(lean_object* v_f_978_){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; lean_object* v___x_986_; 
v___x_979_ = lean_obj_once(&l_Std_Format_paren___closed__3, &l_Std_Format_paren___closed__3_once, _init_l_Std_Format_paren___closed__3);
v___x_980_ = ((lean_object*)(l_Std_Format_paren___closed__4));
v___x_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v_f_978_);
v___x_982_ = ((lean_object*)(l_Std_Format_paren___closed__5));
v___x_983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_979_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = 0;
v___x_986_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*1, v___x_985_);
return v___x_986_;
}
}
static lean_object* _init_l_Std_Format_sbracket___closed__2(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Std_Format_sbracket___closed__0));
v___x_990_ = lean_string_length(v___x_989_);
return v___x_990_;
}
}
static lean_object* _init_l_Std_Format_sbracket___closed__3(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_obj_once(&l_Std_Format_sbracket___closed__2, &l_Std_Format_sbracket___closed__2_once, _init_l_Std_Format_sbracket___closed__2);
v___x_992_ = lean_nat_to_int(v___x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_sbracket(lean_object* v_f_997_){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; lean_object* v___x_1005_; 
v___x_998_ = lean_obj_once(&l_Std_Format_sbracket___closed__3, &l_Std_Format_sbracket___closed__3_once, _init_l_Std_Format_sbracket___closed__3);
v___x_999_ = ((lean_object*)(l_Std_Format_sbracket___closed__4));
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v_f_997_);
v___x_1001_ = ((lean_object*)(l_Std_Format_sbracket___closed__5));
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_998_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = 0;
v___x_1005_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set_uint8(v___x_1005_, sizeof(void*)*1, v___x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_bracketFill(lean_object* v_l_1006_, lean_object* v_f_1007_, lean_object* v_r_1008_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1009_ = lean_string_length(v_l_1006_);
v___x_1010_ = lean_nat_to_int(v___x_1009_);
v___x_1011_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1011_, 0, v_l_1006_);
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v_f_1007_);
v___x_1013_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1013_, 0, v_r_1008_);
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1010_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = l_Std_Format_fill(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l_Std_Format_defIndent(void){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_unsigned_to_nat(2u);
return v___x_1017_;
}
}
static uint8_t _init_l_Std_Format_defUnicode(void){
_start:
{
uint8_t v___x_1018_; 
v___x_1018_ = 1;
return v___x_1018_;
}
}
static lean_object* _init_l_Std_Format_defWidth(void){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_unsigned_to_nat(120u);
return v___x_1019_;
}
}
static lean_object* _init_l_Std_Format_nestD___closed__0(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_unsigned_to_nat(2u);
v___x_1021_ = lean_nat_to_int(v___x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nestD(lean_object* v_f_1022_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_obj_once(&l_Std_Format_nestD___closed__0, &l_Std_Format_nestD___closed__0_once, _init_l_Std_Format_nestD___closed__0);
v___x_1024_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v_f_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_indentD(lean_object* v_f_1025_){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = lean_box(1);
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v_f_1025_);
v___x_1028_ = l_Std_Format_nestD(v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(lean_object* v_s_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_out_1031_; lean_object* v_column_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1044_; 
v_out_1031_ = lean_ctor_get(v___y_1030_, 0);
v_column_1032_ = lean_ctor_get(v___y_1030_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___y_1030_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1034_ = v___y_1030_;
v_isShared_1035_ = v_isSharedCheck_1044_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_column_1032_);
lean_inc(v_out_1031_);
lean_dec(v___y_1030_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1044_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1036_ = lean_box(0);
v___x_1037_ = lean_string_append(v_out_1031_, v_s_1029_);
v___x_1038_ = lean_string_length(v_s_1029_);
v___x_1039_ = lean_nat_add(v_column_1032_, v___x_1038_);
lean_dec(v___x_1038_);
lean_dec(v_column_1032_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 1, v___x_1039_);
lean_ctor_set(v___x_1034_, 0, v___x_1037_);
v___x_1041_ = v___x_1034_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1036_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
return v___x_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0___boxed(lean_object* v_s_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(v_s_1045_, v___y_1046_);
lean_dec_ref(v_s_1045_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1(lean_object* v_indent_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_out_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1064_; 
v_out_1051_ = lean_ctor_get(v___y_1050_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___y_1050_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v___y_1050_, 1);
lean_dec(v_unused_1065_);
v___x_1053_ = v___y_1050_;
v_isShared_1054_ = v_isSharedCheck_1064_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_out_1051_);
lean_dec(v___y_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1064_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; uint32_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1055_ = lean_box(0);
v___x_1056_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1057_ = 32;
lean_inc(v_indent_1049_);
v___x_1058_ = lean_string_pushn(v___x_1056_, v___x_1057_, v_indent_1049_);
v___x_1059_ = lean_string_append(v_out_1051_, v___x_1058_);
lean_dec_ref(v___x_1058_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v_indent_1049_);
lean_ctor_set(v___x_1053_, 0, v___x_1059_);
v___x_1061_ = v___x_1053_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_indent_1049_);
v___x_1061_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1055_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
return v___x_1062_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__2(lean_object* v_____do__lift_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_column_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
v_column_1068_ = lean_ctor_get(v_____do__lift_1066_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_____do__lift_1066_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v_____do__lift_1066_, 0);
lean_dec(v_unused_1076_);
v___x_1070_ = v_____do__lift_1066_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_column_1068_);
lean_dec(v_____do__lift_1066_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 1, v___y_1067_);
lean_ctor_set(v___x_1070_, 0, v_column_1068_);
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_column_1068_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___y_1067_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(lean_object* v_x_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_box(0);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v___y_1078_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3___boxed(lean_object* v_x_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(v_x_1081_, v___y_1082_);
lean_dec(v_x_1081_);
return v_res_1083_;
}
}
lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(uint8_t v_flb_1119_, lean_object* v_items_1120_, lean_object* v_gs_1121_, lean_object* v_w_1122_, lean_object* v___y_1123_){
_start:
{
uint8_t v___y_1125_; lean_object* v_column_1130_; uint8_t v___x_1131_; uint8_t v___x_1132_; lean_object* v___x_1133_; lean_object* v_g_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v_r_1138_; lean_object* v___y_1140_; uint8_t v_foundLine_1145_; lean_object* v_space_1146_; uint8_t v___x_1147_; 
v_column_1130_ = lean_ctor_get(v___y_1123_, 1);
v___x_1131_ = 0;
v___x_1132_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_1119_, v___x_1131_);
v___x_1133_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1133_, 0, v___x_1132_);
lean_inc(v_items_1120_);
v_g_1134_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_1134_, 0, v___x_1133_);
lean_ctor_set(v_g_1134_, 1, v_items_1120_);
lean_ctor_set_uint8(v_g_1134_, sizeof(void*)*2, v_flb_1119_);
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1136_, 0, v_g_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = lean_nat_sub(v_w_1122_, v_column_1130_);
lean_inc(v___x_1137_);
lean_inc(v_column_1130_);
v_r_1138_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_1136_, v_column_1130_, v___x_1137_);
v_foundLine_1145_ = lean_ctor_get_uint8(v_r_1138_, sizeof(void*)*1);
v_space_1146_ = lean_ctor_get(v_r_1138_, 0);
v___x_1147_ = lean_nat_dec_lt(v___x_1137_, v_space_1146_);
if (v___x_1147_ == 0)
{
if (v_foundLine_1145_ == 0)
{
lean_object* v___x_1148_; lean_object* v_r_u2082_1149_; uint8_t v_foundLine_1150_; uint8_t v_foundFlattenedHardLine_1151_; lean_object* v_space_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1160_; 
v___x_1148_ = lean_nat_sub(v___x_1137_, v_space_1146_);
lean_inc(v_column_1130_);
lean_inc(v_gs_1121_);
v_r_u2082_1149_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_1121_, v_column_1130_, v___x_1148_);
v_foundLine_1150_ = lean_ctor_get_uint8(v_r_u2082_1149_, sizeof(void*)*1);
v_foundFlattenedHardLine_1151_ = lean_ctor_get_uint8(v_r_u2082_1149_, sizeof(void*)*1 + 1);
v_space_1152_ = lean_ctor_get(v_r_u2082_1149_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_r_u2082_1149_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1154_ = v_r_u2082_1149_;
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_space_1152_);
lean_dec(v_r_u2082_1149_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = lean_nat_add(v_space_1146_, v_space_1152_);
lean_dec(v_space_1152_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1156_);
v___x_1158_ = v___x_1154_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
lean_ctor_set_uint8(v_reuseFailAlloc_1159_, sizeof(void*)*1, v_foundLine_1150_);
lean_ctor_set_uint8(v_reuseFailAlloc_1159_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_1151_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
v___y_1140_ = v___x_1158_;
goto v___jp_1139_;
}
}
}
else
{
lean_inc_ref(v_r_1138_);
v___y_1140_ = v_r_1138_;
goto v___jp_1139_;
}
}
else
{
lean_inc_ref(v_r_1138_);
v___y_1140_ = v_r_1138_;
goto v___jp_1139_;
}
v___jp_1124_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1126_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1126_, 0, v___y_1125_);
v___x_1127_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
lean_ctor_set(v___x_1127_, 1, v_items_1120_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*2, v_flb_1119_);
v___x_1128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v_gs_1121_);
v___x_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v___y_1123_);
return v___x_1129_;
}
v___jp_1139_:
{
uint8_t v_foundFlattenedHardLine_1141_; 
v_foundFlattenedHardLine_1141_ = lean_ctor_get_uint8(v_r_1138_, sizeof(void*)*1 + 1);
lean_dec_ref(v_r_1138_);
if (v_foundFlattenedHardLine_1141_ == 0)
{
lean_object* v_space_1142_; uint8_t v___x_1143_; 
v_space_1142_ = lean_ctor_get(v___y_1140_, 0);
lean_inc(v_space_1142_);
lean_dec_ref(v___y_1140_);
v___x_1143_ = lean_nat_dec_le(v_space_1142_, v___x_1137_);
lean_dec(v___x_1137_);
lean_dec(v_space_1142_);
v___y_1125_ = v___x_1143_;
goto v___jp_1124_;
}
else
{
uint8_t v___x_1144_; 
lean_dec_ref(v___y_1140_);
lean_dec(v___x_1137_);
v___x_1144_ = 0;
v___y_1125_ = v___x_1144_;
goto v___jp_1124_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_flb_1119_ = stack[0].m_num;
lean_object* v_items_1120_ = stack[1].m_obj;
lean_object* v_gs_1121_ = stack[2].m_obj;
lean_object* v_w_1122_ = stack[3].m_obj;
lean_object* v___y_1123_ = stack[4].m_obj;
lean_object* v_res_1161_;
v_res_1161_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1119_, v_items_1120_, v_gs_1121_, v_w_1122_, v___y_1123_);
stack->m_obj
 = v_res_1161_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1___boxed(lean_object* v_flb_1162_, lean_object* v_items_1163_, lean_object* v_gs_1164_, lean_object* v_w_1165_, lean_object* v___y_1166_){
_start:
{
uint8_t v_flb_boxed_1167_; lean_object* v_res_1168_; 
v_flb_boxed_1167_ = lean_unbox(v_flb_1162_);
v_res_1168_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_boxed_1167_, v_items_1163_, v_gs_1164_, v_w_1165_, v___y_1166_);
lean_dec(v_w_1165_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(lean_object* v_msg_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___f_1185_; lean_object* v___f_1186_; lean_object* v___f_1187_; lean_object* v___f_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_4910__overap_1197_; lean_object* v___x_1198_; 
v___f_1185_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0));
v___f_1186_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1));
v___f_1187_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2));
v___f_1188_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3));
v___x_1189_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4));
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
lean_ctor_set(v___x_1190_, 1, v___f_1185_);
v___x_1191_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5));
v___x_1192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
lean_ctor_set(v___x_1192_, 2, v___f_1186_);
lean_ctor_set(v___x_1192_, 3, v___f_1187_);
lean_ctor_set(v___x_1192_, 4, v___f_1188_);
v___x_1193_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6));
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1192_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = lean_box(0);
v___x_1196_ = l_instInhabitedOfMonad___redArg(v___x_1194_, v___x_1195_);
v___x_4910__overap_1197_ = lean_panic_fn_borrowed(v___x_1196_, v_msg_1183_);
lean_dec(v___x_1196_);
v___x_1198_ = lean_apply_1(v___x_4910__overap_1197_, v___y_1184_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(lean_object* v_w_1199_, lean_object* v_x_1200_, lean_object* v___y_1201_){
_start:
{
if (lean_obj_tag(v_x_1200_) == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_box(0);
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
lean_ctor_set(v___x_1203_, 1, v___y_1201_);
return v___x_1203_;
}
else
{
lean_object* v_head_1204_; lean_object* v_items_1205_; 
v_head_1204_ = lean_ctor_get(v_x_1200_, 0);
v_items_1205_ = lean_ctor_get(v_head_1204_, 1);
lean_inc(v_items_1205_);
if (lean_obj_tag(v_items_1205_) == 0)
{
lean_object* v_tail_1206_; 
v_tail_1206_ = lean_ctor_get(v_x_1200_, 1);
lean_inc(v_tail_1206_);
lean_dec_ref_known(v_x_1200_, 2);
v_x_1200_ = v_tail_1206_;
goto _start;
}
else
{
lean_object* v_head_1208_; lean_object* v_tail_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1479_; 
lean_inc(v_head_1204_);
v_head_1208_ = lean_ctor_get(v_items_1205_, 0);
lean_inc(v_head_1208_);
v_tail_1209_ = lean_ctor_get(v_x_1200_, 1);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_x_1200_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; 
v_unused_1480_ = lean_ctor_get(v_x_1200_, 0);
lean_dec(v_unused_1480_);
v___x_1211_ = v_x_1200_;
v_isShared_1212_ = v_isSharedCheck_1479_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_tail_1209_);
lean_dec(v_x_1200_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1479_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v_fla_1213_; uint8_t v_flb_1214_; lean_object* v_tail_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1477_; 
v_fla_1213_ = lean_ctor_get(v_head_1204_, 0);
lean_inc(v_fla_1213_);
v_flb_1214_ = lean_ctor_get_uint8(v_head_1204_, sizeof(void*)*2);
lean_dec(v_head_1204_);
v_tail_1215_ = lean_ctor_get(v_items_1205_, 1);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_items_1205_);
if (v_isSharedCheck_1477_ == 0)
{
lean_object* v_unused_1478_; 
v_unused_1478_ = lean_ctor_get(v_items_1205_, 0);
lean_dec(v_unused_1478_);
v___x_1217_ = v_items_1205_;
v_isShared_1218_ = v_isSharedCheck_1477_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_tail_1215_);
lean_dec(v_items_1205_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1477_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v_f_1219_; lean_object* v_indent_1220_; lean_object* v_activeTags_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1476_; 
v_f_1219_ = lean_ctor_get(v_head_1208_, 0);
v_indent_1220_ = lean_ctor_get(v_head_1208_, 1);
v_activeTags_1221_ = lean_ctor_get(v_head_1208_, 2);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_head_1208_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1223_ = v_head_1208_;
v_isShared_1224_ = v_isSharedCheck_1476_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_activeTags_1221_);
lean_inc(v_indent_1220_);
lean_inc(v_f_1219_);
lean_dec(v_head_1208_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1476_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
uint8_t v___y_1258_; 
switch(lean_obj_tag(v_f_1219_))
{
case 0:
{
lean_object* v___x_1261_; 
lean_del_object(v___x_1223_);
lean_dec(v_activeTags_1221_);
lean_dec(v_indent_1220_);
lean_del_object(v___x_1217_);
lean_del_object(v___x_1211_);
v___x_1261_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1213_, v_flb_1214_, v_tail_1209_, v_tail_1215_);
v_x_1200_ = v___x_1261_;
goto _start;
}
case 1:
{
lean_del_object(v___x_1223_);
lean_dec(v_activeTags_1221_);
lean_del_object(v___x_1217_);
lean_del_object(v___x_1211_);
if (v_flb_1214_ == 0)
{
uint8_t v___x_1263_; 
v___x_1263_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1213_);
if (v___x_1263_ == 0)
{
lean_object* v_out_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1278_; 
v_out_1264_ = lean_ctor_get(v___y_1201_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___y_1201_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v___y_1201_, 1);
lean_dec(v_unused_1279_);
v___x_1266_ = v___y_1201_;
v_isShared_1267_ = v_isSharedCheck_1278_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_out_1264_);
lean_dec(v___y_1201_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1278_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; uint32_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1268_ = l_Int_toNat(v_indent_1220_);
lean_dec(v_indent_1220_);
v___x_1269_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1270_ = 32;
lean_inc(v___x_1268_);
v___x_1271_ = lean_string_pushn(v___x_1269_, v___x_1270_, v___x_1268_);
v___x_1272_ = lean_string_append(v_out_1264_, v___x_1271_);
lean_dec_ref(v___x_1271_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v___x_1268_);
lean_ctor_set(v___x_1266_, 0, v___x_1272_);
v___x_1274_ = v___x_1266_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v___x_1268_);
v___x_1274_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1275_; 
v___x_1275_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1213_, v_flb_1214_, v_tail_1209_, v_tail_1215_);
v_x_1200_ = v___x_1275_;
v___y_1201_ = v___x_1274_;
goto _start;
}
}
}
else
{
lean_object* v_out_1280_; lean_object* v_column_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1294_; 
lean_dec(v_indent_1220_);
v_out_1280_ = lean_ctor_get(v___y_1201_, 0);
v_column_1281_ = lean_ctor_get(v___y_1201_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___y_1201_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1283_ = v___y_1201_;
v_isShared_1284_ = v_isSharedCheck_1294_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_column_1281_);
lean_inc(v_out_1280_);
lean_dec(v___y_1201_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1294_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1285_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_1286_ = lean_string_append(v_out_1280_, v___x_1285_);
v___x_1287_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_1288_ = lean_nat_add(v_column_1281_, v___x_1287_);
lean_dec(v_column_1281_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 1, v___x_1288_);
lean_ctor_set(v___x_1283_, 0, v___x_1286_);
v___x_1290_ = v___x_1283_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1291_; 
v___x_1291_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1213_, v_flb_1214_, v_tail_1209_, v_tail_1215_);
v_x_1200_ = v___x_1291_;
v___y_1201_ = v___x_1290_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = l_Int_toNat(v_indent_1220_);
lean_dec(v_indent_1220_);
v___x_1296_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1213_);
lean_dec(v_fla_1213_);
if (v___x_1296_ == 0)
{
lean_object* v_out_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1312_; 
v_out_1297_ = lean_ctor_get(v___y_1201_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___y_1201_);
if (v_isSharedCheck_1312_ == 0)
{
lean_object* v_unused_1313_; 
v_unused_1313_ = lean_ctor_get(v___y_1201_, 1);
lean_dec(v_unused_1313_);
v___x_1299_ = v___y_1201_;
v_isShared_1300_ = v_isSharedCheck_1312_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_out_1297_);
lean_dec(v___y_1201_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1312_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; uint32_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1301_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1302_ = 32;
lean_inc(v___x_1295_);
v___x_1303_ = lean_string_pushn(v___x_1301_, v___x_1302_, v___x_1295_);
v___x_1304_ = lean_string_append(v_out_1297_, v___x_1303_);
lean_dec_ref(v___x_1303_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 1, v___x_1295_);
lean_ctor_set(v___x_1299_, 0, v___x_1304_);
v___x_1306_ = v___x_1299_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v___x_1295_);
v___x_1306_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1307_; lean_object* v_fst_1308_; lean_object* v_snd_1309_; 
v___x_1307_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1214_, v_tail_1215_, v_tail_1209_, v_w_1199_, v___x_1306_);
v_fst_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_fst_1308_);
v_snd_1309_ = lean_ctor_get(v___x_1307_, 1);
lean_inc(v_snd_1309_);
lean_dec_ref(v___x_1307_);
v_x_1200_ = v_fst_1308_;
v___y_1201_ = v_snd_1309_;
goto _start;
}
}
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_fst_1318_; 
v___x_1314_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_1315_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_1316_ = lean_nat_sub(v_w_1199_, v___x_1315_);
lean_inc(v_tail_1209_);
lean_inc(v_tail_1215_);
v___x_1317_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1214_, v_tail_1215_, v_tail_1209_, v___x_1316_, v___y_1201_);
lean_dec(v___x_1316_);
v_fst_1318_ = lean_ctor_get(v___x_1317_, 0);
if (lean_obj_tag(v_fst_1318_) == 1)
{
lean_object* v_head_1319_; lean_object* v_snd_1320_; lean_object* v_fla_1321_; uint8_t v___x_1322_; 
lean_inc_ref(v_fst_1318_);
v_head_1319_ = lean_ctor_get(v_fst_1318_, 0);
v_snd_1320_ = lean_ctor_get(v___x_1317_, 1);
lean_inc(v_snd_1320_);
lean_dec_ref(v___x_1317_);
v_fla_1321_ = lean_ctor_get(v_head_1319_, 0);
v___x_1322_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1321_);
if (v___x_1322_ == 0)
{
lean_object* v_out_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1338_; 
lean_dec_ref_known(v_fst_1318_, 2);
v_out_1323_ = lean_ctor_get(v_snd_1320_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_snd_1320_);
if (v_isSharedCheck_1338_ == 0)
{
lean_object* v_unused_1339_; 
v_unused_1339_ = lean_ctor_get(v_snd_1320_, 1);
lean_dec(v_unused_1339_);
v___x_1325_ = v_snd_1320_;
v_isShared_1326_ = v_isSharedCheck_1338_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_out_1323_);
lean_dec(v_snd_1320_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1338_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; uint32_t v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1327_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1328_ = 32;
lean_inc(v___x_1295_);
v___x_1329_ = lean_string_pushn(v___x_1327_, v___x_1328_, v___x_1295_);
v___x_1330_ = lean_string_append(v_out_1323_, v___x_1329_);
lean_dec_ref(v___x_1329_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 1, v___x_1295_);
lean_ctor_set(v___x_1325_, 0, v___x_1330_);
v___x_1332_ = v___x_1325_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1330_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v___x_1295_);
v___x_1332_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
lean_object* v___x_1333_; lean_object* v_fst_1334_; lean_object* v_snd_1335_; 
v___x_1333_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1214_, v_tail_1215_, v_tail_1209_, v_w_1199_, v___x_1332_);
v_fst_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_fst_1334_);
v_snd_1335_ = lean_ctor_get(v___x_1333_, 1);
lean_inc(v_snd_1335_);
lean_dec_ref(v___x_1333_);
v_x_1200_ = v_fst_1334_;
v___y_1201_ = v_snd_1335_;
goto _start;
}
}
}
else
{
lean_object* v_out_1340_; lean_object* v_column_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1351_; 
lean_dec(v___x_1295_);
lean_dec(v_tail_1215_);
lean_dec(v_tail_1209_);
v_out_1340_ = lean_ctor_get(v_snd_1320_, 0);
v_column_1341_ = lean_ctor_get(v_snd_1320_, 1);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_snd_1320_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1343_ = v_snd_1320_;
v_isShared_1344_ = v_isSharedCheck_1351_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_column_1341_);
lean_inc(v_out_1340_);
lean_dec(v_snd_1320_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1351_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1345_ = lean_string_append(v_out_1340_, v___x_1314_);
v___x_1346_ = lean_nat_add(v_column_1341_, v___x_1315_);
lean_dec(v_column_1341_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 1, v___x_1346_);
lean_ctor_set(v___x_1343_, 0, v___x_1345_);
v___x_1348_ = v___x_1343_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
v_x_1200_ = v_fst_1318_;
v___y_1201_ = v___x_1348_;
goto _start;
}
}
}
}
else
{
lean_object* v_snd_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_dec(v___x_1295_);
lean_dec(v_tail_1215_);
lean_dec(v_tail_1209_);
v_snd_1352_ = lean_ctor_get(v___x_1317_, 1);
lean_inc(v_snd_1352_);
lean_dec_ref(v___x_1317_);
v___x_1353_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0));
v___x_1354_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(v___x_1353_, v_snd_1352_);
return v___x_1354_;
}
}
}
}
case 2:
{
uint8_t v_force_1355_; uint8_t v___x_1356_; 
lean_del_object(v___x_1223_);
lean_dec(v_activeTags_1221_);
lean_del_object(v___x_1217_);
lean_del_object(v___x_1211_);
v_force_1355_ = lean_ctor_get_uint8(v_f_1219_, 0);
lean_dec_ref_known(v_f_1219_, 0);
v___x_1356_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1213_);
if (v___x_1356_ == 0)
{
v___y_1258_ = v___x_1356_;
goto v___jp_1257_;
}
else
{
if (v_force_1355_ == 0)
{
v___y_1258_ = v___x_1356_;
goto v___jp_1257_;
}
else
{
goto v___jp_1225_;
}
}
}
case 3:
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1415_; 
lean_del_object(v___x_1211_);
v_a_1357_ = lean_ctor_get(v_f_1219_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_f_1219_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1359_ = v_f_1219_;
v_isShared_1360_ = v_isSharedCheck_1415_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v_f_1219_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1415_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
uint32_t v___x_1361_; lean_object* v_p_1362_; lean_object* v___x_1363_; uint8_t v_decide_1364_; 
v___x_1361_ = 10;
lean_inc_ref(v_a_1357_);
v_p_1362_ = lean_string_posof(v_a_1357_, v___x_1361_);
v___x_1363_ = lean_string_utf8_byte_size(v_a_1357_);
v_decide_1364_ = lean_nat_dec_eq(v_p_1362_, v___x_1363_);
if (v_decide_1364_ == 0)
{
lean_object* v_out_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1399_; 
v_out_1365_ = lean_ctor_get(v___y_1201_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___y_1201_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; 
v_unused_1400_ = lean_ctor_get(v___y_1201_, 1);
lean_dec(v_unused_1400_);
v___x_1367_ = v___y_1201_;
v_isShared_1368_ = v_isSharedCheck_1399_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_out_1365_);
lean_dec(v___y_1201_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1399_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; uint32_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1369_ = lean_unsigned_to_nat(0u);
v___x_1370_ = lean_string_utf8_extract(v_a_1357_, v___x_1369_, v_p_1362_);
v___x_1371_ = lean_string_append(v_out_1365_, v___x_1370_);
lean_dec_ref(v___x_1370_);
v___x_1372_ = l_Int_toNat(v_indent_1220_);
v___x_1373_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1374_ = 32;
lean_inc(v___x_1372_);
v___x_1375_ = lean_string_pushn(v___x_1373_, v___x_1374_, v___x_1372_);
v___x_1376_ = lean_string_append(v___x_1371_, v___x_1375_);
lean_dec_ref(v___x_1375_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 1, v___x_1372_);
lean_ctor_set(v___x_1367_, 0, v___x_1376_);
v___x_1378_ = v___x_1367_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v___x_1372_);
v___x_1378_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1379_ = lean_string_utf8_next(v_a_1357_, v_p_1362_);
lean_dec(v_p_1362_);
v___x_1380_ = lean_string_utf8_extract(v_a_1357_, v___x_1379_, v___x_1363_);
lean_dec(v___x_1379_);
lean_dec_ref(v_a_1357_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1380_);
v___x_1382_ = v___x_1359_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1384_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1382_);
v___x_1384_ = v___x_1223_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_indent_1220_);
lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_activeTags_1221_);
v___x_1384_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v_is_1386_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1384_);
v_is_1386_ = v___x_1217_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_tail_1215_);
v_is_1386_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1387_ = lean_box(1);
v___x_1388_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_1213_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v_fst_1390_; lean_object* v_snd_1391_; 
lean_dec(v_fla_1213_);
v___x_1389_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1214_, v_is_1386_, v_tail_1209_, v_w_1199_, v___x_1378_);
v_fst_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_fst_1390_);
v_snd_1391_ = lean_ctor_get(v___x_1389_, 1);
lean_inc(v_snd_1391_);
lean_dec_ref(v___x_1389_);
v_x_1200_ = v_fst_1390_;
v___y_1201_ = v_snd_1391_;
goto _start;
}
else
{
lean_object* v___x_1393_; 
v___x_1393_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1213_, v_flb_1214_, v_tail_1209_, v_is_1386_);
v_x_1200_ = v___x_1393_;
v___y_1201_ = v___x_1378_;
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
lean_object* v_out_1401_; lean_object* v_column_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1414_; 
lean_dec(v_p_1362_);
lean_del_object(v___x_1359_);
lean_del_object(v___x_1223_);
lean_dec(v_activeTags_1221_);
lean_dec(v_indent_1220_);
lean_del_object(v___x_1217_);
v_out_1401_ = lean_ctor_get(v___y_1201_, 0);
v_column_1402_ = lean_ctor_get(v___y_1201_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___y_1201_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1404_ = v___y_1201_;
v_isShared_1405_ = v_isSharedCheck_1414_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_column_1402_);
lean_inc(v_out_1401_);
lean_dec(v___y_1201_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1414_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1406_ = lean_string_append(v_out_1401_, v_a_1357_);
v___x_1407_ = lean_string_length(v_a_1357_);
lean_dec_ref(v_a_1357_);
v___x_1408_ = lean_nat_add(v_column_1402_, v___x_1407_);
lean_dec(v___x_1407_);
lean_dec(v_column_1402_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 1, v___x_1408_);
lean_ctor_set(v___x_1404_, 0, v___x_1406_);
v___x_1410_ = v___x_1404_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1411_; 
v___x_1411_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1213_, v_flb_1214_, v_tail_1209_, v_tail_1215_);
v_x_1200_ = v___x_1411_;
v___y_1201_ = v___x_1410_;
goto _start;
}
}
}
}
}
case 4:
{
lean_object* v_indent_1416_; lean_object* v_f_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; 
lean_del_object(v___x_1211_);
v_indent_1416_ = lean_ctor_get(v_f_1219_, 0);
lean_inc(v_indent_1416_);
v_f_1417_ = lean_ctor_get(v_f_1219_, 1);
lean_inc(v_f_1417_);
lean_dec_ref_known(v_f_1219_, 2);
v___x_1418_ = lean_int_add(v_indent_1220_, v_indent_1416_);
lean_dec(v_indent_1416_);
lean_dec(v_indent_1220_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v___x_1418_);
lean_ctor_set(v___x_1223_, 0, v_f_1417_);
v___x_1420_ = v___x_1223_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_f_1417_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1426_, 2, v_activeTags_1221_);
v___x_1420_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1422_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1420_);
v___x_1422_ = v___x_1217_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_tail_1215_);
v___x_1422_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1423_; 
v___x_1423_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1213_, v_flb_1214_, v_tail_1209_, v___x_1422_);
v_x_1200_ = v___x_1423_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_1427_; lean_object* v_a_1428_; lean_object* v___x_1429_; lean_object* v___x_1431_; 
v_a_1427_ = lean_ctor_get(v_f_1219_, 0);
lean_inc(v_a_1427_);
v_a_1428_ = lean_ctor_get(v_f_1219_, 1);
lean_inc(v_a_1428_);
lean_dec_ref_known(v_f_1219_, 2);
v___x_1429_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_1220_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 2, v___x_1429_);
lean_ctor_set(v___x_1223_, 0, v_a_1427_);
v___x_1431_ = v___x_1223_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1427_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_indent_1220_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1432_, 0, v_a_1428_);
lean_ctor_set(v___x_1432_, 1, v_indent_1220_);
lean_ctor_set(v___x_1432_, 2, v_activeTags_1221_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1432_);
v___x_1434_ = v___x_1217_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_tail_1215_);
v___x_1434_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1436_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 1, v___x_1434_);
lean_ctor_set(v___x_1211_, 0, v___x_1431_);
v___x_1436_ = v___x_1211_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1437_; 
v___x_1437_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1213_, v_flb_1214_, v_tail_1209_, v___x_1436_);
v_x_1200_ = v___x_1437_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_1442_; uint8_t v_behavior_1443_; uint8_t v___x_1444_; 
lean_del_object(v___x_1211_);
v_a_1442_ = lean_ctor_get(v_f_1219_, 0);
lean_inc(v_a_1442_);
v_behavior_1443_ = lean_ctor_get_uint8(v_f_1219_, sizeof(void*)*1);
lean_dec_ref_known(v_f_1219_, 1);
v___x_1444_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1213_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1446_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v_a_1442_);
v___x_1446_ = v___x_1223_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1442_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_indent_1220_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v_activeTags_1221_);
v___x_1446_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; lean_object* v___x_1449_; 
v___x_1447_ = lean_box(0);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v___x_1447_);
lean_ctor_set(v___x_1217_, 0, v___x_1446_);
v___x_1449_ = v___x_1217_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v_fst_1452_; lean_object* v_snd_1453_; 
v___x_1450_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1213_, v_flb_1214_, v_tail_1209_, v_tail_1215_);
v___x_1451_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_behavior_1443_, v___x_1449_, v___x_1450_, v_w_1199_, v___y_1201_);
v_fst_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_fst_1452_);
v_snd_1453_ = lean_ctor_get(v___x_1451_, 1);
lean_inc(v_snd_1453_);
lean_dec_ref(v___x_1451_);
v_x_1200_ = v_fst_1452_;
v___y_1201_ = v_snd_1453_;
goto _start;
}
}
}
else
{
lean_object* v___x_1458_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v_a_1442_);
v___x_1458_ = v___x_1223_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1442_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_indent_1220_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_activeTags_1221_);
v___x_1458_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1460_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1458_);
v___x_1460_ = v___x_1217_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_tail_1215_);
v___x_1460_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1461_; 
v___x_1461_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1213_, v_flb_1214_, v_tail_1209_, v___x_1460_);
v_x_1200_ = v___x_1461_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1469_; 
lean_del_object(v___x_1211_);
v_a_1465_ = lean_ctor_get(v_f_1219_, 1);
lean_inc(v_a_1465_);
lean_dec_ref_known(v_f_1219_, 2);
v___x_1466_ = lean_unsigned_to_nat(1u);
v___x_1467_ = lean_nat_add(v_activeTags_1221_, v___x_1466_);
lean_dec(v_activeTags_1221_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 2, v___x_1467_);
lean_ctor_set(v___x_1223_, 0, v_a_1465_);
v___x_1469_ = v___x_1223_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1465_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_indent_1220_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v___x_1467_);
v___x_1469_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1471_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1469_);
v___x_1471_ = v___x_1217_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_tail_1215_);
v___x_1471_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1472_; 
v___x_1472_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1213_, v_flb_1214_, v_tail_1209_, v___x_1471_);
v_x_1200_ = v___x_1472_;
goto _start;
}
}
}
}
v___jp_1225_:
{
lean_object* v_out_1226_; lean_object* v_column_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1256_; 
v_out_1226_ = lean_ctor_get(v___y_1201_, 0);
v_column_1227_ = lean_ctor_get(v___y_1201_, 1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___y_1201_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1229_ = v___y_1201_;
v_isShared_1230_ = v_isSharedCheck_1256_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_column_1227_);
lean_inc(v_out_1226_);
lean_dec(v___y_1201_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1256_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; uint8_t v___x_1232_; 
lean_inc(v_column_1227_);
v___x_1231_ = lean_nat_to_int(v_column_1227_);
v___x_1232_ = lean_int_dec_lt(v___x_1231_, v_indent_1220_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; uint32_t v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
lean_dec(v___x_1231_);
lean_dec(v_column_1227_);
v___x_1233_ = l_Int_toNat(v_indent_1220_);
lean_dec(v_indent_1220_);
v___x_1234_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1235_ = 32;
lean_inc(v___x_1233_);
v___x_1236_ = lean_string_pushn(v___x_1234_, v___x_1235_, v___x_1233_);
v___x_1237_ = lean_string_append(v_out_1226_, v___x_1236_);
lean_dec_ref(v___x_1236_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v___x_1233_);
lean_ctor_set(v___x_1229_, 0, v___x_1237_);
v___x_1239_ = v___x_1229_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v___x_1233_);
v___x_1239_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; 
v___x_1240_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1213_, v_flb_1214_, v_tail_1209_, v_tail_1215_);
v_x_1200_ = v___x_1240_;
v___y_1201_ = v___x_1239_;
goto _start;
}
}
else
{
lean_object* v___x_1243_; uint32_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1243_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_1244_ = 32;
v___x_1245_ = lean_int_sub(v_indent_1220_, v___x_1231_);
lean_dec(v___x_1231_);
lean_dec(v_indent_1220_);
v___x_1246_ = l_Int_toNat(v___x_1245_);
lean_dec(v___x_1245_);
v___x_1247_ = lean_string_pushn(v___x_1243_, v___x_1244_, v___x_1246_);
v___x_1248_ = lean_string_append(v_out_1226_, v___x_1247_);
v___x_1249_ = lean_string_length(v___x_1247_);
lean_dec_ref(v___x_1247_);
v___x_1250_ = lean_nat_add(v_column_1227_, v___x_1249_);
lean_dec(v___x_1249_);
lean_dec(v_column_1227_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v___x_1250_);
lean_ctor_set(v___x_1229_, 0, v___x_1248_);
v___x_1252_ = v___x_1229_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1253_; 
v___x_1253_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1213_, v_flb_1214_, v_tail_1209_, v_tail_1215_);
v_x_1200_ = v___x_1253_;
v___y_1201_ = v___x_1252_;
goto _start;
}
}
}
}
v___jp_1257_:
{
if (v___y_1258_ == 0)
{
goto v___jp_1225_;
}
else
{
lean_object* v___x_1259_; 
lean_dec(v_indent_1220_);
v___x_1259_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1213_, v_flb_1214_, v_tail_1209_, v_tail_1215_);
v_x_1200_ = v___x_1259_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0___boxed(lean_object* v_w_1481_, lean_object* v_x_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_1481_, v_x_1482_, v___y_1483_);
lean_dec(v_w_1481_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(lean_object* v_f_1485_, lean_object* v_w_1486_, lean_object* v_indent_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v___x_1489_; uint8_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1489_ = lean_box(1);
v___x_1490_ = 0;
v___x_1491_ = lean_nat_to_int(v_indent_1487_);
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1493_, 0, v_f_1485_);
lean_ctor_set(v___x_1493_, 1, v___x_1491_);
lean_ctor_set(v___x_1493_, 2, v___x_1492_);
v___x_1494_ = lean_box(0);
v___x_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1493_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1496_, 0, v___x_1489_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
lean_ctor_set_uint8(v___x_1496_, sizeof(void*)*2, v___x_1490_);
v___x_1497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
lean_ctor_set(v___x_1497_, 1, v___x_1494_);
v___x_1498_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_1486_, v___x_1497_, v___y_1488_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0___boxed(lean_object* v_f_1499_, lean_object* v_w_1500_, lean_object* v_indent_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(v_f_1499_, v_w_1500_, v_indent_1501_, v___y_1502_);
lean_dec(v_w_1500_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty(lean_object* v_f_1504_, lean_object* v_width_1505_, lean_object* v_indent_1506_, lean_object* v_column_1507_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v_snd_1511_; lean_object* v_out_1512_; 
v___x_1508_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set(v___x_1509_, 1, v_column_1507_);
v___x_1510_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(v_f_1504_, v_width_1505_, v_indent_1506_, v___x_1509_);
v_snd_1511_ = lean_ctor_get(v___x_1510_, 1);
lean_inc(v_snd_1511_);
lean_dec_ref(v___x_1510_);
v_out_1512_ = lean_ctor_get(v_snd_1511_, 0);
lean_inc_ref(v_out_1512_);
lean_dec(v_snd_1511_);
return v_out_1512_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty___boxed(lean_object* v_f_1513_, lean_object* v_width_1514_, lean_object* v_indent_1515_, lean_object* v_column_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Std_Format_pretty(v_f_1513_, v_width_1514_, v_indent_1515_, v_column_1516_);
lean_dec(v_width_1514_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0(lean_object* v_f_1518_){
_start:
{
lean_inc(v_f_1518_);
return v_f_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object* v_f_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Std_instToFormatFormat___lam__0(v_f_1519_);
lean_dec(v_f_1519_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatString___lam__0(lean_object* v_s_1523_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1524_, 0, v_s_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg___lam__0(lean_object* v_x_1527_, lean_object* v_inst_1528_, lean_object* v_x1_1529_, lean_object* v_x2_1530_){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1531_, 0, v_x1_1529_);
lean_ctor_set(v___x_1531_, 1, v_x_1527_);
v___x_1532_ = lean_apply_1(v_inst_1528_, v_x2_1530_);
v___x_1533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg(lean_object* v_inst_1534_, lean_object* v_x_1535_, lean_object* v_x_1536_){
_start:
{
if (lean_obj_tag(v_x_1535_) == 0)
{
lean_object* v___x_1537_; 
lean_dec(v_x_1536_);
lean_dec_ref(v_inst_1534_);
v___x_1537_ = lean_box(0);
return v___x_1537_;
}
else
{
lean_object* v_tail_1538_; 
v_tail_1538_ = lean_ctor_get(v_x_1535_, 1);
if (lean_obj_tag(v_tail_1538_) == 0)
{
lean_object* v_head_1539_; lean_object* v___x_1540_; 
lean_dec(v_x_1536_);
v_head_1539_ = lean_ctor_get(v_x_1535_, 0);
lean_inc(v_head_1539_);
lean_dec_ref_known(v_x_1535_, 2);
v___x_1540_ = lean_apply_1(v_inst_1534_, v_head_1539_);
return v___x_1540_;
}
else
{
lean_object* v_head_1541_; lean_object* v___f_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_inc(v_tail_1538_);
v_head_1541_ = lean_ctor_get(v_x_1535_, 0);
lean_inc(v_head_1541_);
lean_dec_ref_known(v_x_1535_, 2);
lean_inc_ref(v_inst_1534_);
v___f_1542_ = lean_alloc_closure((void*)(l_Std_Format_joinSep___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1542_, 0, v_x_1536_);
lean_closure_set(v___f_1542_, 1, v_inst_1534_);
v___x_1543_ = lean_apply_1(v_inst_1534_, v_head_1541_);
v___x_1544_ = l_List_foldl___redArg(v___f_1542_, v___x_1543_, v_tail_1538_);
return v___x_1544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep(lean_object* v_00_u03b1_1545_, lean_object* v_inst_1546_, lean_object* v_x_1547_, lean_object* v_x_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Std_Format_joinSep___redArg(v_inst_1546_, v_x_1547_, v_x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg___lam__0(lean_object* v_pre_1550_, lean_object* v_inst_1551_, lean_object* v_x1_1552_, lean_object* v_x2_1553_){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1554_, 0, v_x1_1552_);
lean_ctor_set(v___x_1554_, 1, v_pre_1550_);
v___x_1555_ = lean_apply_1(v_inst_1551_, v_x2_1553_);
v___x_1556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg(lean_object* v_inst_1557_, lean_object* v_pre_1558_, lean_object* v_x_1559_){
_start:
{
if (lean_obj_tag(v_x_1559_) == 0)
{
lean_object* v___x_1560_; 
lean_dec(v_pre_1558_);
lean_dec_ref(v_inst_1557_);
v___x_1560_ = lean_box(0);
return v___x_1560_;
}
else
{
lean_object* v_head_1561_; lean_object* v_tail_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1572_; 
v_head_1561_ = lean_ctor_get(v_x_1559_, 0);
v_tail_1562_ = lean_ctor_get(v_x_1559_, 1);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_x_1559_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1564_ = v_x_1559_;
v_isShared_1565_ = v_isSharedCheck_1572_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_tail_1562_);
lean_inc(v_head_1561_);
lean_dec(v_x_1559_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1572_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___f_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
lean_inc_ref(v_inst_1557_);
lean_inc(v_pre_1558_);
v___f_1566_ = lean_alloc_closure((void*)(l_Std_Format_prefixJoin___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1566_, 0, v_pre_1558_);
lean_closure_set(v___f_1566_, 1, v_inst_1557_);
v___x_1567_ = lean_apply_1(v_inst_1557_, v_head_1561_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set_tag(v___x_1564_, 5);
lean_ctor_set(v___x_1564_, 1, v___x_1567_);
lean_ctor_set(v___x_1564_, 0, v_pre_1558_);
v___x_1569_ = v___x_1564_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_pre_1558_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_List_foldl___redArg(v___f_1566_, v___x_1569_, v_tail_1562_);
return v___x_1570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin(lean_object* v_00_u03b1_1573_, lean_object* v_inst_1574_, lean_object* v_pre_1575_, lean_object* v_x_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Std_Format_prefixJoin___redArg(v_inst_1574_, v_pre_1575_, v_x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg___lam__0(lean_object* v_inst_1578_, lean_object* v_x_1579_, lean_object* v_x1_1580_, lean_object* v_x2_1581_){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1582_ = lean_apply_1(v_inst_1578_, v_x2_1581_);
v___x_1583_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1583_, 0, v_x1_1580_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
lean_ctor_set(v___x_1584_, 1, v_x_1579_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg(lean_object* v_inst_1585_, lean_object* v_x_1586_, lean_object* v_x_1587_){
_start:
{
if (lean_obj_tag(v_x_1586_) == 0)
{
lean_object* v___x_1588_; 
lean_dec(v_x_1587_);
lean_dec_ref(v_inst_1585_);
v___x_1588_ = lean_box(0);
return v___x_1588_;
}
else
{
lean_object* v_head_1589_; lean_object* v_tail_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1600_; 
v_head_1589_ = lean_ctor_get(v_x_1586_, 0);
v_tail_1590_ = lean_ctor_get(v_x_1586_, 1);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_x_1586_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1592_ = v_x_1586_;
v_isShared_1593_ = v_isSharedCheck_1600_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_tail_1590_);
lean_inc(v_head_1589_);
lean_dec(v_x_1586_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1600_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___f_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
lean_inc(v_x_1587_);
lean_inc_ref(v_inst_1585_);
v___f_1594_ = lean_alloc_closure((void*)(l_Std_Format_joinSuffix___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1594_, 0, v_inst_1585_);
lean_closure_set(v___f_1594_, 1, v_x_1587_);
v___x_1595_ = lean_apply_1(v_inst_1585_, v_head_1589_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 5);
lean_ctor_set(v___x_1592_, 1, v_x_1587_);
lean_ctor_set(v___x_1592_, 0, v___x_1595_);
v___x_1597_ = v___x_1592_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_x_1587_);
v___x_1597_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_List_foldl___redArg(v___f_1594_, v___x_1597_, v_tail_1590_);
return v___x_1598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix(lean_object* v_00_u03b1_1601_, lean_object* v_inst_1602_, lean_object* v_x_1603_, lean_object* v_x_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Std_Format_joinSuffix___redArg(v_inst_1602_, v_x_1603_, v_x_1604_);
return v___x_1605_;
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
