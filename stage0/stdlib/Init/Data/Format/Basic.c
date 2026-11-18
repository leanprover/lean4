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
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_posof(lean_object*, uint32_t);
lean_object* lean_string_offsetofpos(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_string_pushn(lean_object*, uint32_t, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_462_; uint8_t v___x_467_; uint8_t v___x_468_; lean_object* v___x_469_; lean_object* v_g_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v_r_474_; uint8_t v_foundLine_475_; uint8_t v_foundFlattenedHardLine_476_; lean_object* v_space_477_; lean_object* v___y_479_; uint8_t v___x_483_; 
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
v_foundLine_475_ = lean_ctor_get_uint8(v_r_474_, sizeof(void*)*1);
v_foundFlattenedHardLine_476_ = lean_ctor_get_uint8(v_r_474_, sizeof(void*)*1 + 1);
v_space_477_ = lean_ctor_get(v_r_474_, 0);
v___x_483_ = lean_nat_dec_lt(v___x_473_, v_space_477_);
if (v___x_483_ == 0)
{
if (v_foundLine_475_ == 0)
{
lean_object* v___x_484_; lean_object* v_r_u2082_485_; uint8_t v_foundLine_486_; uint8_t v_foundFlattenedHardLine_487_; lean_object* v_space_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_496_; 
lean_inc(v_space_477_);
lean_dec_ref(v_r_474_);
v___x_484_ = lean_nat_sub(v___x_473_, v_space_477_);
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
v___x_492_ = lean_nat_add(v_space_477_, v_space_488_);
lean_dec(v_space_488_);
lean_dec(v_space_477_);
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
v___y_479_ = v___x_494_;
goto v___jp_478_;
}
}
}
else
{
lean_dec(v_k_460_);
v___y_479_ = v_r_474_;
goto v___jp_478_;
}
}
else
{
lean_dec(v_k_460_);
v___y_479_ = v_r_474_;
goto v___jp_478_;
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
v___jp_478_:
{
if (v_foundFlattenedHardLine_476_ == 0)
{
lean_object* v_space_480_; uint8_t v___x_481_; 
v_space_480_ = lean_ctor_get(v___y_479_, 0);
lean_inc(v_space_480_);
lean_dec_ref(v___y_479_);
v___x_481_ = lean_nat_dec_le(v_space_480_, v___x_473_);
lean_dec(v___x_473_);
lean_dec(v_space_480_);
v___y_462_ = v___x_481_;
goto v___jp_461_;
}
else
{
uint8_t v___x_482_; 
lean_dec_ref(v___y_479_);
lean_dec(v___x_473_);
v___x_482_ = 0;
v___y_462_ = v___x_482_;
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
uint8_t v_flb_1479__boxed_553_; lean_object* v_res_554_; 
v_flb_1479__boxed_553_ = lean_unbox(v_flb_550_);
v_res_554_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_549_, v_flb_1479__boxed_553_, v_tail_551_, v_is_x27_552_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(lean_object* v_indent_562_, lean_object* v_pushNewline_563_, lean_object* v_toBind_564_, lean_object* v___f_565_, lean_object* v_____r_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = l_Int_toNat(v_indent_562_);
v___x_568_ = lean_apply_1(v_pushNewline_563_, v___x_567_);
v___x_569_ = lean_apply_4(v_toBind_564_, lean_box(0), lean_box(0), v___x_568_, v___f_565_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed(lean_object* v_indent_570_, lean_object* v_pushNewline_571_, lean_object* v_toBind_572_, lean_object* v___f_573_, lean_object* v_____r_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2(v_indent_570_, v_pushNewline_571_, v_toBind_572_, v___f_573_, v_____r_574_);
lean_dec(v_indent_570_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8(lean_object* v_inst_576_, lean_object* v_activeTags_577_, lean_object* v_toBind_578_, lean_object* v___f_579_, lean_object* v_____r_580_){
_start:
{
lean_object* v_endTags_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_endTags_581_ = lean_ctor_get(v_inst_576_, 4);
lean_inc(v_endTags_581_);
lean_dec_ref(v_inst_576_);
v___x_582_ = lean_apply_1(v_endTags_581_, v_activeTags_577_);
v___x_583_ = lean_apply_4(v_toBind_578_, lean_box(0), lean_box(0), v___x_582_, v___f_579_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(lean_object* v_indent_584_, lean_object* v_inst_585_, lean_object* v_toBind_586_, lean_object* v___f_587_, lean_object* v___f_588_, lean_object* v_k_589_){
_start:
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_nat_to_int(v_k_589_);
v___x_591_ = lean_int_dec_lt(v___x_590_, v_indent_584_);
if (v___x_591_ == 0)
{
lean_object* v_pushNewline_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec(v___x_590_);
lean_dec(v___f_588_);
v_pushNewline_592_ = lean_ctor_get(v_inst_585_, 1);
lean_inc(v_pushNewline_592_);
lean_dec_ref(v_inst_585_);
v___x_593_ = l_Int_toNat(v_indent_584_);
v___x_594_ = lean_apply_1(v_pushNewline_592_, v___x_593_);
v___x_595_ = lean_apply_4(v_toBind_586_, lean_box(0), lean_box(0), v___x_594_, v___f_587_);
return v___x_595_;
}
else
{
lean_object* v_pushOutput_596_; lean_object* v___x_597_; uint32_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v___f_587_);
v_pushOutput_596_ = lean_ctor_get(v_inst_585_, 0);
lean_inc(v_pushOutput_596_);
lean_dec_ref(v_inst_585_);
v___x_597_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_598_ = 32;
v___x_599_ = lean_int_sub(v_indent_584_, v___x_590_);
lean_dec(v___x_590_);
v___x_600_ = l_Int_toNat(v___x_599_);
lean_dec(v___x_599_);
v___x_601_ = lean_string_pushn(v___x_597_, v___x_598_, v___x_600_);
v___x_602_ = lean_apply_1(v_pushOutput_596_, v___x_601_);
v___x_603_ = lean_apply_4(v_toBind_586_, lean_box(0), lean_box(0), v___x_602_, v___f_588_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7___boxed(lean_object* v_indent_604_, lean_object* v_inst_605_, lean_object* v_toBind_606_, lean_object* v___f_607_, lean_object* v___f_608_, lean_object* v_k_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__7(v_indent_604_, v_inst_605_, v_toBind_606_, v___f_607_, v___f_608_, v_k_609_);
lean_dec(v_indent_604_);
return v_res_610_;
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
uint8_t v_flb_1571__boxed_639_; lean_object* v_res_640_; 
v_flb_1571__boxed_639_ = lean_unbox(v_flb_631_);
v_res_640_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__5(v_flb_1571__boxed_639_, v_tail_632_, v_tail_633_, v_w_634_, v_inst_635_, v_inst_636_, v_toBind_637_, v_____r_638_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9(lean_object* v_a_676_, lean_object* v_p_677_, lean_object* v___x_678_, lean_object* v_indent_679_, lean_object* v_activeTags_680_, lean_object* v_tail_681_, lean_object* v_fla_682_, uint8_t v_flb_683_, lean_object* v_tail_684_, lean_object* v_w_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_toBind_688_, lean_object* v_gs_x27_689_, lean_object* v_____r_690_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9___boxed(lean_object* v_a_703_, lean_object* v_p_704_, lean_object* v___x_705_, lean_object* v_indent_706_, lean_object* v_activeTags_707_, lean_object* v_tail_708_, lean_object* v_fla_709_, lean_object* v_flb_710_, lean_object* v_tail_711_, lean_object* v_w_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_toBind_715_, lean_object* v_gs_x27_716_, lean_object* v_____r_717_){
_start:
{
uint8_t v_flb_1609__boxed_718_; lean_object* v_res_719_; 
v_flb_1609__boxed_718_ = lean_unbox(v_flb_710_);
v_res_719_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9(v_a_703_, v_p_704_, v___x_705_, v_indent_706_, v_activeTags_707_, v_tail_708_, v_fla_709_, v_flb_1609__boxed_718_, v_tail_711_, v_w_712_, v_inst_713_, v_inst_714_, v_toBind_715_, v_gs_x27_716_, v_____r_717_);
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
lean_object* v_head_757_; lean_object* v_toBind_758_; lean_object* v_tail_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_902_; 
lean_inc(v_head_753_);
v_head_757_ = lean_ctor_get(v_items_754_, 0);
lean_inc(v_head_757_);
v_toBind_758_ = lean_ctor_get(v_inst_746_, 1);
v_tail_759_ = lean_ctor_get(v_x_748_, 1);
v_isSharedCheck_902_ = !lean_is_exclusive(v_x_748_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v_x_748_, 0);
lean_dec(v_unused_903_);
v___x_761_ = v_x_748_;
v_isShared_762_ = v_isSharedCheck_902_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_tail_759_);
lean_dec(v_x_748_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_902_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_fla_763_; uint8_t v_flb_764_; lean_object* v_tail_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_900_; 
v_fla_763_ = lean_ctor_get(v_head_753_, 0);
lean_inc(v_fla_763_);
v_flb_764_ = lean_ctor_get_uint8(v_head_753_, sizeof(void*)*2);
lean_dec(v_head_753_);
v_tail_765_ = lean_ctor_get(v_items_754_, 1);
v_isSharedCheck_900_ = !lean_is_exclusive(v_items_754_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; 
v_unused_901_ = lean_ctor_get(v_items_754_, 0);
lean_dec(v_unused_901_);
v___x_767_ = v_items_754_;
v_isShared_768_ = v_isSharedCheck_900_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_tail_765_);
lean_dec(v_items_754_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_900_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v_f_769_; lean_object* v_indent_770_; lean_object* v_activeTags_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_899_; 
v_f_769_ = lean_ctor_get(v_head_757_, 0);
v_indent_770_ = lean_ctor_get(v_head_757_, 1);
v_activeTags_771_ = lean_ctor_get(v_head_757_, 2);
v_isSharedCheck_899_ = !lean_is_exclusive(v_head_757_);
if (v_isSharedCheck_899_ == 0)
{
v___x_773_ = v_head_757_;
v_isShared_774_ = v_isSharedCheck_899_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_activeTags_771_);
lean_inc(v_indent_770_);
lean_inc(v_f_769_);
lean_dec(v_head_757_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_899_;
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
uint8_t v_force_814_; lean_object* v___f_815_; lean_object* v___f_816_; lean_object* v___f_817_; uint8_t v___x_821_; 
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
v___f_816_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__8), 5, 4);
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
v___x_821_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_763_);
lean_dec(v_fla_763_);
if (v___x_821_ == 0)
{
lean_dec_ref(v___f_815_);
lean_dec(v_activeTags_771_);
goto v___jp_818_;
}
else
{
if (v_force_814_ == 0)
{
lean_object* v_endTags_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec_ref(v___f_817_);
v_endTags_822_ = lean_ctor_get(v_inst_747_, 4);
lean_inc(v_endTags_822_);
lean_dec_ref(v_inst_747_);
v___x_823_ = lean_apply_1(v_endTags_822_, v_activeTags_771_);
v___x_824_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_823_, v___f_815_);
return v___x_824_;
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
}
case 3:
{
lean_object* v_a_825_; uint32_t v___x_826_; lean_object* v_p_827_; lean_object* v___x_828_; uint8_t v_decide_829_; 
lean_inc(v_toBind_758_);
lean_del_object(v___x_773_);
lean_del_object(v___x_767_);
lean_del_object(v___x_761_);
v_a_825_ = lean_ctor_get(v_f_769_, 0);
lean_inc_ref_n(v_a_825_, 2);
lean_dec_ref_known(v_f_769_, 1);
v___x_826_ = 10;
v_p_827_ = lean_string_posof(v_a_825_, v___x_826_);
v___x_828_ = lean_string_utf8_byte_size(v_a_825_);
v_decide_829_ = lean_nat_dec_eq(v_p_827_, v___x_828_);
if (v_decide_829_ == 0)
{
lean_object* v_pushOutput_830_; lean_object* v_pushNewline_831_; lean_object* v___x_832_; lean_object* v___f_833_; lean_object* v___f_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_pushOutput_830_ = lean_ctor_get(v_inst_747_, 0);
lean_inc(v_pushOutput_830_);
v_pushNewline_831_ = lean_ctor_get(v_inst_747_, 1);
lean_inc(v_pushNewline_831_);
v___x_832_ = lean_box(v_flb_764_);
lean_inc_n(v_toBind_758_, 2);
lean_inc(v_indent_770_);
lean_inc(v_p_827_);
lean_inc_ref(v_a_825_);
v___f_833_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__9___boxed), 15, 14);
lean_closure_set(v___f_833_, 0, v_a_825_);
lean_closure_set(v___f_833_, 1, v_p_827_);
lean_closure_set(v___f_833_, 2, v___x_828_);
lean_closure_set(v___f_833_, 3, v_indent_770_);
lean_closure_set(v___f_833_, 4, v_activeTags_771_);
lean_closure_set(v___f_833_, 5, v_tail_765_);
lean_closure_set(v___f_833_, 6, v_fla_763_);
lean_closure_set(v___f_833_, 7, v___x_832_);
lean_closure_set(v___f_833_, 8, v_tail_759_);
lean_closure_set(v___f_833_, 9, v_w_745_);
lean_closure_set(v___f_833_, 10, v_inst_746_);
lean_closure_set(v___f_833_, 11, v_inst_747_);
lean_closure_set(v___f_833_, 12, v_toBind_758_);
lean_closure_set(v___f_833_, 13, v_gs_x27_776_);
v___f_834_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_834_, 0, v_indent_770_);
lean_closure_set(v___f_834_, 1, v_pushNewline_831_);
lean_closure_set(v___f_834_, 2, v_toBind_758_);
lean_closure_set(v___f_834_, 3, v___f_833_);
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_string_utf8_extract(v_a_825_, v___x_835_, v_p_827_);
lean_dec(v_p_827_);
lean_dec_ref(v_a_825_);
v___x_837_ = lean_apply_1(v_pushOutput_830_, v___x_836_);
v___x_838_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_837_, v___f_834_);
return v___x_838_;
}
else
{
lean_object* v_pushOutput_839_; lean_object* v_endTags_840_; lean_object* v___f_841_; lean_object* v___f_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
lean_dec(v_p_827_);
lean_dec(v_indent_770_);
lean_dec(v_fla_763_);
lean_dec(v_tail_759_);
v_pushOutput_839_ = lean_ctor_get(v_inst_747_, 0);
lean_inc(v_pushOutput_839_);
v_endTags_840_ = lean_ctor_get(v_inst_747_, 4);
lean_inc(v_endTags_840_);
v___f_841_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__1), 6, 5);
lean_closure_set(v___f_841_, 0, v_gs_x27_776_);
lean_closure_set(v___f_841_, 1, v_tail_765_);
lean_closure_set(v___f_841_, 2, v_w_745_);
lean_closure_set(v___f_841_, 3, v_inst_746_);
lean_closure_set(v___f_841_, 4, v_inst_747_);
lean_inc(v_toBind_758_);
v___f_842_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__3), 5, 4);
lean_closure_set(v___f_842_, 0, v_endTags_840_);
lean_closure_set(v___f_842_, 1, v_activeTags_771_);
lean_closure_set(v___f_842_, 2, v_toBind_758_);
lean_closure_set(v___f_842_, 3, v___f_841_);
v___x_843_ = lean_apply_1(v_pushOutput_839_, v_a_825_);
v___x_844_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_843_, v___f_842_);
return v___x_844_;
}
}
case 4:
{
lean_object* v_indent_845_; lean_object* v_f_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
lean_dec_ref(v_gs_x27_776_);
lean_del_object(v___x_761_);
v_indent_845_ = lean_ctor_get(v_f_769_, 0);
lean_inc(v_indent_845_);
v_f_846_ = lean_ctor_get(v_f_769_, 1);
lean_inc(v_f_846_);
lean_dec_ref_known(v_f_769_, 2);
v___x_847_ = lean_int_add(v_indent_770_, v_indent_845_);
lean_dec(v_indent_845_);
lean_dec(v_indent_770_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_847_);
lean_ctor_set(v___x_773_, 0, v_f_846_);
v___x_849_ = v___x_773_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_f_846_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_activeTags_771_);
v___x_849_ = v_reuseFailAlloc_855_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_851_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_849_);
v___x_851_ = v___x_767_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_tail_765_);
v___x_851_ = v_reuseFailAlloc_854_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_852_; 
v___x_852_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_763_, v_flb_764_, v_tail_759_, v___x_851_);
v_x_748_ = v___x_852_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_856_; lean_object* v_a_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
lean_dec_ref(v_gs_x27_776_);
v_a_856_ = lean_ctor_get(v_f_769_, 0);
lean_inc(v_a_856_);
v_a_857_ = lean_ctor_get(v_f_769_, 1);
lean_inc(v_a_857_);
lean_dec_ref_known(v_f_769_, 2);
v___x_858_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_770_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 2, v___x_858_);
lean_ctor_set(v___x_773_, 0, v_a_856_);
v___x_860_ = v___x_773_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_856_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_indent_770_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v___x_858_);
v___x_860_ = v_reuseFailAlloc_870_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_861_, 0, v_a_857_);
lean_ctor_set(v___x_861_, 1, v_indent_770_);
lean_ctor_set(v___x_861_, 2, v_activeTags_771_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_861_);
v___x_863_ = v___x_767_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_tail_765_);
v___x_863_ = v_reuseFailAlloc_869_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_865_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v___x_863_);
lean_ctor_set(v___x_761_, 0, v___x_860_);
v___x_865_ = v___x_761_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v___x_863_);
v___x_865_ = v_reuseFailAlloc_868_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_866_; 
v___x_866_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_763_, v_flb_764_, v_tail_759_, v___x_865_);
v_x_748_ = v___x_866_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_871_; uint8_t v_behavior_872_; uint8_t v___x_873_; 
lean_dec_ref(v_gs_x27_776_);
lean_del_object(v___x_761_);
v_a_871_ = lean_ctor_get(v_f_769_, 0);
lean_inc(v_a_871_);
v_behavior_872_ = lean_ctor_get_uint8(v_f_769_, sizeof(void*)*1);
lean_dec_ref_known(v_f_769_, 1);
v___x_873_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_763_);
if (v___x_873_ == 0)
{
lean_object* v___x_875_; 
lean_inc(v_toBind_758_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v_a_871_);
v___x_875_ = v___x_773_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_871_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_indent_770_);
lean_ctor_set(v_reuseFailAlloc_884_, 2, v_activeTags_771_);
v___x_875_ = v_reuseFailAlloc_884_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_876_ = lean_box(0);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v___x_876_);
lean_ctor_set(v___x_767_, 0, v___x_875_);
v___x_878_ = v___x_767_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v___x_876_);
v___x_878_ = v_reuseFailAlloc_883_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_879_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_763_, v_flb_764_, v_tail_759_, v_tail_765_);
lean_inc_ref(v_inst_747_);
lean_inc_ref(v_inst_746_);
lean_inc(v_w_745_);
v___x_880_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___redArg(v_behavior_872_, v___x_878_, v___x_879_, v_w_745_, v_inst_746_, v_inst_747_);
v___x_881_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg), 4, 3);
lean_closure_set(v___x_881_, 0, v_w_745_);
lean_closure_set(v___x_881_, 1, v_inst_746_);
lean_closure_set(v___x_881_, 2, v_inst_747_);
v___x_882_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_880_, v___x_881_);
return v___x_882_;
}
}
}
else
{
lean_object* v___x_886_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v_a_871_);
v___x_886_ = v___x_773_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_871_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_indent_770_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_activeTags_771_);
v___x_886_ = v_reuseFailAlloc_892_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_886_);
v___x_888_ = v___x_767_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_tail_765_);
v___x_888_ = v_reuseFailAlloc_891_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; 
v___x_889_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_763_, v_flb_764_, v_tail_759_, v___x_888_);
v_x_748_ = v___x_889_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_893_; lean_object* v_a_894_; lean_object* v_startTag_895_; lean_object* v___f_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
lean_inc(v_toBind_758_);
lean_del_object(v___x_773_);
lean_del_object(v___x_767_);
lean_dec(v_fla_763_);
lean_del_object(v___x_761_);
lean_dec(v_tail_759_);
v_a_893_ = lean_ctor_get(v_f_769_, 0);
lean_inc(v_a_893_);
v_a_894_ = lean_ctor_get(v_f_769_, 1);
lean_inc(v_a_894_);
lean_dec_ref_known(v_f_769_, 2);
v_startTag_895_ = lean_ctor_get(v_inst_747_, 3);
lean_inc(v_startTag_895_);
v___f_896_ = lean_alloc_closure((void*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__12___boxed), 9, 8);
lean_closure_set(v___f_896_, 0, v_activeTags_771_);
lean_closure_set(v___f_896_, 1, v_a_894_);
lean_closure_set(v___f_896_, 2, v_indent_770_);
lean_closure_set(v___f_896_, 3, v_tail_765_);
lean_closure_set(v___f_896_, 4, v_gs_x27_776_);
lean_closure_set(v___f_896_, 5, v_w_745_);
lean_closure_set(v___f_896_, 6, v_inst_746_);
lean_closure_set(v___f_896_, 7, v_inst_747_);
v___x_897_ = lean_apply_1(v_startTag_895_, v_a_893_);
v___x_898_ = lean_apply_4(v_toBind_758_, lean_box(0), lean_box(0), v___x_897_, v___f_896_);
return v___x_898_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__4(lean_object* v_w_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_____x_907_, lean_object* v_____r_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_904_, v_inst_905_, v_inst_906_, v_____x_907_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be(lean_object* v_m_910_, lean_object* v_w_911_, lean_object* v_inst_912_, lean_object* v_inst_913_, lean_object* v_x_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_911_, v_inst_912_, v_inst_913_, v_x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___redArg(lean_object* v_f_916_, lean_object* v_w_917_, lean_object* v_indent_918_, lean_object* v_inst_919_, lean_object* v_inst_920_){
_start:
{
lean_object* v___x_921_; uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_921_ = lean_box(1);
v___x_922_ = 0;
v___x_923_ = lean_nat_to_int(v_indent_918_);
v___x_924_ = lean_unsigned_to_nat(0u);
v___x_925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_925_, 0, v_f_916_);
lean_ctor_set(v___x_925_, 1, v___x_923_);
lean_ctor_set(v___x_925_, 2, v___x_924_);
v___x_926_ = lean_box(0);
v___x_927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_928_, 0, v___x_921_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*2, v___x_922_);
v___x_929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___x_926_);
v___x_930_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg(v_w_917_, v_inst_919_, v_inst_920_, v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM(lean_object* v_m_931_, lean_object* v_f_932_, lean_object* v_w_933_, lean_object* v_indent_934_, lean_object* v_inst_935_, lean_object* v_inst_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Std_Format_prettyM___redArg(v_f_932_, v_w_933_, v_indent_934_, v_inst_935_, v_inst_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_bracket(lean_object* v_l_938_, lean_object* v_f_939_, lean_object* v_r_940_){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; lean_object* v___x_949_; 
v___x_941_ = lean_string_length(v_l_938_);
v___x_942_ = lean_nat_to_int(v___x_941_);
v___x_943_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_943_, 0, v_l_938_);
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v_f_939_);
v___x_945_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_945_, 0, v_r_940_);
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_942_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = 0;
v___x_949_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_949_, 0, v___x_947_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*1, v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_l_Std_Format_paren___closed__2(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l_Std_Format_paren___closed__0));
v___x_953_ = lean_string_length(v___x_952_);
return v___x_953_;
}
}
static lean_object* _init_l_Std_Format_paren___closed__3(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = lean_obj_once(&l_Std_Format_paren___closed__2, &l_Std_Format_paren___closed__2_once, _init_l_Std_Format_paren___closed__2);
v___x_955_ = lean_nat_to_int(v___x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_paren(lean_object* v_f_960_){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; lean_object* v___x_968_; 
v___x_961_ = lean_obj_once(&l_Std_Format_paren___closed__3, &l_Std_Format_paren___closed__3_once, _init_l_Std_Format_paren___closed__3);
v___x_962_ = ((lean_object*)(l_Std_Format_paren___closed__4));
v___x_963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v_f_960_);
v___x_964_ = ((lean_object*)(l_Std_Format_paren___closed__5));
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
static lean_object* _init_l_Std_Format_sbracket___closed__2(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l_Std_Format_sbracket___closed__0));
v___x_972_ = lean_string_length(v___x_971_);
return v___x_972_;
}
}
static lean_object* _init_l_Std_Format_sbracket___closed__3(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_obj_once(&l_Std_Format_sbracket___closed__2, &l_Std_Format_sbracket___closed__2_once, _init_l_Std_Format_sbracket___closed__2);
v___x_974_ = lean_nat_to_int(v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_sbracket(lean_object* v_f_979_){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; lean_object* v___x_987_; 
v___x_980_ = lean_obj_once(&l_Std_Format_sbracket___closed__3, &l_Std_Format_sbracket___closed__3_once, _init_l_Std_Format_sbracket___closed__3);
v___x_981_ = ((lean_object*)(l_Std_Format_sbracket___closed__4));
v___x_982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v_f_979_);
v___x_983_ = ((lean_object*)(l_Std_Format_sbracket___closed__5));
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
LEAN_EXPORT lean_object* l_Std_Format_bracketFill(lean_object* v_l_988_, lean_object* v_f_989_, lean_object* v_r_990_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_991_ = lean_string_length(v_l_988_);
v___x_992_ = lean_nat_to_int(v___x_991_);
v___x_993_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_993_, 0, v_l_988_);
v___x_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v_f_989_);
v___x_995_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_995_, 0, v_r_990_);
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_992_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = l_Std_Format_fill(v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l_Std_Format_defIndent(void){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = lean_unsigned_to_nat(2u);
return v___x_999_;
}
}
static uint8_t _init_l_Std_Format_defUnicode(void){
_start:
{
uint8_t v___x_1000_; 
v___x_1000_ = 1;
return v___x_1000_;
}
}
static lean_object* _init_l_Std_Format_defWidth(void){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_unsigned_to_nat(120u);
return v___x_1001_;
}
}
static lean_object* _init_l_Std_Format_nestD___closed__0(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_unsigned_to_nat(2u);
v___x_1003_ = lean_nat_to_int(v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_nestD(lean_object* v_f_1004_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_obj_once(&l_Std_Format_nestD___closed__0, &l_Std_Format_nestD___closed__0_once, _init_l_Std_Format_nestD___closed__0);
v___x_1006_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v_f_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_indentD(lean_object* v_f_1007_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = lean_box(1);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v_f_1007_);
v___x_1010_ = l_Std_Format_nestD(v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(lean_object* v_s_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_out_1013_; lean_object* v_column_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1026_; 
v_out_1013_ = lean_ctor_get(v___y_1012_, 0);
v_column_1014_ = lean_ctor_get(v___y_1012_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___y_1012_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1016_ = v___y_1012_;
v_isShared_1017_ = v_isSharedCheck_1026_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_column_1014_);
lean_inc(v_out_1013_);
lean_dec(v___y_1012_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1026_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1018_ = lean_box(0);
v___x_1019_ = lean_string_append(v_out_1013_, v_s_1011_);
v___x_1020_ = lean_string_length(v_s_1011_);
v___x_1021_ = lean_nat_add(v_column_1014_, v___x_1020_);
lean_dec(v___x_1020_);
lean_dec(v_column_1014_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 1, v___x_1021_);
lean_ctor_set(v___x_1016_, 0, v___x_1019_);
v___x_1023_ = v___x_1016_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; 
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1018_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
return v___x_1024_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0___boxed(lean_object* v_s_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__0(v_s_1027_, v___y_1028_);
lean_dec_ref(v_s_1027_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1(lean_object* v_indent_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_out_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1046_; 
v_out_1033_ = lean_ctor_get(v___y_1032_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___y_1032_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v___y_1032_, 1);
lean_dec(v_unused_1047_);
v___x_1035_ = v___y_1032_;
v_isShared_1036_ = v_isSharedCheck_1046_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_out_1033_);
lean_dec(v___y_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1046_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; uint32_t v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1037_ = lean_box(0);
v___x_1038_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1039_ = 32;
lean_inc(v_indent_1031_);
v___x_1040_ = lean_string_pushn(v___x_1038_, v___x_1039_, v_indent_1031_);
v___x_1041_ = lean_string_append(v_out_1033_, v___x_1040_);
lean_dec_ref(v___x_1040_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 1, v_indent_1031_);
lean_ctor_set(v___x_1035_, 0, v___x_1041_);
v___x_1043_ = v___x_1035_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_indent_1031_);
v___x_1043_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1037_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
return v___x_1044_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__2(lean_object* v_____do__lift_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_column_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
v_column_1050_ = lean_ctor_get(v_____do__lift_1048_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_____do__lift_1048_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v_____do__lift_1048_, 0);
lean_dec(v_unused_1058_);
v___x_1052_ = v_____do__lift_1048_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_column_1050_);
lean_dec(v_____do__lift_1048_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 1, v___y_1049_);
lean_ctor_set(v___x_1052_, 0, v_column_1050_);
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_column_1050_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___y_1049_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(lean_object* v_x_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_box(0);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v___y_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3___boxed(lean_object* v_x_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__3(v_x_1063_, v___y_1064_);
lean_dec(v_x_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(uint8_t v_flb_1101_, lean_object* v_items_1102_, lean_object* v_gs_1103_, lean_object* v_w_1104_, lean_object* v___y_1105_){
_start:
{
uint8_t v___y_1107_; lean_object* v_column_1112_; uint8_t v___x_1113_; uint8_t v___x_1114_; lean_object* v___x_1115_; lean_object* v_g_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v_r_1120_; uint8_t v_foundLine_1121_; uint8_t v_foundFlattenedHardLine_1122_; lean_object* v_space_1123_; lean_object* v___y_1125_; uint8_t v___x_1129_; 
v_column_1112_ = lean_ctor_get(v___y_1105_, 1);
v___x_1113_ = 0;
v___x_1114_ = l_Std_Format_instBEqFlattenBehavior_beq(v_flb_1101_, v___x_1113_);
v___x_1115_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1115_, 0, v___x_1114_);
lean_inc(v_items_1102_);
v_g_1116_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_g_1116_, 0, v___x_1115_);
lean_ctor_set(v_g_1116_, 1, v_items_1102_);
lean_ctor_set_uint8(v_g_1116_, sizeof(void*)*2, v_flb_1101_);
v___x_1117_ = lean_box(0);
v___x_1118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1118_, 0, v_g_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = lean_nat_sub(v_w_1104_, v_column_1112_);
lean_inc(v___x_1119_);
lean_inc(v_column_1112_);
v_r_1120_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v___x_1118_, v_column_1112_, v___x_1119_);
v_foundLine_1121_ = lean_ctor_get_uint8(v_r_1120_, sizeof(void*)*1);
v_foundFlattenedHardLine_1122_ = lean_ctor_get_uint8(v_r_1120_, sizeof(void*)*1 + 1);
v_space_1123_ = lean_ctor_get(v_r_1120_, 0);
v___x_1129_ = lean_nat_dec_lt(v___x_1119_, v_space_1123_);
if (v___x_1129_ == 0)
{
if (v_foundLine_1121_ == 0)
{
lean_object* v___x_1130_; lean_object* v_r_u2082_1131_; uint8_t v_foundLine_1132_; uint8_t v_foundFlattenedHardLine_1133_; lean_object* v_space_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1142_; 
lean_inc(v_space_1123_);
lean_dec_ref(v_r_1120_);
v___x_1130_ = lean_nat_sub(v___x_1119_, v_space_1123_);
lean_inc(v_column_1112_);
lean_inc(v_gs_1103_);
v_r_u2082_1131_ = l___private_Init_Data_Format_Basic_0__Std_Format_spaceUptoLine_x27(v_gs_1103_, v_column_1112_, v___x_1130_);
v_foundLine_1132_ = lean_ctor_get_uint8(v_r_u2082_1131_, sizeof(void*)*1);
v_foundFlattenedHardLine_1133_ = lean_ctor_get_uint8(v_r_u2082_1131_, sizeof(void*)*1 + 1);
v_space_1134_ = lean_ctor_get(v_r_u2082_1131_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_r_u2082_1131_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1136_ = v_r_u2082_1131_;
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_space_1134_);
lean_dec(v_r_u2082_1131_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = lean_nat_add(v_space_1123_, v_space_1134_);
lean_dec(v_space_1134_);
lean_dec(v_space_1123_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1138_);
v___x_1140_ = v___x_1136_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
lean_ctor_set_uint8(v_reuseFailAlloc_1141_, sizeof(void*)*1, v_foundLine_1132_);
lean_ctor_set_uint8(v_reuseFailAlloc_1141_, sizeof(void*)*1 + 1, v_foundFlattenedHardLine_1133_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
v___y_1125_ = v___x_1140_;
goto v___jp_1124_;
}
}
}
else
{
v___y_1125_ = v_r_1120_;
goto v___jp_1124_;
}
}
else
{
v___y_1125_ = v_r_1120_;
goto v___jp_1124_;
}
v___jp_1106_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1108_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1108_, 0, v___y_1107_);
v___x_1109_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v_items_1102_);
lean_ctor_set_uint8(v___x_1109_, sizeof(void*)*2, v_flb_1101_);
v___x_1110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
lean_ctor_set(v___x_1110_, 1, v_gs_1103_);
v___x_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v___y_1105_);
return v___x_1111_;
}
v___jp_1124_:
{
if (v_foundFlattenedHardLine_1122_ == 0)
{
lean_object* v_space_1126_; uint8_t v___x_1127_; 
v_space_1126_ = lean_ctor_get(v___y_1125_, 0);
lean_inc(v_space_1126_);
lean_dec_ref(v___y_1125_);
v___x_1127_ = lean_nat_dec_le(v_space_1126_, v___x_1119_);
lean_dec(v___x_1119_);
lean_dec(v_space_1126_);
v___y_1107_ = v___x_1127_;
goto v___jp_1106_;
}
else
{
uint8_t v___x_1128_; 
lean_dec_ref(v___y_1125_);
lean_dec(v___x_1119_);
v___x_1128_ = 0;
v___y_1107_ = v___x_1128_;
goto v___jp_1106_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1___boxed(lean_object* v_flb_1143_, lean_object* v_items_1144_, lean_object* v_gs_1145_, lean_object* v_w_1146_, lean_object* v___y_1147_){
_start:
{
uint8_t v_flb_boxed_1148_; lean_object* v_res_1149_; 
v_flb_boxed_1148_ = lean_unbox(v_flb_1143_);
v_res_1149_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_boxed_1148_, v_items_1144_, v_gs_1145_, v_w_1146_, v___y_1147_);
lean_dec(v_w_1146_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(lean_object* v_msg_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___f_1166_; lean_object* v___f_1167_; lean_object* v___f_1168_; lean_object* v___f_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_4906__overap_1178_; lean_object* v___x_1179_; 
v___f_1166_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__0));
v___f_1167_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__1));
v___f_1168_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__2));
v___f_1169_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__3));
v___x_1170_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__4));
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
lean_ctor_set(v___x_1171_, 1, v___f_1166_);
v___x_1172_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__5));
v___x_1173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
lean_ctor_set(v___x_1173_, 2, v___f_1167_);
lean_ctor_set(v___x_1173_, 3, v___f_1168_);
lean_ctor_set(v___x_1173_, 4, v___f_1169_);
v___x_1174_ = ((lean_object*)(l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2___closed__6));
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1173_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = lean_box(0);
v___x_1177_ = l_instInhabitedOfMonad___redArg(v___x_1175_, v___x_1176_);
v___x_4906__overap_1178_ = lean_panic_fn_borrowed(v___x_1177_, v_msg_1164_);
lean_dec(v___x_1177_);
v___x_1179_ = lean_apply_1(v___x_4906__overap_1178_, v___y_1165_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(lean_object* v_w_1180_, lean_object* v_x_1181_, lean_object* v___y_1182_){
_start:
{
if (lean_obj_tag(v_x_1181_) == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_box(0);
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v___y_1182_);
return v___x_1184_;
}
else
{
lean_object* v_head_1185_; lean_object* v_items_1186_; 
v_head_1185_ = lean_ctor_get(v_x_1181_, 0);
v_items_1186_ = lean_ctor_get(v_head_1185_, 1);
lean_inc(v_items_1186_);
if (lean_obj_tag(v_items_1186_) == 0)
{
lean_object* v_tail_1187_; 
v_tail_1187_ = lean_ctor_get(v_x_1181_, 1);
lean_inc(v_tail_1187_);
lean_dec_ref_known(v_x_1181_, 2);
v_x_1181_ = v_tail_1187_;
goto _start;
}
else
{
lean_object* v_head_1189_; lean_object* v_tail_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1458_; 
lean_inc(v_head_1185_);
v_head_1189_ = lean_ctor_get(v_items_1186_, 0);
lean_inc(v_head_1189_);
v_tail_1190_ = lean_ctor_get(v_x_1181_, 1);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_x_1181_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; 
v_unused_1459_ = lean_ctor_get(v_x_1181_, 0);
lean_dec(v_unused_1459_);
v___x_1192_ = v_x_1181_;
v_isShared_1193_ = v_isSharedCheck_1458_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_tail_1190_);
lean_dec(v_x_1181_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1458_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_fla_1194_; uint8_t v_flb_1195_; lean_object* v_tail_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1456_; 
v_fla_1194_ = lean_ctor_get(v_head_1185_, 0);
lean_inc(v_fla_1194_);
v_flb_1195_ = lean_ctor_get_uint8(v_head_1185_, sizeof(void*)*2);
lean_dec(v_head_1185_);
v_tail_1196_ = lean_ctor_get(v_items_1186_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_items_1186_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; 
v_unused_1457_ = lean_ctor_get(v_items_1186_, 0);
lean_dec(v_unused_1457_);
v___x_1198_ = v_items_1186_;
v_isShared_1199_ = v_isSharedCheck_1456_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_tail_1196_);
lean_dec(v_items_1186_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1456_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v_f_1200_; lean_object* v_indent_1201_; lean_object* v_activeTags_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1455_; 
v_f_1200_ = lean_ctor_get(v_head_1189_, 0);
v_indent_1201_ = lean_ctor_get(v_head_1189_, 1);
v_activeTags_1202_ = lean_ctor_get(v_head_1189_, 2);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_head_1189_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1204_ = v_head_1189_;
v_isShared_1205_ = v_isSharedCheck_1455_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_activeTags_1202_);
lean_inc(v_indent_1201_);
lean_inc(v_f_1200_);
lean_dec(v_head_1189_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1455_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
switch(lean_obj_tag(v_f_1200_))
{
case 0:
{
lean_object* v___x_1238_; 
lean_del_object(v___x_1204_);
lean_dec(v_activeTags_1202_);
lean_dec(v_indent_1201_);
lean_del_object(v___x_1198_);
lean_del_object(v___x_1192_);
v___x_1238_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1194_, v_flb_1195_, v_tail_1190_, v_tail_1196_);
v_x_1181_ = v___x_1238_;
goto _start;
}
case 1:
{
lean_del_object(v___x_1204_);
lean_dec(v_activeTags_1202_);
lean_del_object(v___x_1198_);
lean_del_object(v___x_1192_);
if (v_flb_1195_ == 0)
{
uint8_t v___x_1240_; 
v___x_1240_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1194_);
if (v___x_1240_ == 0)
{
lean_object* v_out_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1255_; 
v_out_1241_ = lean_ctor_get(v___y_1182_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___y_1182_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; 
v_unused_1256_ = lean_ctor_get(v___y_1182_, 1);
lean_dec(v_unused_1256_);
v___x_1243_ = v___y_1182_;
v_isShared_1244_ = v_isSharedCheck_1255_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_out_1241_);
lean_dec(v___y_1182_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1255_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; uint32_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1245_ = l_Int_toNat(v_indent_1201_);
lean_dec(v_indent_1201_);
v___x_1246_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1247_ = 32;
lean_inc(v___x_1245_);
v___x_1248_ = lean_string_pushn(v___x_1246_, v___x_1247_, v___x_1245_);
v___x_1249_ = lean_string_append(v_out_1241_, v___x_1248_);
lean_dec_ref(v___x_1248_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___x_1245_);
lean_ctor_set(v___x_1243_, 0, v___x_1249_);
v___x_1251_ = v___x_1243_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1245_);
v___x_1251_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; 
v___x_1252_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1194_, v_flb_1195_, v_tail_1190_, v_tail_1196_);
v_x_1181_ = v___x_1252_;
v___y_1182_ = v___x_1251_;
goto _start;
}
}
}
else
{
lean_object* v_out_1257_; lean_object* v_column_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v_indent_1201_);
v_out_1257_ = lean_ctor_get(v___y_1182_, 0);
v_column_1258_ = lean_ctor_get(v___y_1182_, 1);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___y_1182_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1260_ = v___y_1182_;
v_isShared_1261_ = v_isSharedCheck_1271_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_column_1258_);
lean_inc(v_out_1257_);
lean_dec(v___y_1182_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1271_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1262_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_1263_ = lean_string_append(v_out_1257_, v___x_1262_);
v___x_1264_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_1265_ = lean_nat_add(v_column_1258_, v___x_1264_);
lean_dec(v_column_1258_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 1, v___x_1265_);
lean_ctor_set(v___x_1260_, 0, v___x_1263_);
v___x_1267_ = v___x_1260_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; 
v___x_1268_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1194_, v_flb_1195_, v_tail_1190_, v_tail_1196_);
v_x_1181_ = v___x_1268_;
v___y_1182_ = v___x_1267_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1272_ = l_Int_toNat(v_indent_1201_);
lean_dec(v_indent_1201_);
v___x_1273_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1194_);
lean_dec(v_fla_1194_);
if (v___x_1273_ == 0)
{
lean_object* v_out_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1289_; 
v_out_1274_ = lean_ctor_get(v___y_1182_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___y_1182_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v___y_1182_, 1);
lean_dec(v_unused_1290_);
v___x_1276_ = v___y_1182_;
v_isShared_1277_ = v_isSharedCheck_1289_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_out_1274_);
lean_dec(v___y_1182_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1289_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; uint32_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1278_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1279_ = 32;
lean_inc(v___x_1272_);
v___x_1280_ = lean_string_pushn(v___x_1278_, v___x_1279_, v___x_1272_);
v___x_1281_ = lean_string_append(v_out_1274_, v___x_1280_);
lean_dec_ref(v___x_1280_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v___x_1272_);
lean_ctor_set(v___x_1276_, 0, v___x_1281_);
v___x_1283_ = v___x_1276_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v___x_1272_);
v___x_1283_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; lean_object* v_fst_1285_; lean_object* v_snd_1286_; 
v___x_1284_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1195_, v_tail_1196_, v_tail_1190_, v_w_1180_, v___x_1283_);
v_fst_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_fst_1285_);
v_snd_1286_ = lean_ctor_get(v___x_1284_, 1);
lean_inc(v_snd_1286_);
lean_dec_ref(v___x_1284_);
v_x_1181_ = v_fst_1285_;
v___y_1182_ = v_snd_1286_;
goto _start;
}
}
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v_fst_1295_; 
v___x_1291_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__0));
v___x_1292_ = lean_obj_once(&l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1, &l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1_once, _init_l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___closed__1);
v___x_1293_ = lean_nat_sub(v_w_1180_, v___x_1292_);
lean_inc(v_tail_1190_);
lean_inc(v_tail_1196_);
v___x_1294_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1195_, v_tail_1196_, v_tail_1190_, v___x_1293_, v___y_1182_);
lean_dec(v___x_1293_);
v_fst_1295_ = lean_ctor_get(v___x_1294_, 0);
if (lean_obj_tag(v_fst_1295_) == 1)
{
lean_object* v_head_1296_; lean_object* v_snd_1297_; lean_object* v_fla_1298_; uint8_t v___x_1299_; 
lean_inc_ref(v_fst_1295_);
v_head_1296_ = lean_ctor_get(v_fst_1295_, 0);
v_snd_1297_ = lean_ctor_get(v___x_1294_, 1);
lean_inc(v_snd_1297_);
lean_dec_ref(v___x_1294_);
v_fla_1298_ = lean_ctor_get(v_head_1296_, 0);
v___x_1299_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1298_);
if (v___x_1299_ == 0)
{
lean_object* v_out_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1315_; 
lean_dec_ref_known(v_fst_1295_, 2);
v_out_1300_ = lean_ctor_get(v_snd_1297_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_snd_1297_);
if (v_isSharedCheck_1315_ == 0)
{
lean_object* v_unused_1316_; 
v_unused_1316_ = lean_ctor_get(v_snd_1297_, 1);
lean_dec(v_unused_1316_);
v___x_1302_ = v_snd_1297_;
v_isShared_1303_ = v_isSharedCheck_1315_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_out_1300_);
lean_dec(v_snd_1297_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1315_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; uint32_t v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1304_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1305_ = 32;
lean_inc(v___x_1272_);
v___x_1306_ = lean_string_pushn(v___x_1304_, v___x_1305_, v___x_1272_);
v___x_1307_ = lean_string_append(v_out_1300_, v___x_1306_);
lean_dec_ref(v___x_1306_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 1, v___x_1272_);
lean_ctor_set(v___x_1302_, 0, v___x_1307_);
v___x_1309_ = v___x_1302_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v___x_1272_);
v___x_1309_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1310_; lean_object* v_fst_1311_; lean_object* v_snd_1312_; 
v___x_1310_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1195_, v_tail_1196_, v_tail_1190_, v_w_1180_, v___x_1309_);
v_fst_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_fst_1311_);
v_snd_1312_ = lean_ctor_get(v___x_1310_, 1);
lean_inc(v_snd_1312_);
lean_dec_ref(v___x_1310_);
v_x_1181_ = v_fst_1311_;
v___y_1182_ = v_snd_1312_;
goto _start;
}
}
}
else
{
lean_object* v_out_1317_; lean_object* v_column_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1328_; 
lean_dec(v___x_1272_);
lean_dec(v_tail_1196_);
lean_dec(v_tail_1190_);
v_out_1317_ = lean_ctor_get(v_snd_1297_, 0);
v_column_1318_ = lean_ctor_get(v_snd_1297_, 1);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_snd_1297_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1320_ = v_snd_1297_;
v_isShared_1321_ = v_isSharedCheck_1328_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_column_1318_);
lean_inc(v_out_1317_);
lean_dec(v_snd_1297_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1328_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1322_ = lean_string_append(v_out_1317_, v___x_1291_);
v___x_1323_ = lean_nat_add(v_column_1318_, v___x_1292_);
lean_dec(v_column_1318_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 1, v___x_1323_);
lean_ctor_set(v___x_1320_, 0, v___x_1322_);
v___x_1325_ = v___x_1320_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
v_x_1181_ = v_fst_1295_;
v___y_1182_ = v___x_1325_;
goto _start;
}
}
}
}
else
{
lean_object* v_snd_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec(v___x_1272_);
lean_dec(v_tail_1196_);
lean_dec(v_tail_1190_);
v_snd_1329_ = lean_ctor_get(v___x_1294_, 1);
lean_inc(v_snd_1329_);
lean_dec_ref(v___x_1294_);
v___x_1330_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__6___closed__0));
v___x_1331_ = l_panic___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__2(v___x_1330_, v_snd_1329_);
return v___x_1331_;
}
}
}
}
case 2:
{
uint8_t v_force_1332_; uint8_t v___x_1333_; 
lean_del_object(v___x_1204_);
lean_dec(v_activeTags_1202_);
lean_del_object(v___x_1198_);
lean_del_object(v___x_1192_);
v_force_1332_ = lean_ctor_get_uint8(v_f_1200_, 0);
lean_dec_ref_known(v_f_1200_, 0);
v___x_1333_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1194_);
if (v___x_1333_ == 0)
{
goto v___jp_1206_;
}
else
{
if (v_force_1332_ == 0)
{
lean_object* v___x_1334_; 
lean_dec(v_indent_1201_);
v___x_1334_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1194_, v_flb_1195_, v_tail_1190_, v_tail_1196_);
v_x_1181_ = v___x_1334_;
goto _start;
}
else
{
goto v___jp_1206_;
}
}
}
case 3:
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1394_; 
lean_del_object(v___x_1192_);
v_a_1336_ = lean_ctor_get(v_f_1200_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_f_1200_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1338_ = v_f_1200_;
v_isShared_1339_ = v_isSharedCheck_1394_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v_f_1200_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1394_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
uint32_t v___x_1340_; lean_object* v_p_1341_; lean_object* v___x_1342_; uint8_t v_decide_1343_; 
v___x_1340_ = 10;
lean_inc_ref(v_a_1336_);
v_p_1341_ = lean_string_posof(v_a_1336_, v___x_1340_);
v___x_1342_ = lean_string_utf8_byte_size(v_a_1336_);
v_decide_1343_ = lean_nat_dec_eq(v_p_1341_, v___x_1342_);
if (v_decide_1343_ == 0)
{
lean_object* v_out_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1378_; 
v_out_1344_ = lean_ctor_get(v___y_1182_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___y_1182_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v___y_1182_, 1);
lean_dec(v_unused_1379_);
v___x_1346_ = v___y_1182_;
v_isShared_1347_ = v_isSharedCheck_1378_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_out_1344_);
lean_dec(v___y_1182_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1378_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint32_t v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1348_ = lean_unsigned_to_nat(0u);
v___x_1349_ = lean_string_utf8_extract(v_a_1336_, v___x_1348_, v_p_1341_);
v___x_1350_ = lean_string_append(v_out_1344_, v___x_1349_);
lean_dec_ref(v___x_1349_);
v___x_1351_ = l_Int_toNat(v_indent_1201_);
v___x_1352_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1353_ = 32;
lean_inc(v___x_1351_);
v___x_1354_ = lean_string_pushn(v___x_1352_, v___x_1353_, v___x_1351_);
v___x_1355_ = lean_string_append(v___x_1350_, v___x_1354_);
lean_dec_ref(v___x_1354_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v___x_1351_);
lean_ctor_set(v___x_1346_, 0, v___x_1355_);
v___x_1357_ = v___x_1346_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v___x_1351_);
v___x_1357_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1358_ = lean_string_utf8_next(v_a_1336_, v_p_1341_);
lean_dec(v_p_1341_);
v___x_1359_ = lean_string_utf8_extract(v_a_1336_, v___x_1358_, v___x_1342_);
lean_dec(v___x_1358_);
lean_dec_ref(v_a_1336_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1359_);
v___x_1361_ = v___x_1338_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1363_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1361_);
v___x_1363_ = v___x_1204_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_indent_1201_);
lean_ctor_set(v_reuseFailAlloc_1375_, 2, v_activeTags_1202_);
v___x_1363_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v_is_1365_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1363_);
v_is_1365_ = v___x_1198_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_tail_1196_);
v_is_1365_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; uint8_t v___x_1367_; 
v___x_1366_ = lean_box(1);
v___x_1367_ = l_Std_Format_instBEqFlattenAllowability_beq(v_fla_1194_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; lean_object* v_fst_1369_; lean_object* v_snd_1370_; 
lean_dec(v_fla_1194_);
v___x_1368_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_flb_1195_, v_is_1365_, v_tail_1190_, v_w_1180_, v___x_1357_);
v_fst_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_fst_1369_);
v_snd_1370_ = lean_ctor_get(v___x_1368_, 1);
lean_inc(v_snd_1370_);
lean_dec_ref(v___x_1368_);
v_x_1181_ = v_fst_1369_;
v___y_1182_ = v_snd_1370_;
goto _start;
}
else
{
lean_object* v___x_1372_; 
v___x_1372_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1194_, v_flb_1195_, v_tail_1190_, v_is_1365_);
v_x_1181_ = v___x_1372_;
v___y_1182_ = v___x_1357_;
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
lean_object* v_out_1380_; lean_object* v_column_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1393_; 
lean_dec(v_p_1341_);
lean_del_object(v___x_1338_);
lean_del_object(v___x_1204_);
lean_dec(v_activeTags_1202_);
lean_dec(v_indent_1201_);
lean_del_object(v___x_1198_);
v_out_1380_ = lean_ctor_get(v___y_1182_, 0);
v_column_1381_ = lean_ctor_get(v___y_1182_, 1);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___y_1182_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1383_ = v___y_1182_;
v_isShared_1384_ = v_isSharedCheck_1393_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_column_1381_);
lean_inc(v_out_1380_);
lean_dec(v___y_1182_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1393_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1385_ = lean_string_append(v_out_1380_, v_a_1336_);
v___x_1386_ = lean_string_length(v_a_1336_);
lean_dec_ref(v_a_1336_);
v___x_1387_ = lean_nat_add(v_column_1381_, v___x_1386_);
lean_dec(v___x_1386_);
lean_dec(v_column_1381_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v___x_1387_);
lean_ctor_set(v___x_1383_, 0, v___x_1385_);
v___x_1389_ = v___x_1383_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; 
v___x_1390_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1194_, v_flb_1195_, v_tail_1190_, v_tail_1196_);
v_x_1181_ = v___x_1390_;
v___y_1182_ = v___x_1389_;
goto _start;
}
}
}
}
}
case 4:
{
lean_object* v_indent_1395_; lean_object* v_f_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
lean_del_object(v___x_1192_);
v_indent_1395_ = lean_ctor_get(v_f_1200_, 0);
lean_inc(v_indent_1395_);
v_f_1396_ = lean_ctor_get(v_f_1200_, 1);
lean_inc(v_f_1396_);
lean_dec_ref_known(v_f_1200_, 2);
v___x_1397_ = lean_int_add(v_indent_1201_, v_indent_1395_);
lean_dec(v_indent_1395_);
lean_dec(v_indent_1201_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1397_);
lean_ctor_set(v___x_1204_, 0, v_f_1396_);
v___x_1399_ = v___x_1204_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_f_1396_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1405_, 2, v_activeTags_1202_);
v___x_1399_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1401_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1399_);
v___x_1401_ = v___x_1198_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1399_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_tail_1196_);
v___x_1401_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1402_; 
v___x_1402_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1194_, v_flb_1195_, v_tail_1190_, v___x_1401_);
v_x_1181_ = v___x_1402_;
goto _start;
}
}
}
case 5:
{
lean_object* v_a_1406_; lean_object* v_a_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
v_a_1406_ = lean_ctor_get(v_f_1200_, 0);
lean_inc(v_a_1406_);
v_a_1407_ = lean_ctor_get(v_f_1200_, 1);
lean_inc(v_a_1407_);
lean_dec_ref_known(v_f_1200_, 2);
v___x_1408_ = lean_unsigned_to_nat(0u);
lean_inc(v_indent_1201_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 2, v___x_1408_);
lean_ctor_set(v___x_1204_, 0, v_a_1406_);
v___x_1410_ = v___x_1204_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1406_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_indent_1201_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1411_, 0, v_a_1407_);
lean_ctor_set(v___x_1411_, 1, v_indent_1201_);
lean_ctor_set(v___x_1411_, 2, v_activeTags_1202_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1411_);
v___x_1413_ = v___x_1198_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_tail_1196_);
v___x_1413_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1415_; 
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v___x_1413_);
lean_ctor_set(v___x_1192_, 0, v___x_1410_);
v___x_1415_ = v___x_1192_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v___x_1413_);
v___x_1415_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1416_; 
v___x_1416_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1194_, v_flb_1195_, v_tail_1190_, v___x_1415_);
v_x_1181_ = v___x_1416_;
goto _start;
}
}
}
}
case 6:
{
lean_object* v_a_1421_; uint8_t v_behavior_1422_; uint8_t v___x_1423_; 
lean_del_object(v___x_1192_);
v_a_1421_ = lean_ctor_get(v_f_1200_, 0);
lean_inc(v_a_1421_);
v_behavior_1422_ = lean_ctor_get_uint8(v_f_1200_, sizeof(void*)*1);
lean_dec_ref_known(v_f_1200_, 1);
v___x_1423_ = l_Std_Format_FlattenAllowability_shouldFlatten(v_fla_1194_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1425_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v_a_1421_);
v___x_1425_ = v___x_1204_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1421_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_indent_1201_);
lean_ctor_set(v_reuseFailAlloc_1435_, 2, v_activeTags_1202_);
v___x_1425_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1426_ = lean_box(0);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 1, v___x_1426_);
lean_ctor_set(v___x_1198_, 0, v___x_1425_);
v___x_1428_ = v___x_1198_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v_fst_1431_; lean_object* v_snd_1432_; 
v___x_1429_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1194_, v_flb_1195_, v_tail_1190_, v_tail_1196_);
v___x_1430_ = l___private_Init_Data_Format_Basic_0__Std_Format_pushGroup___at___00__private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0_spec__1(v_behavior_1422_, v___x_1428_, v___x_1429_, v_w_1180_, v___y_1182_);
v_fst_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_fst_1431_);
v_snd_1432_ = lean_ctor_get(v___x_1430_, 1);
lean_inc(v_snd_1432_);
lean_dec_ref(v___x_1430_);
v_x_1181_ = v_fst_1431_;
v___y_1182_ = v_snd_1432_;
goto _start;
}
}
}
else
{
lean_object* v___x_1437_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v_a_1421_);
v___x_1437_ = v___x_1204_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1421_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_indent_1201_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_activeTags_1202_);
v___x_1437_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
lean_object* v___x_1439_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1437_);
v___x_1439_ = v___x_1198_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_tail_1196_);
v___x_1439_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1440_; 
v___x_1440_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1194_, v_flb_1195_, v_tail_1190_, v___x_1439_);
v_x_1181_ = v___x_1440_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_a_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1448_; 
lean_del_object(v___x_1192_);
v_a_1444_ = lean_ctor_get(v_f_1200_, 1);
lean_inc(v_a_1444_);
lean_dec_ref_known(v_f_1200_, 2);
v___x_1445_ = lean_unsigned_to_nat(1u);
v___x_1446_ = lean_nat_add(v_activeTags_1202_, v___x_1445_);
lean_dec(v_activeTags_1202_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 2, v___x_1446_);
lean_ctor_set(v___x_1204_, 0, v_a_1444_);
v___x_1448_ = v___x_1204_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1444_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_indent_1201_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v___x_1446_);
v___x_1448_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1450_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1448_);
v___x_1450_ = v___x_1198_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_tail_1196_);
v___x_1450_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; 
v___x_1451_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1194_, v_flb_1195_, v_tail_1190_, v___x_1450_);
v_x_1181_ = v___x_1451_;
goto _start;
}
}
}
}
v___jp_1206_:
{
lean_object* v_out_1207_; lean_object* v_column_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1237_; 
v_out_1207_ = lean_ctor_get(v___y_1182_, 0);
v_column_1208_ = lean_ctor_get(v___y_1182_, 1);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___y_1182_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1210_ = v___y_1182_;
v_isShared_1211_ = v_isSharedCheck_1237_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_column_1208_);
lean_inc(v_out_1207_);
lean_dec(v___y_1182_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1237_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; uint8_t v___x_1213_; 
lean_inc(v_column_1208_);
v___x_1212_ = lean_nat_to_int(v_column_1208_);
v___x_1213_ = lean_int_dec_lt(v___x_1212_, v_indent_1201_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; lean_object* v___x_1215_; uint32_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
lean_dec(v___x_1212_);
lean_dec(v_column_1208_);
v___x_1214_ = l_Int_toNat(v_indent_1201_);
lean_dec(v_indent_1201_);
v___x_1215_ = ((lean_object*)(l___private_Init_Data_Format_Basic_0__Std_Format_instMonadPrettyFormatStateMState___lam__1___closed__0));
v___x_1216_ = 32;
lean_inc(v___x_1214_);
v___x_1217_ = lean_string_pushn(v___x_1215_, v___x_1216_, v___x_1214_);
v___x_1218_ = lean_string_append(v_out_1207_, v___x_1217_);
lean_dec_ref(v___x_1217_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 1, v___x_1214_);
lean_ctor_set(v___x_1210_, 0, v___x_1218_);
v___x_1220_ = v___x_1210_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1214_);
v___x_1220_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; 
v___x_1221_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1194_, v_flb_1195_, v_tail_1190_, v_tail_1196_);
v_x_1181_ = v___x_1221_;
v___y_1182_ = v___x_1220_;
goto _start;
}
}
else
{
lean_object* v___x_1224_; uint32_t v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1224_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_1225_ = 32;
v___x_1226_ = lean_int_sub(v_indent_1201_, v___x_1212_);
lean_dec(v___x_1212_);
lean_dec(v_indent_1201_);
v___x_1227_ = l_Int_toNat(v___x_1226_);
lean_dec(v___x_1226_);
v___x_1228_ = lean_string_pushn(v___x_1224_, v___x_1225_, v___x_1227_);
v___x_1229_ = lean_string_append(v_out_1207_, v___x_1228_);
v___x_1230_ = lean_string_length(v___x_1228_);
lean_dec_ref(v___x_1228_);
v___x_1231_ = lean_nat_add(v_column_1208_, v___x_1230_);
lean_dec(v___x_1230_);
lean_dec(v_column_1208_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 1, v___x_1231_);
lean_ctor_set(v___x_1210_, 0, v___x_1229_);
v___x_1233_ = v___x_1210_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1234_; 
v___x_1234_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___redArg___lam__0(v_fla_1194_, v_flb_1195_, v_tail_1190_, v_tail_1196_);
v_x_1181_ = v___x_1234_;
v___y_1182_ = v___x_1233_;
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0___boxed(lean_object* v_w_1460_, lean_object* v_x_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_1460_, v_x_1461_, v___y_1462_);
lean_dec(v_w_1460_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(lean_object* v_f_1464_, lean_object* v_w_1465_, lean_object* v_indent_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___x_1468_; uint8_t v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1468_ = lean_box(1);
v___x_1469_ = 0;
v___x_1470_ = lean_nat_to_int(v_indent_1466_);
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1472_, 0, v_f_1464_);
lean_ctor_set(v___x_1472_, 1, v___x_1470_);
lean_ctor_set(v___x_1472_, 2, v___x_1471_);
v___x_1473_ = lean_box(0);
v___x_1474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1472_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1475_, 0, v___x_1468_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
lean_ctor_set_uint8(v___x_1475_, sizeof(void*)*2, v___x_1469_);
v___x_1476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
lean_ctor_set(v___x_1476_, 1, v___x_1473_);
v___x_1477_ = l___private_Init_Data_Format_Basic_0__Std_Format_be___at___00Std_Format_prettyM___at___00Std_Format_pretty_spec__0_spec__0(v_w_1465_, v___x_1476_, v___y_1467_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0___boxed(lean_object* v_f_1478_, lean_object* v_w_1479_, lean_object* v_indent_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(v_f_1478_, v_w_1479_, v_indent_1480_, v___y_1481_);
lean_dec(v_w_1479_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty(lean_object* v_f_1483_, lean_object* v_width_1484_, lean_object* v_indent_1485_, lean_object* v_column_1486_){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v_snd_1490_; lean_object* v_out_1491_; 
v___x_1487_ = ((lean_object*)(l_Std_Format_isEmpty___closed__0));
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
lean_ctor_set(v___x_1488_, 1, v_column_1486_);
v___x_1489_ = l_Std_Format_prettyM___at___00Std_Format_pretty_spec__0(v_f_1483_, v_width_1484_, v_indent_1485_, v___x_1488_);
v_snd_1490_ = lean_ctor_get(v___x_1489_, 1);
lean_inc(v_snd_1490_);
lean_dec_ref(v___x_1489_);
v_out_1491_ = lean_ctor_get(v_snd_1490_, 0);
lean_inc_ref(v_out_1491_);
lean_dec(v_snd_1490_);
return v_out_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty___boxed(lean_object* v_f_1492_, lean_object* v_width_1493_, lean_object* v_indent_1494_, lean_object* v_column_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Std_Format_pretty(v_f_1492_, v_width_1493_, v_indent_1494_, v_column_1495_);
lean_dec(v_width_1493_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0(lean_object* v_f_1497_){
_start:
{
lean_inc(v_f_1497_);
return v_f_1497_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object* v_f_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Std_instToFormatFormat___lam__0(v_f_1498_);
lean_dec(v_f_1498_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_instToFormatString___lam__0(lean_object* v_s_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1503_, 0, v_s_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg___lam__0(lean_object* v_x_1506_, lean_object* v_inst_1507_, lean_object* v_x1_1508_, lean_object* v_x2_1509_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1510_, 0, v_x1_1508_);
lean_ctor_set(v___x_1510_, 1, v_x_1506_);
v___x_1511_ = lean_apply_1(v_inst_1507_, v_x2_1509_);
v___x_1512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1510_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___redArg(lean_object* v_inst_1513_, lean_object* v_x_1514_, lean_object* v_x_1515_){
_start:
{
if (lean_obj_tag(v_x_1514_) == 0)
{
lean_object* v___x_1516_; 
lean_dec(v_x_1515_);
lean_dec_ref(v_inst_1513_);
v___x_1516_ = lean_box(0);
return v___x_1516_;
}
else
{
lean_object* v_tail_1517_; 
v_tail_1517_ = lean_ctor_get(v_x_1514_, 1);
if (lean_obj_tag(v_tail_1517_) == 0)
{
lean_object* v_head_1518_; lean_object* v___x_1519_; 
lean_dec(v_x_1515_);
v_head_1518_ = lean_ctor_get(v_x_1514_, 0);
lean_inc(v_head_1518_);
lean_dec_ref_known(v_x_1514_, 2);
v___x_1519_ = lean_apply_1(v_inst_1513_, v_head_1518_);
return v___x_1519_;
}
else
{
lean_object* v_head_1520_; lean_object* v___f_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
lean_inc(v_tail_1517_);
v_head_1520_ = lean_ctor_get(v_x_1514_, 0);
lean_inc(v_head_1520_);
lean_dec_ref_known(v_x_1514_, 2);
lean_inc_ref(v_inst_1513_);
v___f_1521_ = lean_alloc_closure((void*)(l_Std_Format_joinSep___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1521_, 0, v_x_1515_);
lean_closure_set(v___f_1521_, 1, v_inst_1513_);
v___x_1522_ = lean_apply_1(v_inst_1513_, v_head_1520_);
v___x_1523_ = l_List_foldl___redArg(v___f_1521_, v___x_1522_, v_tail_1517_);
return v___x_1523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep(lean_object* v_00_u03b1_1524_, lean_object* v_inst_1525_, lean_object* v_x_1526_, lean_object* v_x_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Std_Format_joinSep___redArg(v_inst_1525_, v_x_1526_, v_x_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg___lam__0(lean_object* v_pre_1529_, lean_object* v_inst_1530_, lean_object* v_x1_1531_, lean_object* v_x2_1532_){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1533_, 0, v_x1_1531_);
lean_ctor_set(v___x_1533_, 1, v_pre_1529_);
v___x_1534_ = lean_apply_1(v_inst_1530_, v_x2_1532_);
v___x_1535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin___redArg(lean_object* v_inst_1536_, lean_object* v_pre_1537_, lean_object* v_x_1538_){
_start:
{
if (lean_obj_tag(v_x_1538_) == 0)
{
lean_object* v___x_1539_; 
lean_dec(v_pre_1537_);
lean_dec_ref(v_inst_1536_);
v___x_1539_ = lean_box(0);
return v___x_1539_;
}
else
{
lean_object* v_head_1540_; lean_object* v_tail_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1551_; 
v_head_1540_ = lean_ctor_get(v_x_1538_, 0);
v_tail_1541_ = lean_ctor_get(v_x_1538_, 1);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_x_1538_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1543_ = v_x_1538_;
v_isShared_1544_ = v_isSharedCheck_1551_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_tail_1541_);
lean_inc(v_head_1540_);
lean_dec(v_x_1538_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1551_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___f_1545_; lean_object* v___x_1546_; lean_object* v___x_1548_; 
lean_inc_ref(v_inst_1536_);
lean_inc(v_pre_1537_);
v___f_1545_ = lean_alloc_closure((void*)(l_Std_Format_prefixJoin___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1545_, 0, v_pre_1537_);
lean_closure_set(v___f_1545_, 1, v_inst_1536_);
v___x_1546_ = lean_apply_1(v_inst_1536_, v_head_1540_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set_tag(v___x_1543_, 5);
lean_ctor_set(v___x_1543_, 1, v___x_1546_);
lean_ctor_set(v___x_1543_, 0, v_pre_1537_);
v___x_1548_ = v___x_1543_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_pre_1537_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_List_foldl___redArg(v___f_1545_, v___x_1548_, v_tail_1541_);
return v___x_1549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_prefixJoin(lean_object* v_00_u03b1_1552_, lean_object* v_inst_1553_, lean_object* v_pre_1554_, lean_object* v_x_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Std_Format_prefixJoin___redArg(v_inst_1553_, v_pre_1554_, v_x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg___lam__0(lean_object* v_inst_1557_, lean_object* v_x_1558_, lean_object* v_x1_1559_, lean_object* v_x2_1560_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1561_ = lean_apply_1(v_inst_1557_, v_x2_1560_);
v___x_1562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_x1_1559_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
lean_ctor_set(v___x_1563_, 1, v_x_1558_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix___redArg(lean_object* v_inst_1564_, lean_object* v_x_1565_, lean_object* v_x_1566_){
_start:
{
if (lean_obj_tag(v_x_1565_) == 0)
{
lean_object* v___x_1567_; 
lean_dec(v_x_1566_);
lean_dec_ref(v_inst_1564_);
v___x_1567_ = lean_box(0);
return v___x_1567_;
}
else
{
lean_object* v_head_1568_; lean_object* v_tail_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1579_; 
v_head_1568_ = lean_ctor_get(v_x_1565_, 0);
v_tail_1569_ = lean_ctor_get(v_x_1565_, 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_x_1565_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1571_ = v_x_1565_;
v_isShared_1572_ = v_isSharedCheck_1579_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_tail_1569_);
lean_inc(v_head_1568_);
lean_dec(v_x_1565_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1579_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___f_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
lean_inc(v_x_1566_);
lean_inc_ref(v_inst_1564_);
v___f_1573_ = lean_alloc_closure((void*)(l_Std_Format_joinSuffix___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1573_, 0, v_inst_1564_);
lean_closure_set(v___f_1573_, 1, v_x_1566_);
v___x_1574_ = lean_apply_1(v_inst_1564_, v_head_1568_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 5);
lean_ctor_set(v___x_1571_, 1, v_x_1566_);
lean_ctor_set(v___x_1571_, 0, v___x_1574_);
v___x_1576_ = v___x_1571_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_x_1566_);
v___x_1576_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_List_foldl___redArg(v___f_1573_, v___x_1576_, v_tail_1569_);
return v___x_1577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSuffix(lean_object* v_00_u03b1_1580_, lean_object* v_inst_1581_, lean_object* v_x_1582_, lean_object* v_x_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Std_Format_joinSuffix___redArg(v_inst_1581_, v_x_1582_, v_x_1583_);
return v___x_1584_;
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
