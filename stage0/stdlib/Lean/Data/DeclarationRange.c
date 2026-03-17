// Lean compiler output
// Module: Lean.Data.DeclarationRange
// Imports: public import Lean.Data.Position
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
extern lean_object* l_Lean_instInhabitedPosition_default;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_instReprPosition_repr___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_instDecidableEqPosition_decEq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedDeclarationRange_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedDeclarationRange_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclarationRange_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclarationRange;
LEAN_EXPORT uint8_t l_Lean_instDecidableEqDeclarationRange_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instDecidableEqDeclarationRange_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instDecidableEqDeclarationRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instDecidableEqDeclarationRange___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprDeclarationRange_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_instReprDeclarationRange_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_instReprDeclarationRange_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pos"};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprDeclarationRange_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprDeclarationRange_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_instReprDeclarationRange_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__4 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_instReprDeclarationRange_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_instReprDeclarationRange_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__3_value),((lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_instReprDeclarationRange_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__7;
static const lean_string_object l_Lean_instReprDeclarationRange_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__8 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_instReprDeclarationRange_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__9 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_instReprDeclarationRange_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "charUtf16"};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__10 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_instReprDeclarationRange_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__11 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_instReprDeclarationRange_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__12;
static const lean_string_object l_Lean_instReprDeclarationRange_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "endPos"};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__13 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_instReprDeclarationRange_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__14 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__14_value;
static lean_once_cell_t l_Lean_instReprDeclarationRange_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__15;
static const lean_string_object l_Lean_instReprDeclarationRange_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "endCharUtf16"};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__16 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_instReprDeclarationRange_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__16_value)}};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__17 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__17_value;
static lean_once_cell_t l_Lean_instReprDeclarationRange_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__18;
static const lean_string_object l_Lean_instReprDeclarationRange_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__19 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__19_value;
static lean_once_cell_t l_Lean_instReprDeclarationRange_repr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__20;
static lean_once_cell_t l_Lean_instReprDeclarationRange_repr___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__21;
static const lean_ctor_object l_Lean_instReprDeclarationRange_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__22 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__22_value;
static const lean_ctor_object l_Lean_instReprDeclarationRange_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__19_value)}};
static const lean_object* l_Lean_instReprDeclarationRange_repr___redArg___closed__23 = (const lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__23_value;
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationRange_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationRange_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationRange_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprDeclarationRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprDeclarationRange_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprDeclarationRange___closed__0 = (const lean_object*)&l_Lean_instReprDeclarationRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprDeclarationRange = (const lean_object*)&l_Lean_instReprDeclarationRange___closed__0_value;
static const lean_string_object l_Lean_instToExprDeclarationRange___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_instToExprDeclarationRange___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__0_value;
static const lean_string_object l_Lean_instToExprDeclarationRange___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "DeclarationRange"};
static const lean_object* l_Lean_instToExprDeclarationRange___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__1_value;
static const lean_string_object l_Lean_instToExprDeclarationRange___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_instToExprDeclarationRange___lam__0___closed__2 = (const lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_instToExprDeclarationRange___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instToExprDeclarationRange___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 40, 210, 72, 47, 189, 205, 127)}};
static const lean_ctor_object l_Lean_instToExprDeclarationRange___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__3_value_aux_1),((lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(56, 158, 56, 135, 240, 198, 44, 53)}};
static const lean_object* l_Lean_instToExprDeclarationRange___lam__0___closed__3 = (const lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_instToExprDeclarationRange___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprDeclarationRange___lam__0___closed__4;
static const lean_string_object l_Lean_instToExprDeclarationRange___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Position"};
static const lean_object* l_Lean_instToExprDeclarationRange___lam__0___closed__5 = (const lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_instToExprDeclarationRange___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instToExprDeclarationRange___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(65, 243, 169, 21, 0, 54, 19, 101)}};
static const lean_ctor_object l_Lean_instToExprDeclarationRange___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__6_value_aux_1),((lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 0, 160, 114, 110, 41, 100, 154)}};
static const lean_object* l_Lean_instToExprDeclarationRange___lam__0___closed__6 = (const lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_instToExprDeclarationRange___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprDeclarationRange___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_instToExprDeclarationRange___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToExprDeclarationRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprDeclarationRange___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprDeclarationRange___closed__0 = (const lean_object*)&l_Lean_instToExprDeclarationRange___closed__0_value;
static const lean_ctor_object l_Lean_instToExprDeclarationRange___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instToExprDeclarationRange___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprDeclarationRange___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 40, 210, 72, 47, 189, 205, 127)}};
static const lean_object* l_Lean_instToExprDeclarationRange___closed__1 = (const lean_object*)&l_Lean_instToExprDeclarationRange___closed__1_value;
static lean_once_cell_t l_Lean_instToExprDeclarationRange___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprDeclarationRange___closed__2;
static lean_once_cell_t l_Lean_instToExprDeclarationRange___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprDeclarationRange___closed__3;
LEAN_EXPORT lean_object* l_Lean_instToExprDeclarationRange;
static lean_once_cell_t l_Lean_instInhabitedDeclarationRanges_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedDeclarationRanges_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclarationRanges_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclarationRanges;
static const lean_string_object l_Lean_instReprDeclarationRanges_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "range"};
static const lean_object* l_Lean_instReprDeclarationRanges_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprDeclarationRanges_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_instReprDeclarationRanges_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDeclarationRanges_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprDeclarationRanges_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprDeclarationRanges_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprDeclarationRanges_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprDeclarationRanges_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprDeclarationRanges_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprDeclarationRanges_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprDeclarationRanges_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprDeclarationRanges_repr___redArg___closed__2_value),((lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprDeclarationRanges_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprDeclarationRanges_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_instReprDeclarationRanges_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprDeclarationRanges_repr___redArg___closed__4;
static const lean_string_object l_Lean_instReprDeclarationRanges_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "selectionRange"};
static const lean_object* l_Lean_instReprDeclarationRanges_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprDeclarationRanges_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_instReprDeclarationRanges_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDeclarationRanges_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprDeclarationRanges_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprDeclarationRanges_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_instReprDeclarationRanges_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprDeclarationRanges_repr___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationRanges_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationRanges_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationRanges_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprDeclarationRanges___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprDeclarationRanges_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprDeclarationRanges___closed__0 = (const lean_object*)&l_Lean_instReprDeclarationRanges___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprDeclarationRanges = (const lean_object*)&l_Lean_instReprDeclarationRanges___closed__0_value;
static const lean_string_object l_Lean_instToExprDeclarationRanges___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "DeclarationRanges"};
static const lean_object* l_Lean_instToExprDeclarationRanges___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprDeclarationRanges___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprDeclarationRanges___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 178, 233, 239, 130, 231, 201, 68)}};
static const lean_ctor_object l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(131, 154, 194, 162, 5, 60, 128, 221)}};
static const lean_object* l_Lean_instToExprDeclarationRanges___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprDeclarationRanges___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprDeclarationRanges___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprDeclarationRanges___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_instToExprDeclarationRanges___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToExprDeclarationRanges___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprDeclarationRanges___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprDeclarationRanges___closed__0 = (const lean_object*)&l_Lean_instToExprDeclarationRanges___closed__0_value;
static const lean_ctor_object l_Lean_instToExprDeclarationRanges___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprDeclarationRange___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instToExprDeclarationRanges___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprDeclarationRanges___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprDeclarationRanges___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 178, 233, 239, 130, 231, 201, 68)}};
static const lean_object* l_Lean_instToExprDeclarationRanges___closed__1 = (const lean_object*)&l_Lean_instToExprDeclarationRanges___closed__1_value;
static lean_once_cell_t l_Lean_instToExprDeclarationRanges___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprDeclarationRanges___closed__2;
static lean_once_cell_t l_Lean_instToExprDeclarationRanges___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprDeclarationRanges___closed__3;
LEAN_EXPORT lean_object* l_Lean_instToExprDeclarationRanges;
static lean_once_cell_t l_Lean_instInhabitedDeclarationLocation_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedDeclarationLocation_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclarationLocation_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclarationLocation;
LEAN_EXPORT uint8_t l_Lean_instDecidableEqDeclarationLocation_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instDecidableEqDeclarationLocation_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instDecidableEqDeclarationLocation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instDecidableEqDeclarationLocation___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprDeclarationLocation_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_instReprDeclarationLocation_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprDeclarationLocation_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_instReprDeclarationLocation_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDeclarationLocation_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprDeclarationLocation_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprDeclarationLocation_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprDeclarationLocation_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprDeclarationLocation_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprDeclarationLocation_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprDeclarationLocation_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprDeclarationLocation_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprDeclarationLocation_repr___redArg___closed__2_value),((lean_object*)&l_Lean_instReprDeclarationRange_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprDeclarationLocation_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprDeclarationLocation_repr___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationLocation_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationLocation_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationLocation_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprDeclarationLocation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprDeclarationLocation_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprDeclarationLocation___closed__0 = (const lean_object*)&l_Lean_instReprDeclarationLocation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprDeclarationLocation = (const lean_object*)&l_Lean_instReprDeclarationLocation___closed__0_value;
static lean_object* _init_l_Lean_instInhabitedDeclarationRange_default___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = l_Lean_instInhabitedPosition_default;
v___x_3_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
lean_ctor_set(v___x_3_, 2, v___x_2_);
lean_ctor_set(v___x_3_, 3, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclarationRange_default(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_obj_once(&l_Lean_instInhabitedDeclarationRange_default___closed__0, &l_Lean_instInhabitedDeclarationRange_default___closed__0_once, _init_l_Lean_instInhabitedDeclarationRange_default___closed__0);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclarationRange(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = l_Lean_instInhabitedDeclarationRange_default;
return v___x_5_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqDeclarationRange_decEq(lean_object* v_x_6_, lean_object* v_x_7_){
_start:
{
lean_object* v_pos_8_; lean_object* v_charUtf16_9_; lean_object* v_endPos_10_; lean_object* v_endCharUtf16_11_; lean_object* v_pos_12_; lean_object* v_charUtf16_13_; lean_object* v_endPos_14_; lean_object* v_endCharUtf16_15_; uint8_t v___x_16_; 
v_pos_8_ = lean_ctor_get(v_x_6_, 0);
v_charUtf16_9_ = lean_ctor_get(v_x_6_, 1);
v_endPos_10_ = lean_ctor_get(v_x_6_, 2);
v_endCharUtf16_11_ = lean_ctor_get(v_x_6_, 3);
v_pos_12_ = lean_ctor_get(v_x_7_, 0);
v_charUtf16_13_ = lean_ctor_get(v_x_7_, 1);
v_endPos_14_ = lean_ctor_get(v_x_7_, 2);
v_endCharUtf16_15_ = lean_ctor_get(v_x_7_, 3);
v___x_16_ = l_Lean_instDecidableEqPosition_decEq(v_pos_8_, v_pos_12_);
if (v___x_16_ == 0)
{
return v___x_16_;
}
else
{
uint8_t v___x_17_; 
v___x_17_ = lean_nat_dec_eq(v_charUtf16_9_, v_charUtf16_13_);
if (v___x_17_ == 0)
{
return v___x_17_;
}
else
{
uint8_t v___x_18_; 
v___x_18_ = l_Lean_instDecidableEqPosition_decEq(v_endPos_10_, v_endPos_14_);
if (v___x_18_ == 0)
{
return v___x_18_;
}
else
{
uint8_t v___x_19_; 
v___x_19_ = lean_nat_dec_eq(v_endCharUtf16_11_, v_endCharUtf16_15_);
return v___x_19_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqDeclarationRange_decEq___boxed(lean_object* v_x_20_, lean_object* v_x_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l_Lean_instDecidableEqDeclarationRange_decEq(v_x_20_, v_x_21_);
lean_dec_ref(v_x_21_);
lean_dec_ref(v_x_20_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqDeclarationRange(lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
uint8_t v___x_26_; 
v___x_26_ = l_Lean_instDecidableEqDeclarationRange_decEq(v_x_24_, v_x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqDeclarationRange___boxed(lean_object* v_x_27_, lean_object* v_x_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_Lean_instDecidableEqDeclarationRange(v_x_27_, v_x_28_);
lean_dec_ref(v_x_28_);
lean_dec_ref(v_x_27_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprDeclarationRange_repr_spec__0(lean_object* v_a_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_nat_to_int(v_a_31_);
return v___x_32_;
}
}
static lean_object* _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_unsigned_to_nat(7u);
v___x_47_ = lean_nat_to_int(v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(13u);
v___x_55_ = lean_nat_to_int(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(10u);
v___x_60_ = lean_nat_to_int(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(16u);
v___x_65_ = lean_nat_to_int(v___x_64_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = ((lean_object*)(l_Lean_instReprDeclarationRange_repr___redArg___closed__0));
v___x_68_ = lean_string_length(v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_obj_once(&l_Lean_instReprDeclarationRange_repr___redArg___closed__20, &l_Lean_instReprDeclarationRange_repr___redArg___closed__20_once, _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__20);
v___x_70_ = lean_nat_to_int(v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationRange_repr___redArg(lean_object* v_x_75_){
_start:
{
lean_object* v_pos_76_; lean_object* v_charUtf16_77_; lean_object* v_endPos_78_; lean_object* v_endCharUtf16_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v_pos_76_ = lean_ctor_get(v_x_75_, 0);
lean_inc_ref(v_pos_76_);
v_charUtf16_77_ = lean_ctor_get(v_x_75_, 1);
lean_inc(v_charUtf16_77_);
v_endPos_78_ = lean_ctor_get(v_x_75_, 2);
lean_inc_ref(v_endPos_78_);
v_endCharUtf16_79_ = lean_ctor_get(v_x_75_, 3);
lean_inc(v_endCharUtf16_79_);
lean_dec_ref(v_x_75_);
v___x_80_ = ((lean_object*)(l_Lean_instReprDeclarationRange_repr___redArg___closed__5));
v___x_81_ = ((lean_object*)(l_Lean_instReprDeclarationRange_repr___redArg___closed__6));
v___x_82_ = lean_obj_once(&l_Lean_instReprDeclarationRange_repr___redArg___closed__7, &l_Lean_instReprDeclarationRange_repr___redArg___closed__7_once, _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__7);
v___x_83_ = l_Lean_instReprPosition_repr___redArg(v_pos_76_);
v___x_84_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = 0;
v___x_86_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_86_, 0, v___x_84_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*1, v___x_85_);
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_81_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = ((lean_object*)(l_Lean_instReprDeclarationRange_repr___redArg___closed__9));
v___x_89_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = lean_box(1);
v___x_91_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = ((lean_object*)(l_Lean_instReprDeclarationRange_repr___redArg___closed__11));
v___x_93_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___x_80_);
v___x_95_ = lean_obj_once(&l_Lean_instReprDeclarationRange_repr___redArg___closed__12, &l_Lean_instReprDeclarationRange_repr___redArg___closed__12_once, _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__12);
v___x_96_ = l_Nat_reprFast(v_charUtf16_77_);
v___x_97_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
v___x_98_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_95_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set_uint8(v___x_99_, sizeof(void*)*1, v___x_85_);
v___x_100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_94_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_88_);
v___x_102_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_90_);
v___x_103_ = ((lean_object*)(l_Lean_instReprDeclarationRange_repr___redArg___closed__14));
v___x_104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v___x_80_);
v___x_106_ = lean_obj_once(&l_Lean_instReprDeclarationRange_repr___redArg___closed__15, &l_Lean_instReprDeclarationRange_repr___redArg___closed__15_once, _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__15);
v___x_107_ = l_Lean_instReprPosition_repr___redArg(v_endPos_78_);
v___x_108_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set_uint8(v___x_109_, sizeof(void*)*1, v___x_85_);
v___x_110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_105_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v___x_88_);
v___x_112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v___x_90_);
v___x_113_ = ((lean_object*)(l_Lean_instReprDeclarationRange_repr___redArg___closed__17));
v___x_114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_112_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_80_);
v___x_116_ = lean_obj_once(&l_Lean_instReprDeclarationRange_repr___redArg___closed__18, &l_Lean_instReprDeclarationRange_repr___redArg___closed__18_once, _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__18);
v___x_117_ = l_Nat_reprFast(v_endCharUtf16_79_);
v___x_118_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
v___x_119_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_116_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*1, v___x_85_);
v___x_121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_115_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = lean_obj_once(&l_Lean_instReprDeclarationRange_repr___redArg___closed__21, &l_Lean_instReprDeclarationRange_repr___redArg___closed__21_once, _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__21);
v___x_123_ = ((lean_object*)(l_Lean_instReprDeclarationRange_repr___redArg___closed__22));
v___x_124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v___x_121_);
v___x_125_ = ((lean_object*)(l_Lean_instReprDeclarationRange_repr___redArg___closed__23));
v___x_126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_124_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_122_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*1, v___x_85_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationRange_repr(lean_object* v_x_129_, lean_object* v_prec_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_instReprDeclarationRange_repr___redArg(v_x_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationRange_repr___boxed(lean_object* v_x_132_, lean_object* v_prec_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_instReprDeclarationRange_repr(v_x_132_, v_prec_133_);
lean_dec(v_prec_133_);
return v_res_134_;
}
}
static lean_object* _init_l_Lean_instToExprDeclarationRange___lam__0___closed__4(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_box(0);
v___x_145_ = ((lean_object*)(l_Lean_instToExprDeclarationRange___lam__0___closed__3));
v___x_146_ = l_Lean_mkConst(v___x_145_, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_instToExprDeclarationRange___lam__0___closed__7(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_box(0);
v___x_153_ = ((lean_object*)(l_Lean_instToExprDeclarationRange___lam__0___closed__6));
v___x_154_ = l_Lean_mkConst(v___x_153_, v___x_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprDeclarationRange___lam__0(lean_object* v_r_155_){
_start:
{
lean_object* v_pos_156_; lean_object* v_endPos_157_; lean_object* v_charUtf16_158_; lean_object* v_endCharUtf16_159_; lean_object* v_line_160_; lean_object* v_column_161_; lean_object* v_line_162_; lean_object* v_column_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_pos_156_ = lean_ctor_get(v_r_155_, 0);
lean_inc_ref(v_pos_156_);
v_endPos_157_ = lean_ctor_get(v_r_155_, 2);
lean_inc_ref(v_endPos_157_);
v_charUtf16_158_ = lean_ctor_get(v_r_155_, 1);
lean_inc(v_charUtf16_158_);
v_endCharUtf16_159_ = lean_ctor_get(v_r_155_, 3);
lean_inc(v_endCharUtf16_159_);
lean_dec_ref(v_r_155_);
v_line_160_ = lean_ctor_get(v_pos_156_, 0);
lean_inc(v_line_160_);
v_column_161_ = lean_ctor_get(v_pos_156_, 1);
lean_inc(v_column_161_);
lean_dec_ref(v_pos_156_);
v_line_162_ = lean_ctor_get(v_endPos_157_, 0);
lean_inc(v_line_162_);
v_column_163_ = lean_ctor_get(v_endPos_157_, 1);
lean_inc(v_column_163_);
lean_dec_ref(v_endPos_157_);
v___x_164_ = lean_obj_once(&l_Lean_instToExprDeclarationRange___lam__0___closed__4, &l_Lean_instToExprDeclarationRange___lam__0___closed__4_once, _init_l_Lean_instToExprDeclarationRange___lam__0___closed__4);
v___x_165_ = lean_obj_once(&l_Lean_instToExprDeclarationRange___lam__0___closed__7, &l_Lean_instToExprDeclarationRange___lam__0___closed__7_once, _init_l_Lean_instToExprDeclarationRange___lam__0___closed__7);
v___x_166_ = l_Lean_mkNatLit(v_line_160_);
v___x_167_ = l_Lean_mkNatLit(v_column_161_);
v___x_168_ = lean_unsigned_to_nat(2u);
v___x_169_ = lean_mk_empty_array_with_capacity(v___x_168_);
lean_inc_ref(v___x_169_);
v___x_170_ = lean_array_push(v___x_169_, v___x_166_);
v___x_171_ = lean_array_push(v___x_170_, v___x_167_);
v___x_172_ = l_Lean_mkAppN(v___x_165_, v___x_171_);
lean_dec_ref(v___x_171_);
v___x_173_ = l_Lean_mkNatLit(v_charUtf16_158_);
v___x_174_ = l_Lean_mkNatLit(v_line_162_);
v___x_175_ = l_Lean_mkNatLit(v_column_163_);
v___x_176_ = lean_array_push(v___x_169_, v___x_174_);
v___x_177_ = lean_array_push(v___x_176_, v___x_175_);
v___x_178_ = l_Lean_mkAppN(v___x_165_, v___x_177_);
lean_dec_ref(v___x_177_);
v___x_179_ = l_Lean_mkNatLit(v_endCharUtf16_159_);
v___x_180_ = lean_unsigned_to_nat(4u);
v___x_181_ = lean_mk_empty_array_with_capacity(v___x_180_);
v___x_182_ = lean_array_push(v___x_181_, v___x_172_);
v___x_183_ = lean_array_push(v___x_182_, v___x_173_);
v___x_184_ = lean_array_push(v___x_183_, v___x_178_);
v___x_185_ = lean_array_push(v___x_184_, v___x_179_);
v___x_186_ = l_Lean_mkAppN(v___x_164_, v___x_185_);
lean_dec_ref(v___x_185_);
return v___x_186_;
}
}
static lean_object* _init_l_Lean_instToExprDeclarationRange___closed__2(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_box(0);
v___x_192_ = ((lean_object*)(l_Lean_instToExprDeclarationRange___closed__1));
v___x_193_ = l_Lean_mkConst(v___x_192_, v___x_191_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_instToExprDeclarationRange___closed__3(void){
_start:
{
lean_object* v___x_194_; lean_object* v___f_195_; lean_object* v___x_196_; 
v___x_194_ = lean_obj_once(&l_Lean_instToExprDeclarationRange___closed__2, &l_Lean_instToExprDeclarationRange___closed__2_once, _init_l_Lean_instToExprDeclarationRange___closed__2);
v___f_195_ = ((lean_object*)(l_Lean_instToExprDeclarationRange___closed__0));
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___f_195_);
lean_ctor_set(v___x_196_, 1, v___x_194_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_instToExprDeclarationRange(void){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_obj_once(&l_Lean_instToExprDeclarationRange___closed__3, &l_Lean_instToExprDeclarationRange___closed__3_once, _init_l_Lean_instToExprDeclarationRange___closed__3);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclarationRanges_default___closed__0(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = l_Lean_instInhabitedDeclarationRange_default;
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclarationRanges_default(void){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Lean_instInhabitedDeclarationRanges_default___closed__0, &l_Lean_instInhabitedDeclarationRanges_default___closed__0_once, _init_l_Lean_instInhabitedDeclarationRanges_default___closed__0);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclarationRanges(void){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_instInhabitedDeclarationRanges_default;
return v___x_201_;
}
}
static lean_object* _init_l_Lean_instReprDeclarationRanges_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(9u);
v___x_212_ = lean_nat_to_int(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_instReprDeclarationRanges_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_unsigned_to_nat(18u);
v___x_217_ = lean_nat_to_int(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationRanges_repr___redArg(lean_object* v_x_218_){
_start:
{
lean_object* v_range_219_; lean_object* v_selectionRange_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_253_; 
v_range_219_ = lean_ctor_get(v_x_218_, 0);
v_selectionRange_220_ = lean_ctor_get(v_x_218_, 1);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_218_);
if (v_isSharedCheck_253_ == 0)
{
v___x_222_ = v_x_218_;
v_isShared_223_ = v_isSharedCheck_253_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_selectionRange_220_);
lean_inc(v_range_219_);
lean_dec(v_x_218_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_253_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_224_ = ((lean_object*)(l_Lean_instReprDeclarationRange_repr___redArg___closed__5));
v___x_225_ = ((lean_object*)(l_Lean_instReprDeclarationRanges_repr___redArg___closed__3));
v___x_226_ = lean_obj_once(&l_Lean_instReprDeclarationRanges_repr___redArg___closed__4, &l_Lean_instReprDeclarationRanges_repr___redArg___closed__4_once, _init_l_Lean_instReprDeclarationRanges_repr___redArg___closed__4);
v___x_227_ = l_Lean_instReprDeclarationRange_repr___redArg(v_range_219_);
if (v_isShared_223_ == 0)
{
lean_ctor_set_tag(v___x_222_, 4);
lean_ctor_set(v___x_222_, 1, v___x_227_);
lean_ctor_set(v___x_222_, 0, v___x_226_);
v___x_229_ = v___x_222_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v___x_227_);
v___x_229_ = v_reuseFailAlloc_252_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_230_ = 0;
v___x_231_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*1, v___x_230_);
v___x_232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_225_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = ((lean_object*)(l_Lean_instReprDeclarationRange_repr___redArg___closed__9));
v___x_234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = lean_box(1);
v___x_236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = ((lean_object*)(l_Lean_instReprDeclarationRanges_repr___redArg___closed__6));
v___x_238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_236_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_224_);
v___x_240_ = lean_obj_once(&l_Lean_instReprDeclarationRanges_repr___redArg___closed__7, &l_Lean_instReprDeclarationRanges_repr___redArg___closed__7_once, _init_l_Lean_instReprDeclarationRanges_repr___redArg___closed__7);
v___x_241_ = l_Lean_instReprDeclarationRange_repr___redArg(v_selectionRange_220_);
v___x_242_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*1, v___x_230_);
v___x_244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_239_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_obj_once(&l_Lean_instReprDeclarationRange_repr___redArg___closed__21, &l_Lean_instReprDeclarationRange_repr___redArg___closed__21_once, _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__21);
v___x_246_ = ((lean_object*)(l_Lean_instReprDeclarationRange_repr___redArg___closed__22));
v___x_247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___x_244_);
v___x_248_ = ((lean_object*)(l_Lean_instReprDeclarationRange_repr___redArg___closed__23));
v___x_249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_245_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*1, v___x_230_);
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationRanges_repr(lean_object* v_x_254_, lean_object* v_prec_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_instReprDeclarationRanges_repr___redArg(v_x_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationRanges_repr___boxed(lean_object* v_x_257_, lean_object* v_prec_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_instReprDeclarationRanges_repr(v_x_257_, v_prec_258_);
lean_dec(v_prec_258_);
return v_res_259_;
}
}
static lean_object* _init_l_Lean_instToExprDeclarationRanges___lam__0___closed__2(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_box(0);
v___x_268_ = ((lean_object*)(l_Lean_instToExprDeclarationRanges___lam__0___closed__1));
v___x_269_ = l_Lean_mkConst(v___x_268_, v___x_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprDeclarationRanges___lam__0(lean_object* v_r_270_){
_start:
{
lean_object* v_range_271_; lean_object* v_selectionRange_272_; lean_object* v_pos_273_; lean_object* v_charUtf16_274_; lean_object* v_endPos_275_; lean_object* v_endCharUtf16_276_; lean_object* v___x_277_; lean_object* v_line_278_; lean_object* v_column_279_; lean_object* v_line_280_; lean_object* v_column_281_; lean_object* v___x_282_; lean_object* v_pos_283_; lean_object* v_charUtf16_284_; lean_object* v_endPos_285_; lean_object* v_endCharUtf16_286_; lean_object* v_line_287_; lean_object* v_column_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v_line_297_; lean_object* v_column_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_range_271_ = lean_ctor_get(v_r_270_, 0);
lean_inc_ref(v_range_271_);
v_selectionRange_272_ = lean_ctor_get(v_r_270_, 1);
lean_inc_ref(v_selectionRange_272_);
lean_dec_ref(v_r_270_);
v_pos_273_ = lean_ctor_get(v_range_271_, 0);
lean_inc_ref(v_pos_273_);
v_charUtf16_274_ = lean_ctor_get(v_range_271_, 1);
lean_inc(v_charUtf16_274_);
v_endPos_275_ = lean_ctor_get(v_range_271_, 2);
lean_inc_ref(v_endPos_275_);
v_endCharUtf16_276_ = lean_ctor_get(v_range_271_, 3);
lean_inc(v_endCharUtf16_276_);
lean_dec_ref(v_range_271_);
v___x_277_ = lean_obj_once(&l_Lean_instToExprDeclarationRanges___lam__0___closed__2, &l_Lean_instToExprDeclarationRanges___lam__0___closed__2_once, _init_l_Lean_instToExprDeclarationRanges___lam__0___closed__2);
v_line_278_ = lean_ctor_get(v_pos_273_, 0);
lean_inc(v_line_278_);
v_column_279_ = lean_ctor_get(v_pos_273_, 1);
lean_inc(v_column_279_);
lean_dec_ref(v_pos_273_);
v_line_280_ = lean_ctor_get(v_endPos_275_, 0);
lean_inc(v_line_280_);
v_column_281_ = lean_ctor_get(v_endPos_275_, 1);
lean_inc(v_column_281_);
lean_dec_ref(v_endPos_275_);
v___x_282_ = lean_obj_once(&l_Lean_instToExprDeclarationRange___lam__0___closed__4, &l_Lean_instToExprDeclarationRange___lam__0___closed__4_once, _init_l_Lean_instToExprDeclarationRange___lam__0___closed__4);
v_pos_283_ = lean_ctor_get(v_selectionRange_272_, 0);
lean_inc_ref(v_pos_283_);
v_charUtf16_284_ = lean_ctor_get(v_selectionRange_272_, 1);
lean_inc(v_charUtf16_284_);
v_endPos_285_ = lean_ctor_get(v_selectionRange_272_, 2);
lean_inc_ref(v_endPos_285_);
v_endCharUtf16_286_ = lean_ctor_get(v_selectionRange_272_, 3);
lean_inc(v_endCharUtf16_286_);
lean_dec_ref(v_selectionRange_272_);
v_line_287_ = lean_ctor_get(v_pos_283_, 0);
lean_inc(v_line_287_);
v_column_288_ = lean_ctor_get(v_pos_283_, 1);
lean_inc(v_column_288_);
lean_dec_ref(v_pos_283_);
v___x_289_ = lean_obj_once(&l_Lean_instToExprDeclarationRange___lam__0___closed__7, &l_Lean_instToExprDeclarationRange___lam__0___closed__7_once, _init_l_Lean_instToExprDeclarationRange___lam__0___closed__7);
v___x_290_ = l_Lean_mkNatLit(v_line_278_);
v___x_291_ = l_Lean_mkNatLit(v_column_279_);
v___x_292_ = lean_unsigned_to_nat(2u);
v___x_293_ = lean_mk_empty_array_with_capacity(v___x_292_);
lean_inc_ref(v___x_293_);
v___x_294_ = lean_array_push(v___x_293_, v___x_290_);
v___x_295_ = lean_array_push(v___x_294_, v___x_291_);
v___x_296_ = l_Lean_mkAppN(v___x_289_, v___x_295_);
lean_dec_ref(v___x_295_);
v_line_297_ = lean_ctor_get(v_endPos_285_, 0);
lean_inc(v_line_297_);
v_column_298_ = lean_ctor_get(v_endPos_285_, 1);
lean_inc(v_column_298_);
lean_dec_ref(v_endPos_285_);
v___x_299_ = l_Lean_mkNatLit(v_line_280_);
v___x_300_ = l_Lean_mkNatLit(v_column_281_);
lean_inc_ref(v___x_293_);
v___x_301_ = lean_array_push(v___x_293_, v___x_299_);
v___x_302_ = lean_array_push(v___x_301_, v___x_300_);
v___x_303_ = l_Lean_mkAppN(v___x_289_, v___x_302_);
lean_dec_ref(v___x_302_);
v___x_304_ = l_Lean_mkNatLit(v_charUtf16_274_);
v___x_305_ = l_Lean_mkNatLit(v_endCharUtf16_276_);
v___x_306_ = lean_unsigned_to_nat(4u);
v___x_307_ = lean_mk_empty_array_with_capacity(v___x_306_);
lean_inc_ref(v___x_307_);
v___x_308_ = lean_array_push(v___x_307_, v___x_296_);
v___x_309_ = lean_array_push(v___x_308_, v___x_304_);
v___x_310_ = lean_array_push(v___x_309_, v___x_303_);
v___x_311_ = lean_array_push(v___x_310_, v___x_305_);
v___x_312_ = l_Lean_mkAppN(v___x_282_, v___x_311_);
lean_dec_ref(v___x_311_);
v___x_313_ = l_Lean_mkNatLit(v_line_287_);
v___x_314_ = l_Lean_mkNatLit(v_column_288_);
lean_inc_ref(v___x_293_);
v___x_315_ = lean_array_push(v___x_293_, v___x_313_);
v___x_316_ = lean_array_push(v___x_315_, v___x_314_);
v___x_317_ = l_Lean_mkAppN(v___x_289_, v___x_316_);
lean_dec_ref(v___x_316_);
v___x_318_ = l_Lean_mkNatLit(v_charUtf16_284_);
v___x_319_ = l_Lean_mkNatLit(v_line_297_);
v___x_320_ = l_Lean_mkNatLit(v_column_298_);
lean_inc_ref(v___x_293_);
v___x_321_ = lean_array_push(v___x_293_, v___x_319_);
v___x_322_ = lean_array_push(v___x_321_, v___x_320_);
v___x_323_ = l_Lean_mkAppN(v___x_289_, v___x_322_);
lean_dec_ref(v___x_322_);
v___x_324_ = l_Lean_mkNatLit(v_endCharUtf16_286_);
v___x_325_ = lean_array_push(v___x_307_, v___x_317_);
v___x_326_ = lean_array_push(v___x_325_, v___x_318_);
v___x_327_ = lean_array_push(v___x_326_, v___x_323_);
v___x_328_ = lean_array_push(v___x_327_, v___x_324_);
v___x_329_ = l_Lean_mkAppN(v___x_282_, v___x_328_);
lean_dec_ref(v___x_328_);
v___x_330_ = lean_array_push(v___x_293_, v___x_312_);
v___x_331_ = lean_array_push(v___x_330_, v___x_329_);
v___x_332_ = l_Lean_mkAppN(v___x_277_, v___x_331_);
lean_dec_ref(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_instToExprDeclarationRanges___closed__2(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_box(0);
v___x_338_ = ((lean_object*)(l_Lean_instToExprDeclarationRanges___closed__1));
v___x_339_ = l_Lean_mkConst(v___x_338_, v___x_337_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_instToExprDeclarationRanges___closed__3(void){
_start:
{
lean_object* v___x_340_; lean_object* v___f_341_; lean_object* v___x_342_; 
v___x_340_ = lean_obj_once(&l_Lean_instToExprDeclarationRanges___closed__2, &l_Lean_instToExprDeclarationRanges___closed__2_once, _init_l_Lean_instToExprDeclarationRanges___closed__2);
v___f_341_ = ((lean_object*)(l_Lean_instToExprDeclarationRanges___closed__0));
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___f_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
return v___x_342_;
}
}
static lean_object* _init_l_Lean_instToExprDeclarationRanges(void){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = lean_obj_once(&l_Lean_instToExprDeclarationRanges___closed__3, &l_Lean_instToExprDeclarationRanges___closed__3_once, _init_l_Lean_instToExprDeclarationRanges___closed__3);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclarationLocation_default___closed__0(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = l_Lean_instInhabitedDeclarationRange_default;
v___x_345_ = lean_box(0);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclarationLocation_default(void){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = lean_obj_once(&l_Lean_instInhabitedDeclarationLocation_default___closed__0, &l_Lean_instInhabitedDeclarationLocation_default___closed__0_once, _init_l_Lean_instInhabitedDeclarationLocation_default___closed__0);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclarationLocation(void){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_instInhabitedDeclarationLocation_default;
return v___x_348_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqDeclarationLocation_decEq(lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
lean_object* v_module_351_; lean_object* v_range_352_; lean_object* v_module_353_; lean_object* v_range_354_; uint8_t v___x_355_; 
v_module_351_ = lean_ctor_get(v_x_349_, 0);
v_range_352_ = lean_ctor_get(v_x_349_, 1);
v_module_353_ = lean_ctor_get(v_x_350_, 0);
v_range_354_ = lean_ctor_get(v_x_350_, 1);
v___x_355_ = lean_name_eq(v_module_351_, v_module_353_);
if (v___x_355_ == 0)
{
return v___x_355_;
}
else
{
uint8_t v___x_356_; 
v___x_356_ = l_Lean_instDecidableEqDeclarationRange_decEq(v_range_352_, v_range_354_);
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqDeclarationLocation_decEq___boxed(lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_Lean_instDecidableEqDeclarationLocation_decEq(v_x_357_, v_x_358_);
lean_dec_ref(v_x_358_);
lean_dec_ref(v_x_357_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqDeclarationLocation(lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
uint8_t v___x_363_; 
v___x_363_ = l_Lean_instDecidableEqDeclarationLocation_decEq(v_x_361_, v_x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqDeclarationLocation___boxed(lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_Lean_instDecidableEqDeclarationLocation(v_x_364_, v_x_365_);
lean_dec_ref(v_x_365_);
lean_dec_ref(v_x_364_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationLocation_repr___redArg(lean_object* v_x_377_){
_start:
{
lean_object* v_module_378_; lean_object* v_range_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_413_; 
v_module_378_ = lean_ctor_get(v_x_377_, 0);
v_range_379_ = lean_ctor_get(v_x_377_, 1);
v_isSharedCheck_413_ = !lean_is_exclusive(v_x_377_);
if (v_isSharedCheck_413_ == 0)
{
v___x_381_ = v_x_377_;
v_isShared_382_ = v_isSharedCheck_413_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_range_379_);
lean_inc(v_module_378_);
lean_dec(v_x_377_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_413_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_383_ = ((lean_object*)(l_Lean_instReprDeclarationRange_repr___redArg___closed__5));
v___x_384_ = ((lean_object*)(l_Lean_instReprDeclarationLocation_repr___redArg___closed__3));
v___x_385_ = lean_obj_once(&l_Lean_instReprDeclarationRange_repr___redArg___closed__15, &l_Lean_instReprDeclarationRange_repr___redArg___closed__15_once, _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__15);
v___x_386_ = lean_unsigned_to_nat(0u);
v___x_387_ = l_Lean_Name_reprPrec(v_module_378_, v___x_386_);
if (v_isShared_382_ == 0)
{
lean_ctor_set_tag(v___x_381_, 4);
lean_ctor_set(v___x_381_, 1, v___x_387_);
lean_ctor_set(v___x_381_, 0, v___x_385_);
v___x_389_ = v___x_381_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v___x_387_);
v___x_389_ = v_reuseFailAlloc_412_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
uint8_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_390_ = 0;
v___x_391_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_391_, 0, v___x_389_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*1, v___x_390_);
v___x_392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_384_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = ((lean_object*)(l_Lean_instReprDeclarationRange_repr___redArg___closed__9));
v___x_394_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = lean_box(1);
v___x_396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = ((lean_object*)(l_Lean_instReprDeclarationRanges_repr___redArg___closed__1));
v___x_398_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___x_383_);
v___x_400_ = lean_obj_once(&l_Lean_instReprDeclarationRanges_repr___redArg___closed__4, &l_Lean_instReprDeclarationRanges_repr___redArg___closed__4_once, _init_l_Lean_instReprDeclarationRanges_repr___redArg___closed__4);
v___x_401_ = l_Lean_instReprDeclarationRange_repr___redArg(v_range_379_);
v___x_402_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*1, v___x_390_);
v___x_404_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_399_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = lean_obj_once(&l_Lean_instReprDeclarationRange_repr___redArg___closed__21, &l_Lean_instReprDeclarationRange_repr___redArg___closed__21_once, _init_l_Lean_instReprDeclarationRange_repr___redArg___closed__21);
v___x_406_ = ((lean_object*)(l_Lean_instReprDeclarationRange_repr___redArg___closed__22));
v___x_407_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_404_);
v___x_408_ = ((lean_object*)(l_Lean_instReprDeclarationRange_repr___redArg___closed__23));
v___x_409_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_405_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set_uint8(v___x_411_, sizeof(void*)*1, v___x_390_);
return v___x_411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationLocation_repr(lean_object* v_x_414_, lean_object* v_prec_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_instReprDeclarationLocation_repr___redArg(v_x_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDeclarationLocation_repr___boxed(lean_object* v_x_417_, lean_object* v_prec_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_instReprDeclarationLocation_repr(v_x_417_, v_prec_418_);
lean_dec(v_prec_418_);
return v_res_419_;
}
}
lean_object* runtime_initialize_Lean_Data_Position(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_DeclarationRange(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Position(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedDeclarationRange_default = _init_l_Lean_instInhabitedDeclarationRange_default();
lean_mark_persistent(l_Lean_instInhabitedDeclarationRange_default);
l_Lean_instInhabitedDeclarationRange = _init_l_Lean_instInhabitedDeclarationRange();
lean_mark_persistent(l_Lean_instInhabitedDeclarationRange);
l_Lean_instToExprDeclarationRange = _init_l_Lean_instToExprDeclarationRange();
lean_mark_persistent(l_Lean_instToExprDeclarationRange);
l_Lean_instInhabitedDeclarationRanges_default = _init_l_Lean_instInhabitedDeclarationRanges_default();
lean_mark_persistent(l_Lean_instInhabitedDeclarationRanges_default);
l_Lean_instInhabitedDeclarationRanges = _init_l_Lean_instInhabitedDeclarationRanges();
lean_mark_persistent(l_Lean_instInhabitedDeclarationRanges);
l_Lean_instToExprDeclarationRanges = _init_l_Lean_instToExprDeclarationRanges();
lean_mark_persistent(l_Lean_instToExprDeclarationRanges);
l_Lean_instInhabitedDeclarationLocation_default = _init_l_Lean_instInhabitedDeclarationLocation_default();
lean_mark_persistent(l_Lean_instInhabitedDeclarationLocation_default);
l_Lean_instInhabitedDeclarationLocation = _init_l_Lean_instInhabitedDeclarationLocation();
lean_mark_persistent(l_Lean_instInhabitedDeclarationLocation);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_DeclarationRange(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Position(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_DeclarationRange(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Position(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_DeclarationRange(builtin);
}
#ifdef __cplusplus
}
#endif
