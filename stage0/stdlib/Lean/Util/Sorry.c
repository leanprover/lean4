// Lean compiler output
// Module: Lean.Util.Sorry
// Imports: public import Lean.Util.FindExpr public import Lean.Declaration
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
static const lean_string_object l_Lean_Expr_isSorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sorryAx"};
static const lean_object* l_Lean_Expr_isSorry___closed__0 = (const lean_object*)&l_Lean_Expr_isSorry___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Expr_isSorry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isSorry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 190, 164, 146, 38, 179, 69, 72)}};
static const lean_object* l_Lean_Expr_isSorry___closed__1 = (const lean_object*)&l_Lean_Expr_isSorry___closed__1_value;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isSorry___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_isSyntheticSorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Expr_isSyntheticSorry___closed__0 = (const lean_object*)&l_Lean_Expr_isSyntheticSorry___closed__0_value;
static const lean_string_object l_Lean_Expr_isSyntheticSorry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Expr_isSyntheticSorry___closed__1 = (const lean_object*)&l_Lean_Expr_isSyntheticSorry___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Expr_isSyntheticSorry___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isSyntheticSorry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Expr_isSyntheticSorry___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_isSyntheticSorry___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_isSyntheticSorry___closed__1_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Expr_isSyntheticSorry___closed__2 = (const lean_object*)&l_Lean_Expr_isSyntheticSorry___closed__2_value;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isSyntheticSorry___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_isNonSyntheticSorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Expr_isNonSyntheticSorry___closed__0 = (const lean_object*)&l_Lean_Expr_isNonSyntheticSorry___closed__0_value;
static const lean_ctor_object l_Lean_Expr_isNonSyntheticSorry___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isSyntheticSorry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Expr_isNonSyntheticSorry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_isNonSyntheticSorry___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_isNonSyntheticSorry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Expr_isNonSyntheticSorry___closed__1 = (const lean_object*)&l_Lean_Expr_isNonSyntheticSorry___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isNonSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isNonSyntheticSorry___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasSorry___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Expr_hasSorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hasSorry___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_hasSorry___closed__0 = (const lean_object*)&l_Lean_Expr_hasSorry___closed__0_value;
lean_object* lean_find_expr(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___boxed(lean_object*);
static const lean_closure_object l_Lean_Expr_hasSyntheticSorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isSyntheticSorry___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_hasSyntheticSorry___closed__0 = (const lean_object*)&l_Lean_Expr_hasSyntheticSorry___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasSyntheticSorry___boxed(lean_object*);
static const lean_closure_object l_Lean_Expr_hasNonSyntheticSorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isNonSyntheticSorry___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_hasNonSyntheticSorry___closed__0 = (const lean_object*)&l_Lean_Expr_hasNonSyntheticSorry___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Expr_hasNonSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasNonSyntheticSorry___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_hasSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_hasSorry___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_hasSyntheticSorry___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_hasNonSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_hasNonSyntheticSorry___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l_Lean_Expr_isSorry___closed__1));
x_3 = l_Lean_Expr_isAppOf(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isSorry(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSyntheticSorry(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_11; uint8_t x_12; 
x_11 = ((lean_object*)(l_Lean_Expr_isSorry___closed__1));
x_12 = l_Lean_Expr_isAppOf(x_1, x_11);
if (x_12 == 0)
{
x_2 = x_12;
goto block_10;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Expr_getAppNumArgs(x_1);
x_15 = lean_nat_dec_le(x_13, x_14);
lean_dec(x_14);
x_2 = x_15;
goto block_10;
}
block_10:
{
if (x_2 == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Expr_getAppNumArgs(x_1);
x_5 = lean_nat_sub(x_4, x_3);
lean_dec(x_4);
x_6 = lean_nat_sub(x_5, x_3);
lean_dec(x_5);
x_7 = l_Lean_Expr_getRevArg_x21(x_1, x_6);
x_8 = ((lean_object*)(l_Lean_Expr_isSyntheticSorry___closed__2));
x_9 = l_Lean_Expr_isConstOf(x_7, x_8);
lean_dec_ref(x_7);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isSyntheticSorry(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isNonSyntheticSorry(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_11; uint8_t x_12; 
x_11 = ((lean_object*)(l_Lean_Expr_isSorry___closed__1));
x_12 = l_Lean_Expr_isAppOf(x_1, x_11);
if (x_12 == 0)
{
x_2 = x_12;
goto block_10;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Expr_getAppNumArgs(x_1);
x_15 = lean_nat_dec_le(x_13, x_14);
lean_dec(x_14);
x_2 = x_15;
goto block_10;
}
block_10:
{
if (x_2 == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Expr_getAppNumArgs(x_1);
x_5 = lean_nat_sub(x_4, x_3);
lean_dec(x_4);
x_6 = lean_nat_sub(x_5, x_3);
lean_dec(x_5);
x_7 = l_Lean_Expr_getRevArg_x21(x_1, x_6);
x_8 = ((lean_object*)(l_Lean_Expr_isNonSyntheticSorry___closed__1));
x_9 = l_Lean_Expr_isConstOf(x_7, x_8);
lean_dec_ref(x_7);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isNonSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isNonSyntheticSorry(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasSorry___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l_Lean_Expr_isSorry___closed__1));
x_3 = l_Lean_Expr_isConstOf(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasSorry___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Expr_hasSorry___closed__0));
x_3 = lean_find_expr(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec_ref(x_3);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasSorry(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Expr_hasSyntheticSorry___closed__0));
x_3 = lean_find_expr(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec_ref(x_3);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasSyntheticSorry(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasNonSyntheticSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Expr_hasNonSyntheticSorry___closed__0));
x_3 = lean_find_expr(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec_ref(x_3);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasNonSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasNonSyntheticSorry(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasSorry(x_2);
return x_3;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(x_1, x_7);
x_9 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(x_8, x_6);
x_1 = x_9;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_Expr_hasSorry(x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
x_2 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_Expr_hasSorry(x_5);
x_7 = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(x_6, x_4);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(x_1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
if (x_1 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasSorry(x_5);
x_7 = x_11;
goto block_10;
}
else
{
x_7 = x_1;
goto block_10;
}
block_10:
{
uint8_t x_8; 
x_8 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(x_7, x_6);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
if (x_1 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasSorry(x_5);
x_7 = x_11;
goto block_10;
}
else
{
x_7 = x_1;
goto block_10;
}
block_10:
{
uint8_t x_8; uint8_t x_9; 
x_8 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(x_7, x_6);
x_9 = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(x_8, x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(lean_object* x_1, uint8_t x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 2);
x_6 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(x_2, x_5);
return x_6;
}
case 4:
{
return x_2;
}
case 5:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(x_2, x_7);
return x_8;
}
case 6:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 2);
x_10 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(x_2, x_9);
return x_10;
}
default: 
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_12, 2);
x_15 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(x_2, x_14);
x_16 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(x_15, x_13);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_hasSorry(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 0;
x_3 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_hasSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Declaration_hasSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasSyntheticSorry(x_2);
return x_3;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(x_1, x_7);
x_9 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(x_8, x_6);
x_1 = x_9;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_Expr_hasSyntheticSorry(x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
x_2 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_Expr_hasSyntheticSorry(x_5);
x_7 = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(x_6, x_4);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(x_1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
if (x_1 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasSyntheticSorry(x_5);
x_7 = x_11;
goto block_10;
}
else
{
x_7 = x_1;
goto block_10;
}
block_10:
{
uint8_t x_8; 
x_8 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(x_7, x_6);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
if (x_1 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasSyntheticSorry(x_5);
x_7 = x_11;
goto block_10;
}
else
{
x_7 = x_1;
goto block_10;
}
block_10:
{
uint8_t x_8; uint8_t x_9; 
x_8 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(x_7, x_6);
x_9 = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(x_8, x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(lean_object* x_1, uint8_t x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 2);
x_6 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(x_2, x_5);
return x_6;
}
case 4:
{
return x_2;
}
case 5:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(x_2, x_7);
return x_8;
}
case 6:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 2);
x_10 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(x_2, x_9);
return x_10;
}
default: 
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_12, 2);
x_15 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(x_2, x_14);
x_16 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(x_15, x_13);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_hasSyntheticSorry(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 0;
x_3 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_hasSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Declaration_hasSyntheticSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasNonSyntheticSorry(x_2);
return x_3;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(x_1, x_7);
x_9 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(x_8, x_6);
x_1 = x_9;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_Expr_hasNonSyntheticSorry(x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
x_2 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_Expr_hasNonSyntheticSorry(x_5);
x_7 = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(x_6, x_4);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(x_1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
if (x_1 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasNonSyntheticSorry(x_5);
x_7 = x_11;
goto block_10;
}
else
{
x_7 = x_1;
goto block_10;
}
block_10:
{
uint8_t x_8; 
x_8 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(x_7, x_6);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
if (x_1 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasNonSyntheticSorry(x_5);
x_7 = x_11;
goto block_10;
}
else
{
x_7 = x_1;
goto block_10;
}
block_10:
{
uint8_t x_8; uint8_t x_9; 
x_8 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(x_7, x_6);
x_9 = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(x_8, x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(lean_object* x_1, uint8_t x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 2);
x_6 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(x_2, x_5);
return x_6;
}
case 4:
{
return x_2;
}
case 5:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(x_2, x_7);
return x_8;
}
case 6:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 2);
x_10 = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(x_2, x_9);
return x_10;
}
default: 
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_12, 2);
x_15 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(x_2, x_14);
x_16 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(x_15, x_13);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_hasNonSyntheticSorry(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 0;
x_3 = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_hasNonSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Declaration_hasNonSyntheticSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Lean_Util_FindExpr(uint8_t builtin);
lean_object* initialize_Lean_Declaration(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Sorry(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_FindExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
