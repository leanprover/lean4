// Lean compiler output
// Module: Lean.Meta.HasNotBit
// Imports: public import Lean.Meta.Basic import Lean.Meta.MatchUtil
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_mkHasNotBit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_mkHasNotBit___closed__0 = (const lean_object*)&l_mkHasNotBit___closed__0_value;
static const lean_string_object l_mkHasNotBit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "hasNotBit"};
static const lean_object* l_mkHasNotBit___closed__1 = (const lean_object*)&l_mkHasNotBit___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_mkHasNotBit___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkHasNotBit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_mkHasNotBit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_mkHasNotBit___closed__2_value_aux_0),((lean_object*)&l_mkHasNotBit___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 117, 142, 139, 222, 16, 37, 88)}};
static const lean_object* l_mkHasNotBit___closed__2 = (const lean_object*)&l_mkHasNotBit___closed__2_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l_mkHasNotBit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBit___closed__3;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkHasNotBit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkHasNotBit___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00mkHasNotBitProof_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00mkHasNotBitProof_spec__0___closed__0 = (const lean_object*)&l_panic___at___00mkHasNotBitProof_spec__0___closed__0_value;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00mkHasNotBitProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00mkHasNotBitProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_mkHasNotBitProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ne_of_beq_eq_false"};
static const lean_object* l_mkHasNotBitProof___closed__0 = (const lean_object*)&l_mkHasNotBitProof___closed__0_value;
static const lean_ctor_object l_mkHasNotBitProof___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkHasNotBit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_mkHasNotBitProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_mkHasNotBitProof___closed__1_value_aux_0),((lean_object*)&l_mkHasNotBitProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 213, 144, 137, 140, 238, 73, 24)}};
static const lean_object* l_mkHasNotBitProof___closed__1 = (const lean_object*)&l_mkHasNotBitProof___closed__1_value;
static lean_once_cell_t l_mkHasNotBitProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBitProof___closed__2;
static const lean_string_object l_mkHasNotBitProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_mkHasNotBitProof___closed__3 = (const lean_object*)&l_mkHasNotBitProof___closed__3_value;
static const lean_string_object l_mkHasNotBitProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_mkHasNotBitProof___closed__4 = (const lean_object*)&l_mkHasNotBitProof___closed__4_value;
static const lean_ctor_object l_mkHasNotBitProof___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkHasNotBitProof___closed__3_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_mkHasNotBitProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_mkHasNotBitProof___closed__5_value_aux_0),((lean_object*)&l_mkHasNotBitProof___closed__4_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_mkHasNotBitProof___closed__5 = (const lean_object*)&l_mkHasNotBitProof___closed__5_value;
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_once_cell_t l_mkHasNotBitProof___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBitProof___closed__6;
static lean_once_cell_t l_mkHasNotBitProof___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBitProof___closed__7;
static lean_once_cell_t l_mkHasNotBitProof___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBitProof___closed__8;
static const lean_string_object l_mkHasNotBitProof___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_mkHasNotBitProof___closed__9 = (const lean_object*)&l_mkHasNotBitProof___closed__9_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_mkHasNotBitProof___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkHasNotBitProof___closed__9_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_mkHasNotBitProof___closed__10 = (const lean_object*)&l_mkHasNotBitProof___closed__10_value;
static lean_once_cell_t l_mkHasNotBitProof___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBitProof___closed__11;
static const lean_string_object l_mkHasNotBitProof___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_mkHasNotBitProof___closed__12 = (const lean_object*)&l_mkHasNotBitProof___closed__12_value;
static const lean_ctor_object l_mkHasNotBitProof___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkHasNotBitProof___closed__9_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_mkHasNotBitProof___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_mkHasNotBitProof___closed__13_value_aux_0),((lean_object*)&l_mkHasNotBitProof___closed__12_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_mkHasNotBitProof___closed__13 = (const lean_object*)&l_mkHasNotBitProof___closed__13_value;
static lean_once_cell_t l_mkHasNotBitProof___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBitProof___closed__14;
static lean_once_cell_t l_mkHasNotBitProof___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBitProof___closed__15;
static const lean_string_object l_mkHasNotBitProof___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Meta.HasNotBit"};
static const lean_object* l_mkHasNotBitProof___closed__16 = (const lean_object*)&l_mkHasNotBitProof___closed__16_value;
static const lean_string_object l_mkHasNotBitProof___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "mkHasNotBitProof"};
static const lean_object* l_mkHasNotBitProof___closed__17 = (const lean_object*)&l_mkHasNotBitProof___closed__17_value;
static const lean_string_object l_mkHasNotBitProof___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_mkHasNotBitProof___closed__18 = (const lean_object*)&l_mkHasNotBitProof___closed__18_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_mkHasNotBitProof___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBitProof___closed__19;
lean_object* l_Lean_Meta_matchNe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkHasNotBitProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkHasNotBitProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_isHasNotBit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00refutableHasNotBit_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00refutableHasNotBit_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_refutableHasNotBit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "eq_of_beq_eq_true"};
static const lean_object* l_refutableHasNotBit_x3f___closed__0 = (const lean_object*)&l_refutableHasNotBit_x3f___closed__0_value;
static const lean_ctor_object l_refutableHasNotBit_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkHasNotBit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_refutableHasNotBit_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_refutableHasNotBit_x3f___closed__1_value_aux_0),((lean_object*)&l_refutableHasNotBit_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 61, 33, 216, 114, 139, 90, 184)}};
static const lean_object* l_refutableHasNotBit_x3f___closed__1 = (const lean_object*)&l_refutableHasNotBit_x3f___closed__1_value;
static lean_once_cell_t l_refutableHasNotBit_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_refutableHasNotBit_x3f___closed__2;
static const lean_string_object l_refutableHasNotBit_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "refutableHasNotBit\?"};
static const lean_object* l_refutableHasNotBit_x3f___closed__3 = (const lean_object*)&l_refutableHasNotBit_x3f___closed__3_value;
static lean_once_cell_t l_refutableHasNotBit_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_refutableHasNotBit_x3f___closed__4;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_reflBoolTrue;
LEAN_EXPORT lean_object* l_refutableHasNotBit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_refutableHasNotBit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget_borrowed(x_1, x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_shiftl(x_7, x_6);
x_9 = lean_nat_lor(x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_mkHasNotBit___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_mkHasNotBit___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_mkHasNotBit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_size(x_2);
x_5 = 0;
x_6 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0(x_2, x_4, x_5, x_3);
x_7 = lean_obj_once(&l_mkHasNotBit___closed__3, &l_mkHasNotBit___closed__3_once, _init_l_mkHasNotBit___closed__3);
x_8 = l_Lean_mkRawNatLit(x_6);
x_9 = l_Lean_mkAppB(x_7, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_mkHasNotBit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_mkHasNotBit(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00mkHasNotBitProof_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = ((lean_object*)(l_panic___at___00mkHasNotBitProof_spec__0___closed__0));
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___00mkHasNotBitProof_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00mkHasNotBitProof_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_mkHasNotBitProof___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_mkHasNotBitProof___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_mkHasNotBitProof___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_mkHasNotBitProof___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l_mkHasNotBitProof___closed__6, &l_mkHasNotBitProof___closed__6_once, _init_l_mkHasNotBitProof___closed__6);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_mkHasNotBitProof___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_mkHasNotBitProof___closed__7, &l_mkHasNotBitProof___closed__7_once, _init_l_mkHasNotBitProof___closed__7);
x_2 = ((lean_object*)(l_mkHasNotBitProof___closed__5));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_mkHasNotBitProof___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_mkHasNotBitProof___closed__10));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_mkHasNotBitProof___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_mkHasNotBitProof___closed__13));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_mkHasNotBitProof___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_mkHasNotBitProof___closed__14, &l_mkHasNotBitProof___closed__14_once, _init_l_mkHasNotBitProof___closed__14);
x_2 = lean_obj_once(&l_mkHasNotBitProof___closed__11, &l_mkHasNotBitProof___closed__11_once, _init_l_mkHasNotBitProof___closed__11);
x_3 = lean_obj_once(&l_mkHasNotBitProof___closed__8, &l_mkHasNotBitProof___closed__8_once, _init_l_mkHasNotBitProof___closed__8);
x_4 = l_Lean_mkAppB(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_mkHasNotBitProof___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_mkHasNotBitProof___closed__18));
x_2 = lean_unsigned_to_nat(57u);
x_3 = lean_unsigned_to_nat(33u);
x_4 = ((lean_object*)(l_mkHasNotBitProof___closed__17));
x_5 = ((lean_object*)(l_mkHasNotBitProof___closed__16));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_mkHasNotBitProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_mkHasNotBit(x_1, x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_9 = l_Lean_Meta_matchNe_x3f(x_8, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_26; 
x_10 = lean_ctor_get(x_9, 0);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
x_11 = x_9;
x_12 = x_26;
goto block_25;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_26;
goto block_25;
}
block_25:
{
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_obj_once(&l_mkHasNotBitProof___closed__2, &l_mkHasNotBitProof___closed__2_once, _init_l_mkHasNotBitProof___closed__2);
x_18 = lean_obj_once(&l_mkHasNotBitProof___closed__15, &l_mkHasNotBitProof___closed__15_once, _init_l_mkHasNotBitProof___closed__15);
x_19 = l_Lean_mkApp3(x_17, x_15, x_16, x_18);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_19);
x_20 = x_11;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_del_object(x_11);
lean_dec(x_10);
x_23 = lean_obj_once(&l_mkHasNotBitProof___closed__19, &l_mkHasNotBitProof___closed__19_once, _init_l_mkHasNotBitProof___closed__19);
x_24 = l_panic___at___00mkHasNotBitProof_spec__0(x_23, x_3, x_4, x_5, x_6);
return x_24;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_27 = lean_ctor_get(x_9, 0);
x_34 = !lean_is_exclusive(x_9);
if (x_34 == 0)
{
x_28 = x_9;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_9);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_mkHasNotBitProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_mkHasNotBitProof(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_isHasNotBit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_10 = ((lean_object*)(l_mkHasNotBit___closed__2));
x_11 = l_Lean_Expr_isConstOf(x_9, x_10);
lean_dec_ref(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_5);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00refutableHasNotBit_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = ((lean_object*)(l_panic___at___00mkHasNotBitProof_spec__0___closed__0));
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___00refutableHasNotBit_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00refutableHasNotBit_x3f_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_refutableHasNotBit_x3f___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_refutableHasNotBit_x3f___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_refutableHasNotBit_x3f___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_mkHasNotBitProof___closed__18));
x_2 = lean_unsigned_to_nat(84u);
x_3 = lean_unsigned_to_nat(53u);
x_4 = ((lean_object*)(l_refutableHasNotBit_x3f___closed__3));
x_5 = ((lean_object*)(l_mkHasNotBitProof___closed__16));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_refutableHasNotBit_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_95; 
x_8 = lean_ctor_get(x_7, 0);
x_95 = !lean_is_exclusive(x_7);
if (x_95 == 0)
{
x_9 = x_7;
x_10 = x_95;
goto block_94;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Expr_cleanupAnnotations(x_8);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_18);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_23 = ((lean_object*)(l_mkHasNotBit___closed__2));
x_24 = l_Lean_Expr_isConstOf(x_22, x_23);
lean_dec_ref(x_22);
if (x_24 == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_15;
}
else
{
lean_object* x_25; 
lean_del_object(x_9);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_25 = lean_whnf(x_18, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_85; 
x_26 = lean_ctor_get(x_25, 0);
x_85 = !lean_is_exclusive(x_25);
if (x_85 == 0)
{
x_27 = x_25;
x_28 = x_85;
goto block_84;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_85;
goto block_84;
}
block_84:
{
uint8_t x_29; 
x_29 = l_Lean_Expr_hasFVar(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_del_object(x_27);
x_30 = lean_obj_once(&l_mkHasNotBit___closed__3, &l_mkHasNotBit___closed__3_once, _init_l_mkHasNotBit___closed__3);
x_31 = l_Lean_mkAppB(x_30, x_21, x_26);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_32 = l_Lean_Meta_matchNe_x3f(x_31, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_69; 
x_34 = lean_ctor_get(x_33, 0);
x_69 = !lean_is_exclusive(x_33);
if (x_69 == 0)
{
x_35 = x_33;
x_36 = x_69;
goto block_68;
}
else
{
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_39);
lean_inc(x_38);
x_40 = l_Lean_Meta_isExprDefEq(x_38, x_39, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_59; 
x_41 = lean_ctor_get(x_40, 0);
x_59 = !lean_is_exclusive(x_40);
if (x_59 == 0)
{
x_42 = x_40;
x_43 = x_59;
goto block_58;
}
else
{
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = x_59;
goto block_58;
}
block_58:
{
uint8_t x_44; 
x_44 = lean_unbox(x_41);
lean_dec(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_39);
lean_dec(x_38);
lean_del_object(x_35);
x_45 = lean_box(0);
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_45);
x_46 = x_42;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_obj_once(&l_refutableHasNotBit_x3f___closed__2, &l_refutableHasNotBit_x3f___closed__2_once, _init_l_refutableHasNotBit_x3f___closed__2);
x_50 = l_Lean_reflBoolTrue;
x_51 = l_Lean_mkApp3(x_49, x_38, x_39, x_50);
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_51);
x_52 = x_35;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_51);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_52);
x_53 = x_42;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_52);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_67; 
lean_dec(x_39);
lean_dec(x_38);
lean_del_object(x_35);
x_60 = lean_ctor_get(x_40, 0);
x_67 = !lean_is_exclusive(x_40);
if (x_67 == 0)
{
x_61 = x_40;
x_62 = x_67;
goto block_66;
}
else
{
lean_inc(x_60);
lean_dec(x_40);
x_61 = lean_box(0);
x_62 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_63; 
if (x_62 == 0)
{
x_63 = x_61;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_60);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_33);
x_70 = lean_obj_once(&l_refutableHasNotBit_x3f___closed__4, &l_refutableHasNotBit_x3f___closed__4_once, _init_l_refutableHasNotBit_x3f___closed__4);
x_71 = l_panic___at___00refutableHasNotBit_x3f_spec__0(x_70, x_2, x_3, x_4, x_5);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_72 = lean_ctor_get(x_32, 0);
x_79 = !lean_is_exclusive(x_32);
if (x_79 == 0)
{
x_73 = x_32;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_32);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_26);
lean_dec_ref(x_21);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_80 = lean_box(0);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_80);
x_81 = x_27;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_80);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_93; 
lean_dec_ref(x_21);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_86 = lean_ctor_get(x_25, 0);
x_93 = !lean_is_exclusive(x_25);
if (x_93 == 0)
{
x_87 = x_25;
x_88 = x_93;
goto block_92;
}
else
{
lean_inc(x_86);
lean_dec(x_25);
x_87 = lean_box(0);
x_88 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_89; 
if (x_88 == 0)
{
x_89 = x_87;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_86);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
}
}
}
block_15:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_11);
x_12 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_103; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_96 = lean_ctor_get(x_7, 0);
x_103 = !lean_is_exclusive(x_7);
if (x_103 == 0)
{
x_97 = x_7;
x_98 = x_103;
goto block_102;
}
else
{
lean_inc(x_96);
lean_dec(x_7);
x_97 = lean_box(0);
x_98 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_99; 
if (x_98 == 0)
{
x_99 = x_97;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_96);
x_99 = x_101;
goto block_100;
}
block_100:
{
return x_99;
}
}
}
}
}
LEAN_EXPORT lean_object* l_refutableHasNotBit_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_refutableHasNotBit_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_MatchUtil(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_HasNotBit(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_MatchUtil(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_HasNotBit(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_HasNotBit(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_HasNotBit(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_HasNotBit(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_HasNotBit(builtin);
}
#ifdef __cplusplus
}
#endif
