// Lean compiler output
// Module: Init.Grind.Ring.Envelope
// Imports: public import Init.Grind.Ordered.Ring import all Init.Data.AC import Init.Omega import Init.RCases
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Envelope_0__Lean_Grind_Ring_OfSemiring_r_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Envelope_0__Lean_Grind_Ring_OfSemiring_r_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_natCast___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_natCast(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_sub___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_sub(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_add___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_add(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_mul___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_mul(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_nsmul___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_nsmul(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_toQ___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_toQ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring(lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__0_value;
static const lean_string_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__1 = (const lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__1_value;
static const lean_string_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__2 = (const lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__2_value;
static const lean_string_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__3 = (const lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_0),((lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_1),((lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_2),((lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4 = (const lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value;
static const lean_string_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "coeNotation"};
static const lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__5 = (const lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__5_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 100, 71, 170, 251, 12, 50, 58)}};
static const lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6 = (const lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6_value;
static const lean_string_object l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "↑"};
static const lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7 = (const lean_object*)&l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Envelope_0__Lean_Grind_Ring_OfSemiring_r_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_apply_4(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_Envelope_0__Lean_Grind_Ring_OfSemiring_r_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Grind_Ring_Envelope_0__Lean_Grind_Ring_OfSemiring_r_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_mk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_Ring_OfSemiring_Q_mk(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_2(x_6, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_natCast___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_apply_1(x_4, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_natCast(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_obj_once(&l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0, &l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0_once, _init_l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0);
x_5 = lean_int_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_nat_abs(x_2);
x_9 = lean_apply_1(x_6, x_8);
x_10 = lean_apply_1(x_7, x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = lean_apply_1(x_13, x_3);
x_15 = lean_nat_abs(x_2);
x_16 = lean_apply_1(x_12, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_intCast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_Ring_OfSemiring_intCast(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_sub___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_10 = lean_apply_2(x_4, x_5, x_9);
x_11 = lean_apply_2(x_4, x_8, x_6);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_4);
x_14 = lean_apply_2(x_4, x_5, x_13);
x_15 = lean_apply_2(x_4, x_12, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_sub(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_Ring_OfSemiring_sub___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_add___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_10 = lean_apply_2(x_4, x_5, x_8);
x_11 = lean_apply_2(x_4, x_6, x_9);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_4);
x_14 = lean_apply_2(x_4, x_5, x_12);
x_15 = lean_apply_2(x_4, x_6, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_add(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_Ring_OfSemiring_add___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_mul___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_inc(x_9);
lean_inc(x_6);
x_11 = lean_apply_2(x_5, x_6, x_9);
lean_inc(x_5);
lean_inc(x_10);
lean_inc(x_7);
x_12 = lean_apply_2(x_5, x_7, x_10);
lean_inc(x_4);
x_13 = lean_apply_2(x_4, x_11, x_12);
lean_inc(x_5);
x_14 = lean_apply_2(x_5, x_6, x_10);
x_15 = lean_apply_2(x_5, x_7, x_9);
x_16 = lean_apply_2(x_4, x_14, x_15);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
lean_inc(x_5);
lean_inc(x_17);
lean_inc(x_6);
x_19 = lean_apply_2(x_5, x_6, x_17);
lean_inc(x_5);
lean_inc(x_18);
lean_inc(x_7);
x_20 = lean_apply_2(x_5, x_7, x_18);
lean_inc(x_4);
x_21 = lean_apply_2(x_4, x_19, x_20);
lean_inc(x_5);
x_22 = lean_apply_2(x_5, x_6, x_18);
x_23 = lean_apply_2(x_5, x_7, x_17);
x_24 = lean_apply_2(x_4, x_22, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_mul(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_Ring_OfSemiring_mul___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_3);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_Ring_OfSemiring_neg___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_neg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_Ring_OfSemiring_neg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(x_1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_inc(x_2);
lean_inc_ref(x_1);
x_10 = l_Lean_Grind_Ring_OfSemiring_npow___redArg(x_1, x_2, x_9);
lean_dec(x_9);
x_11 = l_Lean_Grind_Ring_OfSemiring_mul___redArg(x_1, x_10, x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_Ring_OfSemiring_npow___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_Ring_OfSemiring_npow___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_npow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_Ring_OfSemiring_npow(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_nsmul___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc_ref(x_1);
x_4 = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(x_1, x_2);
x_5 = l_Lean_Grind_Ring_OfSemiring_mul___redArg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_nsmul(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_Ring_OfSemiring_nsmul___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc_ref(x_1);
x_4 = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(x_1, x_2);
x_5 = l_Lean_Grind_Ring_OfSemiring_mul___redArg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_zsmul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Grind_Ring_OfSemiring_zsmul(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_add), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_1);
lean_inc_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_mul), 4, 2);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_1);
lean_inc_ref(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_natCast), 3, 2);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_1);
lean_inc_ref(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_nsmul), 4, 2);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, x_1);
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_npow___boxed), 4, 2);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, x_1);
x_8 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_2);
lean_ctor_set(x_8, 4, x_6);
lean_ctor_set(x_8, 5, x_7);
lean_inc_ref(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_neg___boxed), 3, 2);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, x_1);
lean_inc_ref(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_sub), 4, 2);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, x_1);
lean_inc_ref(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_intCast___boxed), 3, 2);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Grind_Ring_OfSemiring_zsmul___boxed), 4, 2);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, x_1);
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_11);
lean_ctor_set(x_13, 4, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_ofSemiring(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_toQ___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_apply_1(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_toQ(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_Ring_OfSemiring_toQ___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4));
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
lean_inc(x_9);
x_10 = l_Lean_Syntax_matchesNull(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_9, x_13);
lean_dec(x_9);
x_15 = 0;
x_16 = l_Lean_SourceInfo_fromRef(x_2, x_15);
x_17 = ((lean_object*)(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6));
x_18 = ((lean_object*)(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7));
lean_inc(x_16);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Syntax_node2(x_16, x_17, x_19, x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Grind_Ordered_Ring(uint8_t builtin);
lean_object* initialize_Init_Data_AC(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Ring_Envelope(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ordered_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
