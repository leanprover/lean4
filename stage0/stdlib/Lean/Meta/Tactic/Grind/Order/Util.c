// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.Util
// Imports: public import Lean.Meta.Tactic.Grind.Order.OrderM import Lean.Meta.Tactic.Grind.Arith.Util
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
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
static const lean_string_object l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Order_Cnstr_pp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " + "};
static const lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4;
static const lean_string_object l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≤"};
static const lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Order_Cnstr_pp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__7_value;
lean_object* l_Lean_Meta_Grind_Order_getExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_compare(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_compare___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Order_instOrdWeight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Order_Weight_compare___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Order_instOrdWeight___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_instOrdWeight___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Order_instOrdWeight = (const lean_object*)&l_Lean_Meta_Grind_Order_instOrdWeight___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instLEWeight;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instLTWeight;
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLEWeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLEWeight___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLTWeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLTWeight___boxed(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Order_instAddWeight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Order_Weight_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Order_instAddWeight___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_instAddWeight___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Order_instAddWeight = (const lean_object*)&l_Lean_Meta_Grind_Order_instAddWeight___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isNeg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isNeg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isZero(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isZero___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 2, .m_data = "-ε"};
static const lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0_value;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Order_instToStringWeight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_instToStringWeight___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Order_instToStringWeight = (const lean_object*)&l_Lean_Meta_Grind_Order_instToStringWeight___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "eqTrue: "};
static const lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eqFalse: "};
static const lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5;
static const lean_string_object l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eq: "};
static const lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
x_18 = l_Lean_Meta_Grind_Order_getExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_20 = x_18;
} else {
 lean_dec_ref(x_18);
 x_20 = lean_box(0);
}
x_21 = l_Lean_Meta_Grind_Order_getExpr(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
if (x_14 == 0)
{
lean_object* x_64; 
x_64 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6));
x_31 = x_64;
goto block_63;
}
else
{
lean_object* x_65; 
x_65 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__7));
x_31 = x_65;
goto block_63;
}
block_30:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_MessageData_ofFormat(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
if (lean_is_scalar(x_23)) {
 x_29 = lean_alloc_ctor(0, 1, 0);
} else {
 x_29 = x_23;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
block_63:
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_33 = lean_int_dec_eq(x_17, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_20);
x_34 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_19);
x_35 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_stringToMessageData(x_31);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
x_40 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_22);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_int_dec_lt(x_17, x_32);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_nat_abs(x_17);
x_46 = l_Nat_reprFast(x_45);
x_24 = x_43;
x_25 = x_46;
goto block_30;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_nat_abs(x_17);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_47, x_48);
lean_dec(x_47);
x_50 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_51 = lean_nat_add(x_49, x_48);
lean_dec(x_49);
x_52 = l_Nat_reprFast(x_51);
x_53 = lean_string_append(x_50, x_52);
lean_dec_ref(x_52);
x_24 = x_43;
x_25 = x_53;
goto block_30;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_23);
x_54 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_19);
x_55 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_stringToMessageData(x_31);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
x_60 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_22);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
if (lean_is_scalar(x_20)) {
 x_62 = lean_alloc_ctor(0, 1, 0);
} else {
 x_62 = x_20;
}
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_20);
lean_dec(x_19);
x_66 = !lean_is_exclusive(x_21);
if (x_66 == 0)
{
return x_21;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_21, 0);
lean_inc(x_67);
lean_dec(x_21);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_18);
if (x_69 == 0)
{
return x_18;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_18, 0);
lean_inc(x_70);
lean_dec(x_18);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_Cnstr_pp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_compare(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_11 = lean_int_dec_lt(x_3, x_5);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_int_dec_lt(x_5, x_3);
if (x_12 == 0)
{
if (x_4 == 0)
{
if (x_6 == 0)
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
else
{
goto block_10;
}
}
else
{
if (x_6 == 0)
{
goto block_10;
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
}
else
{
uint8_t x_15; 
x_15 = 2;
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
block_10:
{
if (x_4 == 0)
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
else
{
if (x_6 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 2;
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_compare___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_Order_Weight_compare(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instLEWeight(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instLTWeight(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLEWeight(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_Grind_Order_Weight_compare(x_1, x_2);
x_4 = 2;
x_5 = l_instDecidableEqOrdering(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLEWeight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_Order_instDecidableLEWeight(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLTWeight(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_Grind_Order_Weight_compare(x_1, x_2);
x_4 = 0;
x_5 = l_instDecidableEqOrdering(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLTWeight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_Order_instDecidableLTWeight(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_int_add(x_4, x_6);
lean_dec(x_6);
if (x_5 == 0)
{
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_ctor_set(x_2, 0, x_7);
lean_ctor_set_uint8(x_2, sizeof(void*)*1, x_5);
return x_2;
}
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_inc(x_10);
lean_dec(x_2);
x_12 = lean_int_add(x_8, x_10);
lean_dec(x_10);
if (x_9 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_11);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_9);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Order_Weight_add(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isNeg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_4 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_5 = lean_int_dec_lt(x_2, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_int_dec_eq(x_2, x_4);
if (x_6 == 0)
{
return x_6;
}
else
{
return x_3;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isNeg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Order_Weight_isNeg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isZero(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_4 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_5 = lean_int_dec_eq(x_2, x_4);
if (x_5 == 0)
{
return x_5;
}
else
{
if (x_3 == 0)
{
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isZero___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Order_Weight_isZero(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_9 = lean_int_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_nat_abs(x_7);
x_11 = l_Nat_reprFast(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_nat_abs(x_7);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_15 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_16 = lean_nat_add(x_14, x_13);
lean_dec(x_14);
x_17 = l_Nat_reprFast(x_16);
x_18 = lean_string_append(x_15, x_17);
lean_dec_ref(x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_21 = lean_int_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_nat_abs(x_19);
x_23 = l_Nat_reprFast(x_22);
x_2 = x_23;
goto block_5;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_nat_abs(x_19);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_24, x_25);
lean_dec(x_24);
x_27 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_28 = lean_nat_add(x_26, x_25);
lean_dec(x_26);
x_29 = l_Nat_reprFast(x_28);
x_30 = lean_string_append(x_27, x_29);
lean_dec_ref(x_29);
x_2 = x_30;
goto block_5;
}
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
x_4 = lean_string_append(x_2, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_18);
lean_dec_ref(x_1);
x_19 = l_Lean_Meta_Grind_Order_getExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Meta_Grind_Order_getExpr(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_31; lean_object* x_32; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_79; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_36 = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1);
x_37 = l_Lean_MessageData_ofExpr(x_14);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_ctor_get(x_17, 0);
lean_inc(x_41);
x_42 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_dec_ref(x_17);
x_43 = l_Lean_MessageData_ofExpr(x_20);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
x_46 = l_Lean_MessageData_ofExpr(x_22);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_39);
if (x_42 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_84 = lean_int_dec_lt(x_41, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_nat_abs(x_41);
lean_dec(x_41);
x_86 = l_Nat_reprFast(x_85);
x_49 = x_86;
goto block_78;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_nat_abs(x_41);
lean_dec(x_41);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_sub(x_87, x_88);
lean_dec(x_87);
x_90 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_91 = lean_nat_add(x_89, x_88);
lean_dec(x_89);
x_92 = l_Nat_reprFast(x_91);
x_93 = lean_string_append(x_90, x_92);
lean_dec_ref(x_92);
x_49 = x_93;
goto block_78;
}
}
else
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_95 = lean_int_dec_lt(x_41, x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_nat_abs(x_41);
lean_dec(x_41);
x_97 = l_Nat_reprFast(x_96);
x_79 = x_97;
goto block_82;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_nat_abs(x_41);
lean_dec(x_41);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_sub(x_98, x_99);
lean_dec(x_98);
x_101 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_102 = lean_nat_add(x_100, x_99);
lean_dec(x_100);
x_103 = l_Nat_reprFast(x_102);
x_104 = lean_string_append(x_101, x_103);
lean_dec_ref(x_103);
x_79 = x_104;
goto block_82;
}
}
block_30:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_MessageData_ofFormat(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
if (lean_is_scalar(x_23)) {
 x_29 = lean_alloc_ctor(0, 1, 0);
} else {
 x_29 = x_23;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
x_34 = lean_string_append(x_32, x_33);
x_24 = x_31;
x_25 = x_34;
goto block_30;
}
block_78:
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_18, 0);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
lean_dec_ref(x_18);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_49);
x_53 = l_Lean_MessageData_ofFormat(x_52);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_39);
if (x_51 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_57 = lean_int_dec_lt(x_50, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_nat_abs(x_50);
lean_dec(x_50);
x_59 = l_Nat_reprFast(x_58);
x_24 = x_55;
x_25 = x_59;
goto block_30;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_nat_abs(x_50);
lean_dec(x_50);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_sub(x_60, x_61);
lean_dec(x_60);
x_63 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_64 = lean_nat_add(x_62, x_61);
lean_dec(x_62);
x_65 = l_Nat_reprFast(x_64);
x_66 = lean_string_append(x_63, x_65);
lean_dec_ref(x_65);
x_24 = x_55;
x_25 = x_66;
goto block_30;
}
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_68 = lean_int_dec_lt(x_50, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_nat_abs(x_50);
lean_dec(x_50);
x_70 = l_Nat_reprFast(x_69);
x_31 = x_55;
x_32 = x_70;
goto block_35;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_nat_abs(x_50);
lean_dec(x_50);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_sub(x_71, x_72);
lean_dec(x_71);
x_74 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_75 = lean_nat_add(x_73, x_72);
lean_dec(x_73);
x_76 = l_Nat_reprFast(x_75);
x_77 = lean_string_append(x_74, x_76);
lean_dec_ref(x_76);
x_31 = x_55;
x_32 = x_77;
goto block_35;
}
}
}
block_82:
{
lean_object* x_80; lean_object* x_81; 
x_80 = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
x_81 = lean_string_append(x_79, x_80);
x_49 = x_81;
goto block_78;
}
}
else
{
uint8_t x_105; 
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_14);
x_105 = !lean_is_exclusive(x_21);
if (x_105 == 0)
{
return x_21;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_21, 0);
lean_inc(x_106);
lean_dec(x_21);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_14);
x_108 = !lean_is_exclusive(x_19);
if (x_108 == 0)
{
return x_19;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_19, 0);
lean_inc(x_109);
lean_dec(x_19);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
}
case 1:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_1, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_1, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_115);
lean_dec_ref(x_1);
x_116 = l_Lean_Meta_Grind_Order_getExpr(x_112, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_112);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
x_118 = l_Lean_Meta_Grind_Order_getExpr(x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_113);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_128; lean_object* x_129; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_176; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
x_133 = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5);
x_134 = l_Lean_MessageData_ofExpr(x_111);
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_ctor_get(x_114, 0);
lean_inc(x_138);
x_139 = lean_ctor_get_uint8(x_114, sizeof(void*)*1);
lean_dec_ref(x_114);
x_140 = l_Lean_MessageData_ofExpr(x_117);
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_137);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_136);
x_143 = l_Lean_MessageData_ofExpr(x_119);
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_136);
if (x_139 == 0)
{
lean_object* x_180; uint8_t x_181; 
x_180 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_181 = lean_int_dec_lt(x_138, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_nat_abs(x_138);
lean_dec(x_138);
x_183 = l_Nat_reprFast(x_182);
x_146 = x_183;
goto block_175;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_nat_abs(x_138);
lean_dec(x_138);
x_185 = lean_unsigned_to_nat(1u);
x_186 = lean_nat_sub(x_184, x_185);
lean_dec(x_184);
x_187 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_188 = lean_nat_add(x_186, x_185);
lean_dec(x_186);
x_189 = l_Nat_reprFast(x_188);
x_190 = lean_string_append(x_187, x_189);
lean_dec_ref(x_189);
x_146 = x_190;
goto block_175;
}
}
else
{
lean_object* x_191; uint8_t x_192; 
x_191 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_192 = lean_int_dec_lt(x_138, x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_nat_abs(x_138);
lean_dec(x_138);
x_194 = l_Nat_reprFast(x_193);
x_176 = x_194;
goto block_179;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_195 = lean_nat_abs(x_138);
lean_dec(x_138);
x_196 = lean_unsigned_to_nat(1u);
x_197 = lean_nat_sub(x_195, x_196);
lean_dec(x_195);
x_198 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_199 = lean_nat_add(x_197, x_196);
lean_dec(x_197);
x_200 = l_Nat_reprFast(x_199);
x_201 = lean_string_append(x_198, x_200);
lean_dec_ref(x_200);
x_176 = x_201;
goto block_179;
}
}
block_127:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = l_Lean_MessageData_ofFormat(x_123);
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
if (lean_is_scalar(x_120)) {
 x_126 = lean_alloc_ctor(0, 1, 0);
} else {
 x_126 = x_120;
}
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
block_132:
{
lean_object* x_130; lean_object* x_131; 
x_130 = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
x_131 = lean_string_append(x_129, x_130);
x_121 = x_128;
x_122 = x_131;
goto block_127;
}
block_175:
{
lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_115, 0);
lean_inc(x_147);
x_148 = lean_ctor_get_uint8(x_115, sizeof(void*)*1);
lean_dec_ref(x_115);
x_149 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_149, 0, x_146);
x_150 = l_Lean_MessageData_ofFormat(x_149);
x_151 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_136);
if (x_148 == 0)
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_154 = lean_int_dec_lt(x_147, x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_nat_abs(x_147);
lean_dec(x_147);
x_156 = l_Nat_reprFast(x_155);
x_121 = x_152;
x_122 = x_156;
goto block_127;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_157 = lean_nat_abs(x_147);
lean_dec(x_147);
x_158 = lean_unsigned_to_nat(1u);
x_159 = lean_nat_sub(x_157, x_158);
lean_dec(x_157);
x_160 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_161 = lean_nat_add(x_159, x_158);
lean_dec(x_159);
x_162 = l_Nat_reprFast(x_161);
x_163 = lean_string_append(x_160, x_162);
lean_dec_ref(x_162);
x_121 = x_152;
x_122 = x_163;
goto block_127;
}
}
else
{
lean_object* x_164; uint8_t x_165; 
x_164 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_165 = lean_int_dec_lt(x_147, x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_nat_abs(x_147);
lean_dec(x_147);
x_167 = l_Nat_reprFast(x_166);
x_128 = x_152;
x_129 = x_167;
goto block_132;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_168 = lean_nat_abs(x_147);
lean_dec(x_147);
x_169 = lean_unsigned_to_nat(1u);
x_170 = lean_nat_sub(x_168, x_169);
lean_dec(x_168);
x_171 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_172 = lean_nat_add(x_170, x_169);
lean_dec(x_170);
x_173 = l_Nat_reprFast(x_172);
x_174 = lean_string_append(x_171, x_173);
lean_dec_ref(x_173);
x_128 = x_152;
x_129 = x_174;
goto block_132;
}
}
}
block_179:
{
lean_object* x_177; lean_object* x_178; 
x_177 = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
x_178 = lean_string_append(x_176, x_177);
x_146 = x_178;
goto block_175;
}
}
else
{
uint8_t x_202; 
lean_dec(x_117);
lean_dec_ref(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_111);
x_202 = !lean_is_exclusive(x_118);
if (x_202 == 0)
{
return x_118;
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_118, 0);
lean_inc(x_203);
lean_dec(x_118);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec_ref(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec_ref(x_111);
x_205 = !lean_is_exclusive(x_116);
if (x_205 == 0)
{
return x_116;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_116, 0);
lean_inc(x_206);
lean_dec(x_116);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
return x_207;
}
}
}
default: 
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_1);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_1, 0);
x_210 = lean_ctor_get(x_1, 1);
x_211 = l_Lean_Meta_Grind_Order_getExpr(x_209, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_209);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
lean_dec_ref(x_211);
x_213 = l_Lean_Meta_Grind_Order_getExpr(x_210, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_210);
if (lean_obj_tag(x_213) == 0)
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_215 = lean_ctor_get(x_213, 0);
x_216 = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7);
x_217 = l_Lean_MessageData_ofExpr(x_212);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_217);
lean_ctor_set(x_1, 0, x_216);
x_218 = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
x_219 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_219, 0, x_1);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Lean_MessageData_ofExpr(x_215);
x_221 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
lean_ctor_set(x_213, 0, x_221);
return x_213;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_222 = lean_ctor_get(x_213, 0);
lean_inc(x_222);
lean_dec(x_213);
x_223 = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7);
x_224 = l_Lean_MessageData_ofExpr(x_212);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_224);
lean_ctor_set(x_1, 0, x_223);
x_225 = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
x_226 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_226, 0, x_1);
lean_ctor_set(x_226, 1, x_225);
x_227 = l_Lean_MessageData_ofExpr(x_222);
x_228 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_229, 0, x_228);
return x_229;
}
}
else
{
uint8_t x_230; 
lean_dec(x_212);
lean_free_object(x_1);
x_230 = !lean_is_exclusive(x_213);
if (x_230 == 0)
{
return x_213;
}
else
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_213, 0);
lean_inc(x_231);
lean_dec(x_213);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_231);
return x_232;
}
}
}
else
{
uint8_t x_233; 
lean_free_object(x_1);
lean_dec(x_210);
x_233 = !lean_is_exclusive(x_211);
if (x_233 == 0)
{
return x_211;
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_211, 0);
lean_inc(x_234);
lean_dec(x_211);
x_235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_235, 0, x_234);
return x_235;
}
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_1, 0);
x_237 = lean_ctor_get(x_1, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_1);
x_238 = l_Lean_Meta_Grind_Order_getExpr(x_236, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_236);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec_ref(x_238);
x_240 = l_Lean_Meta_Grind_Order_getExpr(x_237, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_237);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 x_242 = x_240;
} else {
 lean_dec_ref(x_240);
 x_242 = lean_box(0);
}
x_243 = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7);
x_244 = l_Lean_MessageData_ofExpr(x_239);
x_245 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
x_247 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = l_Lean_MessageData_ofExpr(x_241);
x_249 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
if (lean_is_scalar(x_242)) {
 x_250 = lean_alloc_ctor(0, 1, 0);
} else {
 x_250 = x_242;
}
lean_ctor_set(x_250, 0, x_249);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_239);
x_251 = lean_ctor_get(x_240, 0);
lean_inc(x_251);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 x_252 = x_240;
} else {
 lean_dec_ref(x_240);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 1, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_251);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_237);
x_254 = lean_ctor_get(x_238, 0);
lean_inc(x_254);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 x_255 = x_238;
} else {
 lean_dec_ref(x_238);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 1, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_254);
return x_256;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_ToPropagate_pp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = 0;
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = 1;
lean_inc(x_6);
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Order_Cnstr_getWeight(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Order_instLEWeight = _init_l_Lean_Meta_Grind_Order_instLEWeight();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instLEWeight);
l_Lean_Meta_Grind_Order_instLTWeight = _init_l_Lean_Meta_Grind_Order_instLTWeight();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instLTWeight);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
