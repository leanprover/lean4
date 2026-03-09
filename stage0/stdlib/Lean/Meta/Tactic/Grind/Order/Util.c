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
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_83; 
x_19 = lean_ctor_get(x_18, 0);
x_83 = !lean_is_exclusive(x_18);
if (x_83 == 0)
{
x_20 = x_18;
x_21 = x_83;
goto block_82;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_22; 
x_22 = l_Lean_Meta_Grind_Order_getExpr(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_73; 
x_23 = lean_ctor_get(x_22, 0);
x_73 = !lean_is_exclusive(x_22);
if (x_73 == 0)
{
x_24 = x_22;
x_25 = x_73;
goto block_72;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_26; lean_object* x_27; lean_object* x_35; 
if (x_14 == 0)
{
lean_object* x_70; 
x_70 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6));
x_35 = x_70;
goto block_69;
}
else
{
lean_object* x_71; 
x_71 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__7));
x_35 = x_71;
goto block_69;
}
block_34:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_MessageData_ofFormat(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_30);
x_31 = x_24;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
block_69:
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_37 = lean_int_dec_eq(x_17, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_del_object(x_20);
x_38 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_19);
x_39 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_stringToMessageData(x_35);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
x_44 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_23);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_int_dec_lt(x_17, x_36);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_nat_abs(x_17);
x_50 = l_Nat_reprFast(x_49);
x_26 = x_47;
x_27 = x_50;
goto block_34;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_nat_abs(x_17);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_51, x_52);
lean_dec(x_51);
x_54 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_55 = lean_nat_add(x_53, x_52);
lean_dec(x_53);
x_56 = l_Nat_reprFast(x_55);
x_57 = lean_string_append(x_54, x_56);
lean_dec_ref(x_56);
x_26 = x_47;
x_27 = x_57;
goto block_34;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_del_object(x_24);
x_58 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_19);
x_59 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_stringToMessageData(x_35);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
x_64 = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(x_23);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_65);
x_66 = x_20;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_65);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_del_object(x_20);
lean_dec(x_19);
x_74 = lean_ctor_get(x_22, 0);
x_81 = !lean_is_exclusive(x_22);
if (x_81 == 0)
{
x_75 = x_22;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_22);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_91; 
x_84 = lean_ctor_get(x_18, 0);
x_91 = !lean_is_exclusive(x_18);
if (x_91 == 0)
{
x_85 = x_18;
x_86 = x_91;
goto block_90;
}
else
{
lean_inc(x_84);
lean_dec(x_18);
x_85 = lean_box(0);
x_86 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_87; 
if (x_86 == 0)
{
x_87 = x_85;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_84);
x_87 = x_89;
goto block_88;
}
block_88:
{
return x_87;
}
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
lean_object* x_3; uint8_t x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; uint8_t x_17; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
x_7 = x_2;
x_8 = x_17;
goto block_16;
}
else
{
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_9; 
x_9 = lean_int_add(x_3, x_5);
lean_dec(x_5);
if (x_4 == 0)
{
lean_object* x_10; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_9);
x_10 = x_7;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_6);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
else
{
lean_object* x_13; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 0, x_9);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_9);
x_13 = x_15;
goto block_14;
}
block_14:
{
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_4);
return x_13;
}
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
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_109; 
x_22 = lean_ctor_get(x_21, 0);
x_109 = !lean_is_exclusive(x_21);
if (x_109 == 0)
{
x_23 = x_21;
x_24 = x_109;
goto block_108;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_25; lean_object* x_26; lean_object* x_34; lean_object* x_35; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_82; 
x_39 = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1);
x_40 = l_Lean_MessageData_ofExpr(x_14);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_ctor_get(x_17, 0);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_dec_ref(x_17);
x_46 = l_Lean_MessageData_ofExpr(x_20);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
x_49 = l_Lean_MessageData_ofExpr(x_22);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
if (x_45 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_87 = lean_int_dec_lt(x_44, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_nat_abs(x_44);
lean_dec(x_44);
x_89 = l_Nat_reprFast(x_88);
x_52 = x_89;
goto block_81;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_nat_abs(x_44);
lean_dec(x_44);
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_sub(x_90, x_91);
lean_dec(x_90);
x_93 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_94 = lean_nat_add(x_92, x_91);
lean_dec(x_92);
x_95 = l_Nat_reprFast(x_94);
x_96 = lean_string_append(x_93, x_95);
lean_dec_ref(x_95);
x_52 = x_96;
goto block_81;
}
}
else
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_98 = lean_int_dec_lt(x_44, x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_nat_abs(x_44);
lean_dec(x_44);
x_100 = l_Nat_reprFast(x_99);
x_82 = x_100;
goto block_85;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_101 = lean_nat_abs(x_44);
lean_dec(x_44);
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_nat_sub(x_101, x_102);
lean_dec(x_101);
x_104 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_105 = lean_nat_add(x_103, x_102);
lean_dec(x_103);
x_106 = l_Nat_reprFast(x_105);
x_107 = lean_string_append(x_104, x_106);
lean_dec_ref(x_106);
x_82 = x_107;
goto block_85;
}
}
block_33:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_MessageData_ofFormat(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_29);
x_30 = x_23;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
block_38:
{
lean_object* x_36; lean_object* x_37; 
x_36 = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
x_37 = lean_string_append(x_35, x_36);
x_25 = x_34;
x_26 = x_37;
goto block_33;
}
block_81:
{
lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_18, 0);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
lean_dec_ref(x_18);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_52);
x_56 = l_Lean_MessageData_ofFormat(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_42);
if (x_54 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_60 = lean_int_dec_lt(x_53, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_nat_abs(x_53);
lean_dec(x_53);
x_62 = l_Nat_reprFast(x_61);
x_25 = x_58;
x_26 = x_62;
goto block_33;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_nat_abs(x_53);
lean_dec(x_53);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_sub(x_63, x_64);
lean_dec(x_63);
x_66 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_67 = lean_nat_add(x_65, x_64);
lean_dec(x_65);
x_68 = l_Nat_reprFast(x_67);
x_69 = lean_string_append(x_66, x_68);
lean_dec_ref(x_68);
x_25 = x_58;
x_26 = x_69;
goto block_33;
}
}
else
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_71 = lean_int_dec_lt(x_53, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_nat_abs(x_53);
lean_dec(x_53);
x_73 = l_Nat_reprFast(x_72);
x_34 = x_58;
x_35 = x_73;
goto block_38;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_nat_abs(x_53);
lean_dec(x_53);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_sub(x_74, x_75);
lean_dec(x_74);
x_77 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_78 = lean_nat_add(x_76, x_75);
lean_dec(x_76);
x_79 = l_Nat_reprFast(x_78);
x_80 = lean_string_append(x_77, x_79);
lean_dec_ref(x_79);
x_34 = x_58;
x_35 = x_80;
goto block_38;
}
}
}
block_85:
{
lean_object* x_83; lean_object* x_84; 
x_83 = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
x_84 = lean_string_append(x_82, x_83);
x_52 = x_84;
goto block_81;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_117; 
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_14);
x_110 = lean_ctor_get(x_21, 0);
x_117 = !lean_is_exclusive(x_21);
if (x_117 == 0)
{
x_111 = x_21;
x_112 = x_117;
goto block_116;
}
else
{
lean_inc(x_110);
lean_dec(x_21);
x_111 = lean_box(0);
x_112 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_113; 
if (x_112 == 0)
{
x_113 = x_111;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_110);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_125; 
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_14);
x_118 = lean_ctor_get(x_19, 0);
x_125 = !lean_is_exclusive(x_19);
if (x_125 == 0)
{
x_119 = x_19;
x_120 = x_125;
goto block_124;
}
else
{
lean_inc(x_118);
lean_dec(x_19);
x_119 = lean_box(0);
x_120 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_121; 
if (x_120 == 0)
{
x_121 = x_119;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_118);
x_121 = x_123;
goto block_122;
}
block_122:
{
return x_121;
}
}
}
}
case 1:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_1, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_1, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_130);
lean_dec_ref(x_1);
x_131 = l_Lean_Meta_Grind_Order_getExpr(x_127, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_127);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = l_Lean_Meta_Grind_Order_getExpr(x_128, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_128);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; uint8_t x_221; 
x_134 = lean_ctor_get(x_133, 0);
x_221 = !lean_is_exclusive(x_133);
if (x_221 == 0)
{
x_135 = x_133;
x_136 = x_221;
goto block_220;
}
else
{
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_box(0);
x_136 = x_221;
goto block_220;
}
block_220:
{
lean_object* x_137; lean_object* x_138; lean_object* x_146; lean_object* x_147; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_194; 
x_151 = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5);
x_152 = l_Lean_MessageData_ofExpr(x_126);
x_153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_ctor_get(x_129, 0);
lean_inc(x_156);
x_157 = lean_ctor_get_uint8(x_129, sizeof(void*)*1);
lean_dec_ref(x_129);
x_158 = l_Lean_MessageData_ofExpr(x_132);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_154);
x_161 = l_Lean_MessageData_ofExpr(x_134);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_154);
if (x_157 == 0)
{
lean_object* x_198; uint8_t x_199; 
x_198 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_199 = lean_int_dec_lt(x_156, x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_nat_abs(x_156);
lean_dec(x_156);
x_201 = l_Nat_reprFast(x_200);
x_164 = x_201;
goto block_193;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_202 = lean_nat_abs(x_156);
lean_dec(x_156);
x_203 = lean_unsigned_to_nat(1u);
x_204 = lean_nat_sub(x_202, x_203);
lean_dec(x_202);
x_205 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_206 = lean_nat_add(x_204, x_203);
lean_dec(x_204);
x_207 = l_Nat_reprFast(x_206);
x_208 = lean_string_append(x_205, x_207);
lean_dec_ref(x_207);
x_164 = x_208;
goto block_193;
}
}
else
{
lean_object* x_209; uint8_t x_210; 
x_209 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_210 = lean_int_dec_lt(x_156, x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_nat_abs(x_156);
lean_dec(x_156);
x_212 = l_Nat_reprFast(x_211);
x_194 = x_212;
goto block_197;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_213 = lean_nat_abs(x_156);
lean_dec(x_156);
x_214 = lean_unsigned_to_nat(1u);
x_215 = lean_nat_sub(x_213, x_214);
lean_dec(x_213);
x_216 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_217 = lean_nat_add(x_215, x_214);
lean_dec(x_215);
x_218 = l_Nat_reprFast(x_217);
x_219 = lean_string_append(x_216, x_218);
lean_dec_ref(x_218);
x_194 = x_219;
goto block_197;
}
}
block_145:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = l_Lean_MessageData_ofFormat(x_139);
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_137);
lean_ctor_set(x_141, 1, x_140);
if (x_136 == 0)
{
lean_ctor_set(x_135, 0, x_141);
x_142 = x_135;
goto block_143;
}
else
{
lean_object* x_144; 
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_141);
x_142 = x_144;
goto block_143;
}
block_143:
{
return x_142;
}
}
block_150:
{
lean_object* x_148; lean_object* x_149; 
x_148 = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
x_149 = lean_string_append(x_147, x_148);
x_137 = x_146;
x_138 = x_149;
goto block_145;
}
block_193:
{
lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_165 = lean_ctor_get(x_130, 0);
lean_inc(x_165);
x_166 = lean_ctor_get_uint8(x_130, sizeof(void*)*1);
lean_dec_ref(x_130);
x_167 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_167, 0, x_164);
x_168 = l_Lean_MessageData_ofFormat(x_167);
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_163);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_154);
if (x_166 == 0)
{
lean_object* x_171; uint8_t x_172; 
x_171 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_172 = lean_int_dec_lt(x_165, x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_nat_abs(x_165);
lean_dec(x_165);
x_174 = l_Nat_reprFast(x_173);
x_137 = x_170;
x_138 = x_174;
goto block_145;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_175 = lean_nat_abs(x_165);
lean_dec(x_165);
x_176 = lean_unsigned_to_nat(1u);
x_177 = lean_nat_sub(x_175, x_176);
lean_dec(x_175);
x_178 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_179 = lean_nat_add(x_177, x_176);
lean_dec(x_177);
x_180 = l_Nat_reprFast(x_179);
x_181 = lean_string_append(x_178, x_180);
lean_dec_ref(x_180);
x_137 = x_170;
x_138 = x_181;
goto block_145;
}
}
else
{
lean_object* x_182; uint8_t x_183; 
x_182 = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
x_183 = lean_int_dec_lt(x_165, x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_nat_abs(x_165);
lean_dec(x_165);
x_185 = l_Nat_reprFast(x_184);
x_146 = x_170;
x_147 = x_185;
goto block_150;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_186 = lean_nat_abs(x_165);
lean_dec(x_165);
x_187 = lean_unsigned_to_nat(1u);
x_188 = lean_nat_sub(x_186, x_187);
lean_dec(x_186);
x_189 = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
x_190 = lean_nat_add(x_188, x_187);
lean_dec(x_188);
x_191 = l_Nat_reprFast(x_190);
x_192 = lean_string_append(x_189, x_191);
lean_dec_ref(x_191);
x_146 = x_170;
x_147 = x_192;
goto block_150;
}
}
}
block_197:
{
lean_object* x_195; lean_object* x_196; 
x_195 = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
x_196 = lean_string_append(x_194, x_195);
x_164 = x_196;
goto block_193;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; uint8_t x_229; 
lean_dec(x_132);
lean_dec_ref(x_130);
lean_dec_ref(x_129);
lean_dec_ref(x_126);
x_222 = lean_ctor_get(x_133, 0);
x_229 = !lean_is_exclusive(x_133);
if (x_229 == 0)
{
x_223 = x_133;
x_224 = x_229;
goto block_228;
}
else
{
lean_inc(x_222);
lean_dec(x_133);
x_223 = lean_box(0);
x_224 = x_229;
goto block_228;
}
block_228:
{
lean_object* x_225; 
if (x_224 == 0)
{
x_225 = x_223;
goto block_226;
}
else
{
lean_object* x_227; 
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_222);
x_225 = x_227;
goto block_226;
}
block_226:
{
return x_225;
}
}
}
}
else
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; uint8_t x_237; 
lean_dec_ref(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec_ref(x_126);
x_230 = lean_ctor_get(x_131, 0);
x_237 = !lean_is_exclusive(x_131);
if (x_237 == 0)
{
x_231 = x_131;
x_232 = x_237;
goto block_236;
}
else
{
lean_inc(x_230);
lean_dec(x_131);
x_231 = lean_box(0);
x_232 = x_237;
goto block_236;
}
block_236:
{
lean_object* x_233; 
if (x_232 == 0)
{
x_233 = x_231;
goto block_234;
}
else
{
lean_object* x_235; 
x_235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_235, 0, x_230);
x_233 = x_235;
goto block_234;
}
block_234:
{
return x_233;
}
}
}
}
default: 
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; uint8_t x_279; 
x_238 = lean_ctor_get(x_1, 0);
x_239 = lean_ctor_get(x_1, 1);
x_279 = !lean_is_exclusive(x_1);
if (x_279 == 0)
{
x_240 = x_1;
x_241 = x_279;
goto block_278;
}
else
{
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_1);
x_240 = lean_box(0);
x_241 = x_279;
goto block_278;
}
block_278:
{
lean_object* x_242; 
x_242 = l_Lean_Meta_Grind_Order_getExpr(x_238, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_238);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
lean_dec_ref(x_242);
x_244 = l_Lean_Meta_Grind_Order_getExpr(x_239, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_239);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; uint8_t x_247; uint8_t x_261; 
x_245 = lean_ctor_get(x_244, 0);
x_261 = !lean_is_exclusive(x_244);
if (x_261 == 0)
{
x_246 = x_244;
x_247 = x_261;
goto block_260;
}
else
{
lean_inc(x_245);
lean_dec(x_244);
x_246 = lean_box(0);
x_247 = x_261;
goto block_260;
}
block_260:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7);
x_249 = l_Lean_MessageData_ofExpr(x_243);
if (x_241 == 0)
{
lean_ctor_set_tag(x_240, 7);
lean_ctor_set(x_240, 1, x_249);
lean_ctor_set(x_240, 0, x_248);
x_250 = x_240;
goto block_258;
}
else
{
lean_object* x_259; 
x_259 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_259, 0, x_248);
lean_ctor_set(x_259, 1, x_249);
x_250 = x_259;
goto block_258;
}
block_258:
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_251 = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
x_252 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_MessageData_ofExpr(x_245);
x_254 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
if (x_247 == 0)
{
lean_ctor_set(x_246, 0, x_254);
x_255 = x_246;
goto block_256;
}
else
{
lean_object* x_257; 
x_257 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_257, 0, x_254);
x_255 = x_257;
goto block_256;
}
block_256:
{
return x_255;
}
}
}
}
else
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; uint8_t x_269; 
lean_dec(x_243);
lean_del_object(x_240);
x_262 = lean_ctor_get(x_244, 0);
x_269 = !lean_is_exclusive(x_244);
if (x_269 == 0)
{
x_263 = x_244;
x_264 = x_269;
goto block_268;
}
else
{
lean_inc(x_262);
lean_dec(x_244);
x_263 = lean_box(0);
x_264 = x_269;
goto block_268;
}
block_268:
{
lean_object* x_265; 
if (x_264 == 0)
{
x_265 = x_263;
goto block_266;
}
else
{
lean_object* x_267; 
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_262);
x_265 = x_267;
goto block_266;
}
block_266:
{
return x_265;
}
}
}
}
else
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; uint8_t x_277; 
lean_del_object(x_240);
lean_dec(x_239);
x_270 = lean_ctor_get(x_242, 0);
x_277 = !lean_is_exclusive(x_242);
if (x_277 == 0)
{
x_271 = x_242;
x_272 = x_277;
goto block_276;
}
else
{
lean_inc(x_270);
lean_dec(x_242);
x_271 = lean_box(0);
x_272 = x_277;
goto block_276;
}
block_276:
{
lean_object* x_273; 
if (x_272 == 0)
{
x_273 = x_271;
goto block_274;
}
else
{
lean_object* x_275; 
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_270);
x_273 = x_275;
goto block_274;
}
block_274:
{
return x_273;
}
}
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
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Order_instLEWeight = _init_l_Lean_Meta_Grind_Order_instLEWeight();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instLEWeight);
l_Lean_Meta_Grind_Order_instLTWeight = _init_l_Lean_Meta_Grind_Order_instLTWeight();
lean_mark_persistent(l_Lean_Meta_Grind_Order_instLTWeight);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Order_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Order_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Order_Util(builtin);
}
#ifdef __cplusplus
}
#endif
