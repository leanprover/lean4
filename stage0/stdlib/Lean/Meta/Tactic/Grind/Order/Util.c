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
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
static lean_once_cell_t l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0;
static const lean_string_object l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " + "};
static const lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__4;
static const lean_string_object l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≤"};
static const lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_compare(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_compare___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Order_instOrdWeight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Order_Weight_compare___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Order_instOrdWeight___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_instOrdWeight___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Order_instOrdWeight = (const lean_object*)&l_Lean_Meta_Grind_Order_instOrdWeight___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instLEWeight;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instLTWeight;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLEWeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLEWeight___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLTWeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLTWeight___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Order_instToStringWeight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_instToStringWeight___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Order_instToStringWeight = (const lean_object*)&l_Lean_Meta_Grind_Order_instToStringWeight___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "eqTrue: "};
static const lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eqFalse: "};
static const lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__5;
static const lean_string_object l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eq: "};
static const lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__1));
v___x_5_ = l_Lean_stringToMessageData(v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__4(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__3));
v___x_8_ = l_Lean_stringToMessageData(v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(lean_object* v_c_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
uint8_t v_kind_16_; lean_object* v_u_17_; lean_object* v_v_18_; lean_object* v_k_19_; lean_object* v___x_20_; 
v_kind_16_ = lean_ctor_get_uint8(v_c_11_, sizeof(void*)*5);
v_u_17_ = lean_ctor_get(v_c_11_, 0);
v_v_18_ = lean_ctor_get(v_c_11_, 1);
v_k_19_ = lean_ctor_get(v_c_11_, 2);
v___x_20_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_17_, v_a_12_, v_a_13_, v_a_14_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; lean_object* v___x_22_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_a_21_);
lean_dec_ref_known(v___x_20_, 1);
v___x_22_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_18_, v_a_12_, v_a_13_, v_a_14_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_61_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_61_ == 0)
{
v___x_25_ = v___x_22_;
v_isShared_26_ = v_isSharedCheck_61_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_22_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_61_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___y_28_; 
if (v_kind_16_ == 0)
{
lean_object* v___x_59_; 
v___x_59_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__5));
v___y_28_ = v___x_59_;
goto v___jp_27_;
}
else
{
lean_object* v___x_60_; 
v___x_60_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__6));
v___y_28_ = v___x_60_;
goto v___jp_27_;
}
v___jp_27_:
{
lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_29_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0);
v___x_30_ = lean_int_dec_eq(v_k_19_, v___x_29_);
if (v___x_30_ == 0)
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_31_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_21_);
v___x_32_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__2, &l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__2);
v___x_33_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_31_);
lean_ctor_set(v___x_33_, 1, v___x_32_);
lean_inc_ref(v___y_28_);
v___x_34_ = l_Lean_stringToMessageData(v___y_28_);
v___x_35_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_33_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
v___x_36_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___x_32_);
v___x_37_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_23_);
v___x_38_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_36_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
v___x_39_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__4, &l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__4);
v___x_40_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_38_);
lean_ctor_set(v___x_40_, 1, v___x_39_);
v___x_41_ = l_Int_repr(v_k_19_);
v___x_42_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
v___x_43_ = l_Lean_MessageData_ofFormat(v___x_42_);
v___x_44_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_40_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 0, v___x_44_);
v___x_46_ = v___x_25_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_44_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
else
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_57_; 
v___x_48_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_21_);
v___x_49_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__2, &l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__2);
v___x_50_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_48_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
lean_inc_ref(v___y_28_);
v___x_51_ = l_Lean_stringToMessageData(v___y_28_);
v___x_52_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_50_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
v___x_53_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_49_);
v___x_54_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_23_);
v___x_55_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_53_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 0, v___x_55_);
v___x_57_ = v___x_25_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_55_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
}
}
else
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_69_; 
lean_dec(v_a_21_);
v_a_62_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_69_ == 0)
{
v___x_64_ = v___x_22_;
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_22_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
else
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_77_; 
v_a_70_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_77_ == 0)
{
v___x_72_ = v___x_20_;
v_isShared_73_ = v_isSharedCheck_77_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_20_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_77_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_75_; 
if (v_isShared_73_ == 0)
{
v___x_75_ = v___x_72_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_a_70_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___boxed(lean_object* v_c_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(v_c_78_, v_a_79_, v_a_80_, v_a_81_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec(v_a_79_);
lean_dec_ref(v_c_78_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp(lean_object* v_c_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(v_c_84_, v_a_85_, v_a_86_, v_a_94_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___boxed(lean_object* v_c_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec(v_a_100_);
lean_dec(v_a_99_);
lean_dec_ref(v_c_98_);
return v_res_111_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_compare(lean_object* v_a_112_, lean_object* v_b_113_){
_start:
{
lean_object* v_k_114_; uint8_t v_strict_115_; lean_object* v_k_116_; uint8_t v_strict_117_; uint8_t v___x_122_; 
v_k_114_ = lean_ctor_get(v_a_112_, 0);
v_strict_115_ = lean_ctor_get_uint8(v_a_112_, sizeof(void*)*1);
v_k_116_ = lean_ctor_get(v_b_113_, 0);
v_strict_117_ = lean_ctor_get_uint8(v_b_113_, sizeof(void*)*1);
v___x_122_ = lean_int_dec_lt(v_k_114_, v_k_116_);
if (v___x_122_ == 0)
{
uint8_t v___x_123_; 
v___x_123_ = lean_int_dec_lt(v_k_116_, v_k_114_);
if (v___x_123_ == 0)
{
if (v_strict_117_ == 0)
{
if (v_strict_115_ == 0)
{
uint8_t v___x_124_; 
v___x_124_ = 1;
return v___x_124_;
}
else
{
goto v___jp_118_;
}
}
else
{
if (v_strict_115_ == 0)
{
goto v___jp_118_;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = 1;
return v___x_125_;
}
}
}
else
{
uint8_t v___x_126_; 
v___x_126_ = 2;
return v___x_126_;
}
}
else
{
uint8_t v___x_127_; 
v___x_127_ = 0;
return v___x_127_;
}
v___jp_118_:
{
if (v_strict_115_ == 0)
{
uint8_t v___x_119_; 
v___x_119_ = 2;
return v___x_119_;
}
else
{
if (v_strict_117_ == 0)
{
uint8_t v___x_120_; 
v___x_120_ = 0;
return v___x_120_;
}
else
{
uint8_t v___x_121_; 
v___x_121_ = 2;
return v___x_121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_compare___boxed(lean_object* v_a_128_, lean_object* v_b_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_128_, v_b_129_);
lean_dec_ref(v_b_129_);
lean_dec_ref(v_a_128_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instLEWeight(void){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = lean_box(0);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instLTWeight(void){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lean_box(0);
return v___x_135_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLEWeight(lean_object* v_a_136_, lean_object* v_b_137_){
_start:
{
uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_138_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_136_, v_b_137_);
v___x_139_ = lean_box(v___x_138_);
v___x_140_ = lean_obj_tag_nat(v___x_139_);
lean_dec(v___x_139_);
v___x_141_ = lean_unsigned_to_nat(2u);
v___x_142_ = lean_nat_dec_eq(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
uint8_t v___x_143_; 
v___x_143_ = 1;
return v___x_143_;
}
else
{
uint8_t v___x_144_; 
v___x_144_ = 0;
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLEWeight___boxed(lean_object* v_a_145_, lean_object* v_b_146_){
_start:
{
uint8_t v_res_147_; lean_object* v_r_148_; 
v_res_147_ = l_Lean_Meta_Grind_Order_instDecidableLEWeight(v_a_145_, v_b_146_);
lean_dec_ref(v_b_146_);
lean_dec_ref(v_a_145_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLTWeight(lean_object* v_a_149_, lean_object* v_b_150_){
_start:
{
uint8_t v___x_151_; uint8_t v___x_152_; uint8_t v___x_153_; 
v___x_151_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_149_, v_b_150_);
v___x_152_ = 0;
v___x_153_ = l_instDecidableEqOrdering(v___x_151_, v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLTWeight___boxed(lean_object* v_a_154_, lean_object* v_b_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_Lean_Meta_Grind_Order_instDecidableLTWeight(v_a_154_, v_b_155_);
lean_dec_ref(v_b_155_);
lean_dec_ref(v_a_154_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add(lean_object* v_a_158_, lean_object* v_b_159_){
_start:
{
lean_object* v_k_160_; uint8_t v_strict_161_; lean_object* v_k_162_; uint8_t v_strict_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_174_; 
v_k_160_ = lean_ctor_get(v_a_158_, 0);
v_strict_161_ = lean_ctor_get_uint8(v_a_158_, sizeof(void*)*1);
v_k_162_ = lean_ctor_get(v_b_159_, 0);
v_strict_163_ = lean_ctor_get_uint8(v_b_159_, sizeof(void*)*1);
v_isSharedCheck_174_ = !lean_is_exclusive(v_b_159_);
if (v_isSharedCheck_174_ == 0)
{
v___x_165_ = v_b_159_;
v_isShared_166_ = v_isSharedCheck_174_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_k_162_);
lean_dec(v_b_159_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_174_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; 
v___x_167_ = lean_int_add(v_k_160_, v_k_162_);
lean_dec(v_k_162_);
if (v_strict_161_ == 0)
{
lean_object* v___x_169_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_167_);
v___x_169_ = v___x_165_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
lean_ctor_set_uint8(v_reuseFailAlloc_170_, sizeof(void*)*1, v_strict_163_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
else
{
lean_object* v___x_172_; 
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_167_);
v___x_172_ = v___x_165_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*1, v_strict_161_);
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add___boxed(lean_object* v_a_175_, lean_object* v_b_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Meta_Grind_Order_Weight_add(v_a_175_, v_b_176_);
lean_dec_ref(v_a_175_);
return v_res_177_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isNeg(lean_object* v_a_180_){
_start:
{
lean_object* v_k_181_; uint8_t v_strict_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_k_181_ = lean_ctor_get(v_a_180_, 0);
v_strict_182_ = lean_ctor_get_uint8(v_a_180_, sizeof(void*)*1);
v___x_183_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0);
v___x_184_ = lean_int_dec_lt(v_k_181_, v___x_183_);
if (v___x_184_ == 0)
{
uint8_t v___x_185_; 
v___x_185_ = lean_int_dec_eq(v_k_181_, v___x_183_);
if (v___x_185_ == 0)
{
return v___x_185_;
}
else
{
return v_strict_182_;
}
}
else
{
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isNeg___boxed(lean_object* v_a_186_){
_start:
{
uint8_t v_res_187_; lean_object* v_r_188_; 
v_res_187_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v_a_186_);
lean_dec_ref(v_a_186_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isZero(lean_object* v_a_189_){
_start:
{
lean_object* v_k_190_; uint8_t v_strict_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_k_190_ = lean_ctor_get(v_a_189_, 0);
v_strict_191_ = lean_ctor_get_uint8(v_a_189_, sizeof(void*)*1);
v___x_192_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0);
v___x_193_ = lean_int_dec_eq(v_k_190_, v___x_192_);
if (v___x_193_ == 0)
{
return v___x_193_;
}
else
{
if (v_strict_191_ == 0)
{
return v___x_193_;
}
else
{
uint8_t v___x_194_; 
v___x_194_ = 0;
return v___x_194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isZero___boxed(lean_object* v_a_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_a_195_);
lean_dec_ref(v_a_195_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(lean_object* v_a_199_){
_start:
{
uint8_t v_strict_200_; 
v_strict_200_ = lean_ctor_get_uint8(v_a_199_, sizeof(void*)*1);
if (v_strict_200_ == 0)
{
lean_object* v_k_201_; lean_object* v___x_202_; 
v_k_201_ = lean_ctor_get(v_a_199_, 0);
v___x_202_ = l_Int_repr(v_k_201_);
return v___x_202_;
}
else
{
lean_object* v_k_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_k_203_ = lean_ctor_get(v_a_199_, 0);
v___x_204_ = l_Int_repr(v_k_203_);
v___x_205_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_206_ = lean_string_append(v___x_204_, v___x_205_);
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed(lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(v_a_207_);
lean_dec_ref(v_a_207_);
return v_res_208_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__0));
v___x_213_ = l_Lean_stringToMessageData(v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__2));
v___x_216_ = l_Lean_stringToMessageData(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__5(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__4));
v___x_219_ = l_Lean_stringToMessageData(v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__7(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__6));
v___x_222_ = l_Lean_stringToMessageData(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg(lean_object* v_todo_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
switch(lean_obj_tag(v_todo_223_))
{
case 0:
{
lean_object* v_e_228_; lean_object* v_u_229_; lean_object* v_v_230_; lean_object* v_k_231_; lean_object* v_k_x27_232_; lean_object* v___x_233_; 
v_e_228_ = lean_ctor_get(v_todo_223_, 1);
lean_inc_ref(v_e_228_);
v_u_229_ = lean_ctor_get(v_todo_223_, 2);
lean_inc(v_u_229_);
v_v_230_ = lean_ctor_get(v_todo_223_, 3);
lean_inc(v_v_230_);
v_k_231_ = lean_ctor_get(v_todo_223_, 4);
lean_inc_ref(v_k_231_);
v_k_x27_232_ = lean_ctor_get(v_todo_223_, 5);
lean_inc_ref(v_k_x27_232_);
lean_dec_ref_known(v_todo_223_, 6);
v___x_233_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_229_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_u_229_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_235_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref_known(v___x_233_, 1);
v___x_235_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_230_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_v_230_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_278_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_278_ == 0)
{
v___x_238_ = v___x_235_;
v_isShared_239_ = v_isSharedCheck_278_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_235_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_278_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v_k_254_; uint8_t v_strict_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___y_263_; 
v___x_249_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__1, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__1);
v___x_250_ = l_Lean_MessageData_ofExpr(v_e_228_);
v___x_251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3);
v___x_253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_251_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v_k_254_ = lean_ctor_get(v_k_231_, 0);
lean_inc(v_k_254_);
v_strict_255_ = lean_ctor_get_uint8(v_k_231_, sizeof(void*)*1);
lean_dec_ref(v_k_231_);
v___x_256_ = l_Lean_MessageData_ofExpr(v_a_234_);
v___x_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_253_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v___x_252_);
v___x_259_ = l_Lean_MessageData_ofExpr(v_a_236_);
v___x_260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_252_);
if (v_strict_255_ == 0)
{
lean_object* v___x_274_; 
v___x_274_ = l_Int_repr(v_k_254_);
lean_dec(v_k_254_);
v___y_263_ = v___x_274_;
goto v___jp_262_;
}
else
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = l_Int_repr(v_k_254_);
lean_dec(v_k_254_);
v___x_276_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_277_ = lean_string_append(v___x_275_, v___x_276_);
v___y_263_ = v___x_277_;
goto v___jp_262_;
}
v___jp_240_:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_243_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_243_, 0, v___y_242_);
v___x_244_ = l_Lean_MessageData_ofFormat(v___x_243_);
v___x_245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_245_, 0, v___y_241_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 0, v___x_245_);
v___x_247_ = v___x_238_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
v___jp_262_:
{
lean_object* v_k_264_; uint8_t v_strict_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_k_264_ = lean_ctor_get(v_k_x27_232_, 0);
lean_inc(v_k_264_);
v_strict_265_ = lean_ctor_get_uint8(v_k_x27_232_, sizeof(void*)*1);
lean_dec_ref(v_k_x27_232_);
v___x_266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_266_, 0, v___y_263_);
v___x_267_ = l_Lean_MessageData_ofFormat(v___x_266_);
v___x_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_261_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_252_);
if (v_strict_265_ == 0)
{
lean_object* v___x_270_; 
v___x_270_ = l_Int_repr(v_k_264_);
lean_dec(v_k_264_);
v___y_241_ = v___x_269_;
v___y_242_ = v___x_270_;
goto v___jp_240_;
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = l_Int_repr(v_k_264_);
lean_dec(v_k_264_);
v___x_272_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_273_ = lean_string_append(v___x_271_, v___x_272_);
v___y_241_ = v___x_269_;
v___y_242_ = v___x_273_;
goto v___jp_240_;
}
}
}
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
lean_dec(v_a_234_);
lean_dec_ref(v_k_x27_232_);
lean_dec_ref(v_k_231_);
lean_dec_ref(v_e_228_);
v_a_279_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_235_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_235_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec_ref(v_k_x27_232_);
lean_dec_ref(v_k_231_);
lean_dec(v_v_230_);
lean_dec_ref(v_e_228_);
v_a_287_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_233_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_233_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
case 1:
{
lean_object* v_e_295_; lean_object* v_u_296_; lean_object* v_v_297_; lean_object* v_k_298_; lean_object* v_k_x27_299_; lean_object* v___x_300_; 
v_e_295_ = lean_ctor_get(v_todo_223_, 1);
lean_inc_ref(v_e_295_);
v_u_296_ = lean_ctor_get(v_todo_223_, 2);
lean_inc(v_u_296_);
v_v_297_ = lean_ctor_get(v_todo_223_, 3);
lean_inc(v_v_297_);
v_k_298_ = lean_ctor_get(v_todo_223_, 4);
lean_inc_ref(v_k_298_);
v_k_x27_299_ = lean_ctor_get(v_todo_223_, 5);
lean_inc_ref(v_k_x27_299_);
lean_dec_ref_known(v_todo_223_, 6);
v___x_300_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_296_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_u_296_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_302_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
lean_dec_ref_known(v___x_300_, 1);
v___x_302_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_297_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_v_297_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_345_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_345_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_345_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_345_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v_k_321_; uint8_t v_strict_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___y_330_; 
v___x_316_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__5, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__5);
v___x_317_ = l_Lean_MessageData_ofExpr(v_e_295_);
v___x_318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3);
v___x_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v_k_321_ = lean_ctor_get(v_k_298_, 0);
lean_inc(v_k_321_);
v_strict_322_ = lean_ctor_get_uint8(v_k_298_, sizeof(void*)*1);
lean_dec_ref(v_k_298_);
v___x_323_ = l_Lean_MessageData_ofExpr(v_a_301_);
v___x_324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_320_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___x_319_);
v___x_326_ = l_Lean_MessageData_ofExpr(v_a_303_);
v___x_327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_319_);
if (v_strict_322_ == 0)
{
lean_object* v___x_341_; 
v___x_341_ = l_Int_repr(v_k_321_);
lean_dec(v_k_321_);
v___y_330_ = v___x_341_;
goto v___jp_329_;
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = l_Int_repr(v_k_321_);
lean_dec(v_k_321_);
v___x_343_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_344_ = lean_string_append(v___x_342_, v___x_343_);
v___y_330_ = v___x_344_;
goto v___jp_329_;
}
v___jp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_310_, 0, v___y_309_);
v___x_311_ = l_Lean_MessageData_ofFormat(v___x_310_);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___y_308_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_312_);
v___x_314_ = v___x_305_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
v___jp_329_:
{
lean_object* v_k_331_; uint8_t v_strict_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_k_331_ = lean_ctor_get(v_k_x27_299_, 0);
lean_inc(v_k_331_);
v_strict_332_ = lean_ctor_get_uint8(v_k_x27_299_, sizeof(void*)*1);
lean_dec_ref(v_k_x27_299_);
v___x_333_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_333_, 0, v___y_330_);
v___x_334_ = l_Lean_MessageData_ofFormat(v___x_333_);
v___x_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_328_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_319_);
if (v_strict_332_ == 0)
{
lean_object* v___x_337_; 
v___x_337_ = l_Int_repr(v_k_331_);
lean_dec(v_k_331_);
v___y_308_ = v___x_336_;
v___y_309_ = v___x_337_;
goto v___jp_307_;
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = l_Int_repr(v_k_331_);
lean_dec(v_k_331_);
v___x_339_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_340_ = lean_string_append(v___x_338_, v___x_339_);
v___y_308_ = v___x_336_;
v___y_309_ = v___x_340_;
goto v___jp_307_;
}
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec(v_a_301_);
lean_dec_ref(v_k_x27_299_);
lean_dec_ref(v_k_298_);
lean_dec_ref(v_e_295_);
v_a_346_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_302_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_302_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec_ref(v_k_x27_299_);
lean_dec_ref(v_k_298_);
lean_dec(v_v_297_);
lean_dec_ref(v_e_295_);
v_a_354_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_300_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_300_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
default: 
{
lean_object* v_u_362_; lean_object* v_v_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_403_; 
v_u_362_ = lean_ctor_get(v_todo_223_, 0);
v_v_363_ = lean_ctor_get(v_todo_223_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v_todo_223_);
if (v_isSharedCheck_403_ == 0)
{
v___x_365_ = v_todo_223_;
v_isShared_366_ = v_isSharedCheck_403_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_v_363_);
lean_inc(v_u_362_);
lean_dec(v_todo_223_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_403_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_362_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_u_362_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_369_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_367_, 1);
v___x_369_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_363_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_v_363_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_386_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_386_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_386_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_386_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_374_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__7, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__7_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__7);
v___x_375_ = l_Lean_MessageData_ofExpr(v_a_368_);
if (v_isShared_366_ == 0)
{
lean_ctor_set_tag(v___x_365_, 7);
lean_ctor_set(v___x_365_, 1, v___x_375_);
lean_ctor_set(v___x_365_, 0, v___x_374_);
v___x_377_ = v___x_365_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v___x_375_);
v___x_377_ = v_reuseFailAlloc_385_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_378_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3);
v___x_379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = l_Lean_MessageData_ofExpr(v_a_370_);
v___x_381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_379_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_381_);
v___x_383_ = v___x_372_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
lean_dec(v_a_368_);
lean_del_object(v___x_365_);
v_a_387_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_369_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_369_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_del_object(v___x_365_);
lean_dec(v_v_363_);
v_a_395_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_367_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_367_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___boxed(lean_object* v_todo_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg(v_todo_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec(v_a_405_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object* v_todo_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg(v_todo_410_, v_a_411_, v_a_412_, v_a_420_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___boxed(lean_object* v_todo_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_Grind_Order_ToPropagate_pp(v_todo_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec(v_a_426_);
lean_dec(v_a_425_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(lean_object* v_c_438_){
_start:
{
uint8_t v_kind_439_; 
v_kind_439_ = lean_ctor_get_uint8(v_c_438_, sizeof(void*)*5);
if (v_kind_439_ == 0)
{
lean_object* v_k_440_; uint8_t v___x_441_; lean_object* v___x_442_; 
v_k_440_ = lean_ctor_get(v_c_438_, 2);
v___x_441_ = 0;
lean_inc(v_k_440_);
v___x_442_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_442_, 0, v_k_440_);
lean_ctor_set_uint8(v___x_442_, sizeof(void*)*1, v___x_441_);
return v___x_442_;
}
else
{
lean_object* v_k_443_; uint8_t v___x_444_; lean_object* v___x_445_; 
v_k_443_ = lean_ctor_get(v_c_438_, 2);
v___x_444_ = 1;
lean_inc(v_k_443_);
v___x_445_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_445_, 0, v_k_443_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*1, v___x_444_);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg___boxed(lean_object* v_c_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_446_);
lean_dec_ref(v_c_446_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight(lean_object* v_00_u03b1_448_, lean_object* v_c_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___boxed(lean_object* v_00_u03b1_451_, lean_object* v_c_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight(v_00_u03b1_451_, v_c_452_);
lean_dec_ref(v_c_452_);
return v_res_453_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Order_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Order_Util(builtin);
}
#ifdef __cplusplus
}
#endif
