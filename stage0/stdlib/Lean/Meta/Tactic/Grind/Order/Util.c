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
lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(lean_object* v_c_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_){
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
LEAN_EXPORT void l_Lean_Meta_Grind_Order_Cnstr_pp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_11_ = stack[0].m_obj;
lean_object* v_a_12_ = stack[1].m_obj;
lean_object* v_a_13_ = stack[2].m_obj;
lean_object* v_a_14_ = stack[3].m_obj;
lean_object* v_res_78_;
v_res_78_ = l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(v_c_11_, v_a_12_, v_a_13_, v_a_14_);
stack->m_obj
 = v_res_78_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___boxed(lean_object* v_c_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(v_c_79_, v_a_80_, v_a_81_, v_a_82_);
lean_dec_ref(v_a_82_);
lean_dec(v_a_81_);
lean_dec(v_a_80_);
lean_dec_ref(v_c_79_);
return v_res_84_;
}
}
lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp(lean_object* v_c_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(v_c_85_, v_a_86_, v_a_87_, v_a_95_);
return v___x_98_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_Cnstr_pp_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_85_ = stack[0].m_obj;
lean_object* v_a_86_ = stack[1].m_obj;
lean_object* v_a_87_ = stack[2].m_obj;
lean_object* v_a_88_ = stack[3].m_obj;
lean_object* v_a_89_ = stack[4].m_obj;
lean_object* v_a_90_ = stack[5].m_obj;
lean_object* v_a_91_ = stack[6].m_obj;
lean_object* v_a_92_ = stack[7].m_obj;
lean_object* v_a_93_ = stack[8].m_obj;
lean_object* v_a_94_ = stack[9].m_obj;
lean_object* v_a_95_ = stack[10].m_obj;
lean_object* v_a_96_ = stack[11].m_obj;
lean_object* v_res_99_;
v_res_99_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
stack->m_obj
 = v_res_99_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___boxed(lean_object* v_c_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_c_100_);
return v_res_113_;
}
}
uint8_t l_Lean_Meta_Grind_Order_Weight_compare(lean_object* v_a_114_, lean_object* v_b_115_){
_start:
{
lean_object* v_k_116_; uint8_t v_strict_117_; lean_object* v_k_118_; uint8_t v_strict_119_; uint8_t v___x_124_; 
v_k_116_ = lean_ctor_get(v_a_114_, 0);
v_strict_117_ = lean_ctor_get_uint8(v_a_114_, sizeof(void*)*1);
v_k_118_ = lean_ctor_get(v_b_115_, 0);
v_strict_119_ = lean_ctor_get_uint8(v_b_115_, sizeof(void*)*1);
v___x_124_ = lean_int_dec_lt(v_k_116_, v_k_118_);
if (v___x_124_ == 0)
{
uint8_t v___x_125_; 
v___x_125_ = lean_int_dec_lt(v_k_118_, v_k_116_);
if (v___x_125_ == 0)
{
if (v_strict_119_ == 0)
{
if (v_strict_117_ == 0)
{
uint8_t v___x_126_; 
v___x_126_ = 1;
return v___x_126_;
}
else
{
goto v___jp_120_;
}
}
else
{
if (v_strict_117_ == 0)
{
goto v___jp_120_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = 1;
return v___x_127_;
}
}
}
else
{
uint8_t v___x_128_; 
v___x_128_ = 2;
return v___x_128_;
}
}
else
{
uint8_t v___x_129_; 
v___x_129_ = 0;
return v___x_129_;
}
v___jp_120_:
{
if (v_strict_117_ == 0)
{
uint8_t v___x_121_; 
v___x_121_ = 2;
return v___x_121_;
}
else
{
if (v_strict_119_ == 0)
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
else
{
uint8_t v___x_123_; 
v___x_123_ = 2;
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_Weight_compare_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_114_ = stack[0].m_obj;
lean_object* v_b_115_ = stack[1].m_obj;
uint8_t v_res_130_;
v_res_130_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_114_, v_b_115_);
stack->m_num = v_res_130_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_compare___boxed(lean_object* v_a_131_, lean_object* v_b_132_){
_start:
{
uint8_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_131_, v_b_132_);
lean_dec_ref(v_b_132_);
lean_dec_ref(v_a_131_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instLEWeight(void){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_box(0);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instLTWeight(void){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lean_box(0);
return v___x_138_;
}
}
uint8_t l_Lean_Meta_Grind_Order_instDecidableLEWeight(lean_object* v_a_139_, lean_object* v_b_140_){
_start:
{
uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_141_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_139_, v_b_140_);
v___x_142_ = lean_box(v___x_141_);
v___x_143_ = lean_obj_tag_nat(v___x_142_);
lean_dec(v___x_142_);
v___x_144_ = lean_unsigned_to_nat(2u);
v___x_145_ = lean_nat_dec_eq(v___x_143_, v___x_144_);
if (v___x_145_ == 0)
{
uint8_t v___x_146_; 
v___x_146_ = 1;
return v___x_146_;
}
else
{
uint8_t v___x_147_; 
v___x_147_ = 0;
return v___x_147_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_instDecidableLEWeight_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_139_ = stack[0].m_obj;
lean_object* v_b_140_ = stack[1].m_obj;
uint8_t v_res_148_;
v_res_148_ = l_Lean_Meta_Grind_Order_instDecidableLEWeight(v_a_139_, v_b_140_);
stack->m_num = v_res_148_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLEWeight___boxed(lean_object* v_a_149_, lean_object* v_b_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Lean_Meta_Grind_Order_instDecidableLEWeight(v_a_149_, v_b_150_);
lean_dec_ref(v_b_150_);
lean_dec_ref(v_a_149_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
uint8_t l_Lean_Meta_Grind_Order_instDecidableLTWeight(lean_object* v_a_153_, lean_object* v_b_154_){
_start:
{
uint8_t v___x_155_; uint8_t v___x_156_; uint8_t v___x_157_; 
v___x_155_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_153_, v_b_154_);
v___x_156_ = 0;
v___x_157_ = l_instDecidableEqOrdering(v___x_155_, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_instDecidableLTWeight_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_153_ = stack[0].m_obj;
lean_object* v_b_154_ = stack[1].m_obj;
uint8_t v_res_158_;
v_res_158_ = l_Lean_Meta_Grind_Order_instDecidableLTWeight(v_a_153_, v_b_154_);
stack->m_num = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLTWeight___boxed(lean_object* v_a_159_, lean_object* v_b_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Lean_Meta_Grind_Order_instDecidableLTWeight(v_a_159_, v_b_160_);
lean_dec_ref(v_b_160_);
lean_dec_ref(v_a_159_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add(lean_object* v_a_163_, lean_object* v_b_164_){
_start:
{
lean_object* v_k_165_; uint8_t v_strict_166_; lean_object* v_k_167_; uint8_t v_strict_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_179_; 
v_k_165_ = lean_ctor_get(v_a_163_, 0);
v_strict_166_ = lean_ctor_get_uint8(v_a_163_, sizeof(void*)*1);
v_k_167_ = lean_ctor_get(v_b_164_, 0);
v_strict_168_ = lean_ctor_get_uint8(v_b_164_, sizeof(void*)*1);
v_isSharedCheck_179_ = !lean_is_exclusive(v_b_164_);
if (v_isSharedCheck_179_ == 0)
{
v___x_170_ = v_b_164_;
v_isShared_171_ = v_isSharedCheck_179_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_k_167_);
lean_dec(v_b_164_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_179_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; 
v___x_172_ = lean_int_add(v_k_165_, v_k_167_);
lean_dec(v_k_167_);
if (v_strict_166_ == 0)
{
lean_object* v___x_174_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_172_);
v___x_174_ = v___x_170_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
lean_ctor_set_uint8(v_reuseFailAlloc_175_, sizeof(void*)*1, v_strict_168_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
else
{
lean_object* v___x_177_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_172_);
v___x_177_ = v___x_170_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*1, v_strict_166_);
return v___x_177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add___boxed(lean_object* v_a_180_, lean_object* v_b_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Meta_Grind_Order_Weight_add(v_a_180_, v_b_181_);
lean_dec_ref(v_a_180_);
return v_res_182_;
}
}
uint8_t l_Lean_Meta_Grind_Order_Weight_isNeg(lean_object* v_a_185_){
_start:
{
lean_object* v_k_186_; uint8_t v_strict_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v_k_186_ = lean_ctor_get(v_a_185_, 0);
v_strict_187_ = lean_ctor_get_uint8(v_a_185_, sizeof(void*)*1);
v___x_188_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0);
v___x_189_ = lean_int_dec_lt(v_k_186_, v___x_188_);
if (v___x_189_ == 0)
{
uint8_t v___x_190_; 
v___x_190_ = lean_int_dec_eq(v_k_186_, v___x_188_);
if (v___x_190_ == 0)
{
return v___x_190_;
}
else
{
return v_strict_187_;
}
}
else
{
return v___x_189_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_Weight_isNeg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_185_ = stack[0].m_obj;
uint8_t v_res_191_;
v_res_191_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v_a_185_);
stack->m_num = v_res_191_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isNeg___boxed(lean_object* v_a_192_){
_start:
{
uint8_t v_res_193_; lean_object* v_r_194_; 
v_res_193_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v_a_192_);
lean_dec_ref(v_a_192_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
uint8_t l_Lean_Meta_Grind_Order_Weight_isZero(lean_object* v_a_195_){
_start:
{
lean_object* v_k_196_; uint8_t v_strict_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_k_196_ = lean_ctor_get(v_a_195_, 0);
v_strict_197_ = lean_ctor_get_uint8(v_a_195_, sizeof(void*)*1);
v___x_198_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0);
v___x_199_ = lean_int_dec_eq(v_k_196_, v___x_198_);
if (v___x_199_ == 0)
{
return v___x_199_;
}
else
{
if (v_strict_197_ == 0)
{
return v___x_199_;
}
else
{
uint8_t v___x_200_; 
v___x_200_ = 0;
return v___x_200_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_Weight_isZero_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_195_ = stack[0].m_obj;
uint8_t v_res_201_;
v_res_201_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_a_195_);
stack->m_num = v_res_201_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isZero___boxed(lean_object* v_a_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_a_202_);
lean_dec_ref(v_a_202_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(lean_object* v_a_206_){
_start:
{
uint8_t v_strict_207_; 
v_strict_207_ = lean_ctor_get_uint8(v_a_206_, sizeof(void*)*1);
if (v_strict_207_ == 0)
{
lean_object* v_k_208_; lean_object* v___x_209_; 
v_k_208_ = lean_ctor_get(v_a_206_, 0);
v___x_209_ = l_Int_repr(v_k_208_);
return v___x_209_;
}
else
{
lean_object* v_k_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_k_210_ = lean_ctor_get(v_a_206_, 0);
v___x_211_ = l_Int_repr(v_k_210_);
v___x_212_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_213_ = lean_string_append(v___x_211_, v___x_212_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed(lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(v_a_214_);
lean_dec_ref(v_a_214_);
return v_res_215_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__0));
v___x_220_ = l_Lean_stringToMessageData(v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__2));
v___x_223_ = l_Lean_stringToMessageData(v___x_222_);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__5(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__4));
v___x_226_ = l_Lean_stringToMessageData(v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__7(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__6));
v___x_229_ = l_Lean_stringToMessageData(v___x_228_);
return v___x_229_;
}
}
lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg(lean_object* v_todo_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
switch(lean_obj_tag(v_todo_230_))
{
case 0:
{
lean_object* v_e_235_; lean_object* v_u_236_; lean_object* v_v_237_; lean_object* v_k_238_; lean_object* v_k_x27_239_; lean_object* v___x_240_; 
v_e_235_ = lean_ctor_get(v_todo_230_, 1);
lean_inc_ref(v_e_235_);
v_u_236_ = lean_ctor_get(v_todo_230_, 2);
lean_inc(v_u_236_);
v_v_237_ = lean_ctor_get(v_todo_230_, 3);
lean_inc(v_v_237_);
v_k_238_ = lean_ctor_get(v_todo_230_, 4);
lean_inc_ref(v_k_238_);
v_k_x27_239_ = lean_ctor_get(v_todo_230_, 5);
lean_inc_ref(v_k_x27_239_);
lean_dec_ref_known(v_todo_230_, 6);
v___x_240_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_236_, v_a_231_, v_a_232_, v_a_233_);
lean_dec(v_u_236_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_242_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_241_);
lean_dec_ref_known(v___x_240_, 1);
v___x_242_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_237_, v_a_231_, v_a_232_, v_a_233_);
lean_dec(v_v_237_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_285_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_285_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_285_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_285_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v_k_261_; uint8_t v_strict_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___y_270_; 
v___x_256_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__1, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__1);
v___x_257_ = l_Lean_MessageData_ofExpr(v_e_235_);
v___x_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3);
v___x_260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v_k_261_ = lean_ctor_get(v_k_238_, 0);
lean_inc(v_k_261_);
v_strict_262_ = lean_ctor_get_uint8(v_k_238_, sizeof(void*)*1);
lean_dec_ref(v_k_238_);
v___x_263_ = l_Lean_MessageData_ofExpr(v_a_241_);
v___x_264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_260_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___x_259_);
v___x_266_ = l_Lean_MessageData_ofExpr(v_a_243_);
v___x_267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_259_);
if (v_strict_262_ == 0)
{
lean_object* v___x_281_; 
v___x_281_ = l_Int_repr(v_k_261_);
lean_dec(v_k_261_);
v___y_270_ = v___x_281_;
goto v___jp_269_;
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = l_Int_repr(v_k_261_);
lean_dec(v_k_261_);
v___x_283_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_284_ = lean_string_append(v___x_282_, v___x_283_);
v___y_270_ = v___x_284_;
goto v___jp_269_;
}
v___jp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_250_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_250_, 0, v___y_249_);
v___x_251_ = l_Lean_MessageData_ofFormat(v___x_250_);
v___x_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_252_, 0, v___y_248_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_252_);
v___x_254_ = v___x_245_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
v___jp_269_:
{
lean_object* v_k_271_; uint8_t v_strict_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_k_271_ = lean_ctor_get(v_k_x27_239_, 0);
lean_inc(v_k_271_);
v_strict_272_ = lean_ctor_get_uint8(v_k_x27_239_, sizeof(void*)*1);
lean_dec_ref(v_k_x27_239_);
v___x_273_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_273_, 0, v___y_270_);
v___x_274_ = l_Lean_MessageData_ofFormat(v___x_273_);
v___x_275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_268_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_259_);
if (v_strict_272_ == 0)
{
lean_object* v___x_277_; 
v___x_277_ = l_Int_repr(v_k_271_);
lean_dec(v_k_271_);
v___y_248_ = v___x_276_;
v___y_249_ = v___x_277_;
goto v___jp_247_;
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = l_Int_repr(v_k_271_);
lean_dec(v_k_271_);
v___x_279_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_280_ = lean_string_append(v___x_278_, v___x_279_);
v___y_248_ = v___x_276_;
v___y_249_ = v___x_280_;
goto v___jp_247_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec(v_a_241_);
lean_dec_ref(v_k_x27_239_);
lean_dec_ref(v_k_238_);
lean_dec_ref(v_e_235_);
v_a_286_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_242_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_242_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
lean_dec_ref(v_k_x27_239_);
lean_dec_ref(v_k_238_);
lean_dec(v_v_237_);
lean_dec_ref(v_e_235_);
v_a_294_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_240_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_240_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
case 1:
{
lean_object* v_e_302_; lean_object* v_u_303_; lean_object* v_v_304_; lean_object* v_k_305_; lean_object* v_k_x27_306_; lean_object* v___x_307_; 
v_e_302_ = lean_ctor_get(v_todo_230_, 1);
lean_inc_ref(v_e_302_);
v_u_303_ = lean_ctor_get(v_todo_230_, 2);
lean_inc(v_u_303_);
v_v_304_ = lean_ctor_get(v_todo_230_, 3);
lean_inc(v_v_304_);
v_k_305_ = lean_ctor_get(v_todo_230_, 4);
lean_inc_ref(v_k_305_);
v_k_x27_306_ = lean_ctor_get(v_todo_230_, 5);
lean_inc_ref(v_k_x27_306_);
lean_dec_ref_known(v_todo_230_, 6);
v___x_307_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_303_, v_a_231_, v_a_232_, v_a_233_);
lean_dec(v_u_303_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_309_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v___x_307_, 1);
v___x_309_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_304_, v_a_231_, v_a_232_, v_a_233_);
lean_dec(v_v_304_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_352_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_352_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_352_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_352_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_k_328_; uint8_t v_strict_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___y_337_; 
v___x_323_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__5, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__5);
v___x_324_ = l_Lean_MessageData_ofExpr(v_e_302_);
v___x_325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_323_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3);
v___x_327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v_k_328_ = lean_ctor_get(v_k_305_, 0);
lean_inc(v_k_328_);
v_strict_329_ = lean_ctor_get_uint8(v_k_305_, sizeof(void*)*1);
lean_dec_ref(v_k_305_);
v___x_330_ = l_Lean_MessageData_ofExpr(v_a_308_);
v___x_331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_327_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_326_);
v___x_333_ = l_Lean_MessageData_ofExpr(v_a_310_);
v___x_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_326_);
if (v_strict_329_ == 0)
{
lean_object* v___x_348_; 
v___x_348_ = l_Int_repr(v_k_328_);
lean_dec(v_k_328_);
v___y_337_ = v___x_348_;
goto v___jp_336_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = l_Int_repr(v_k_328_);
lean_dec(v_k_328_);
v___x_350_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_351_ = lean_string_append(v___x_349_, v___x_350_);
v___y_337_ = v___x_351_;
goto v___jp_336_;
}
v___jp_314_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_317_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_317_, 0, v___y_316_);
v___x_318_ = l_Lean_MessageData_ofFormat(v___x_317_);
v___x_319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_319_, 0, v___y_315_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_319_);
v___x_321_ = v___x_312_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
v___jp_336_:
{
lean_object* v_k_338_; uint8_t v_strict_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_k_338_ = lean_ctor_get(v_k_x27_306_, 0);
lean_inc(v_k_338_);
v_strict_339_ = lean_ctor_get_uint8(v_k_x27_306_, sizeof(void*)*1);
lean_dec_ref(v_k_x27_306_);
v___x_340_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_340_, 0, v___y_337_);
v___x_341_ = l_Lean_MessageData_ofFormat(v___x_340_);
v___x_342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_335_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_326_);
if (v_strict_339_ == 0)
{
lean_object* v___x_344_; 
v___x_344_ = l_Int_repr(v_k_338_);
lean_dec(v_k_338_);
v___y_315_ = v___x_343_;
v___y_316_ = v___x_344_;
goto v___jp_314_;
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = l_Int_repr(v_k_338_);
lean_dec(v_k_338_);
v___x_346_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_347_ = lean_string_append(v___x_345_, v___x_346_);
v___y_315_ = v___x_343_;
v___y_316_ = v___x_347_;
goto v___jp_314_;
}
}
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_dec(v_a_308_);
lean_dec_ref(v_k_x27_306_);
lean_dec_ref(v_k_305_);
lean_dec_ref(v_e_302_);
v_a_353_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_309_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_309_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_dec_ref(v_k_x27_306_);
lean_dec_ref(v_k_305_);
lean_dec(v_v_304_);
lean_dec_ref(v_e_302_);
v_a_361_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_307_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_307_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
default: 
{
lean_object* v_u_369_; lean_object* v_v_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_410_; 
v_u_369_ = lean_ctor_get(v_todo_230_, 0);
v_v_370_ = lean_ctor_get(v_todo_230_, 1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_todo_230_);
if (v_isSharedCheck_410_ == 0)
{
v___x_372_ = v_todo_230_;
v_isShared_373_ = v_isSharedCheck_410_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_v_370_);
lean_inc(v_u_369_);
lean_dec(v_todo_230_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_410_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_369_, v_a_231_, v_a_232_, v_a_233_);
lean_dec(v_u_369_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_376_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_374_, 1);
v___x_376_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_370_, v_a_231_, v_a_232_, v_a_233_);
lean_dec(v_v_370_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_393_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_393_ == 0)
{
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_393_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_393_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_381_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__7, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__7_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__7);
v___x_382_ = l_Lean_MessageData_ofExpr(v_a_375_);
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 7);
lean_ctor_set(v___x_372_, 1, v___x_382_);
lean_ctor_set(v___x_372_, 0, v___x_381_);
v___x_384_ = v___x_372_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v___x_382_);
v___x_384_ = v_reuseFailAlloc_392_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_385_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3);
v___x_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = l_Lean_MessageData_ofExpr(v_a_377_);
v___x_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_388_);
v___x_390_ = v___x_379_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec(v_a_375_);
lean_del_object(v___x_372_);
v_a_394_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_376_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_376_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_del_object(v___x_372_);
lean_dec(v_v_370_);
v_a_402_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_374_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_374_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_todo_230_ = stack[0].m_obj;
lean_object* v_a_231_ = stack[1].m_obj;
lean_object* v_a_232_ = stack[2].m_obj;
lean_object* v_a_233_ = stack[3].m_obj;
lean_object* v_res_411_;
v_res_411_ = l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg(v_todo_230_, v_a_231_, v_a_232_, v_a_233_);
stack->m_obj
 = v_res_411_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___boxed(lean_object* v_todo_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg(v_todo_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec(v_a_413_);
return v_res_417_;
}
}
lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object* v_todo_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg(v_todo_418_, v_a_419_, v_a_420_, v_a_428_);
return v___x_431_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_ToPropagate_pp_0interp(lean_interpreter_value* stack)
{
lean_object* v_todo_418_ = stack[0].m_obj;
lean_object* v_a_419_ = stack[1].m_obj;
lean_object* v_a_420_ = stack[2].m_obj;
lean_object* v_a_421_ = stack[3].m_obj;
lean_object* v_a_422_ = stack[4].m_obj;
lean_object* v_a_423_ = stack[5].m_obj;
lean_object* v_a_424_ = stack[6].m_obj;
lean_object* v_a_425_ = stack[7].m_obj;
lean_object* v_a_426_ = stack[8].m_obj;
lean_object* v_a_427_ = stack[9].m_obj;
lean_object* v_a_428_ = stack[10].m_obj;
lean_object* v_a_429_ = stack[11].m_obj;
lean_object* v_res_432_;
v_res_432_ = l_Lean_Meta_Grind_Order_ToPropagate_pp(v_todo_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
stack->m_obj
 = v_res_432_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___boxed(lean_object* v_todo_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Meta_Grind_Order_ToPropagate_pp(v_todo_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec(v_a_435_);
lean_dec(v_a_434_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(lean_object* v_c_447_){
_start:
{
uint8_t v_kind_448_; 
v_kind_448_ = lean_ctor_get_uint8(v_c_447_, sizeof(void*)*5);
if (v_kind_448_ == 0)
{
lean_object* v_k_449_; uint8_t v___x_450_; lean_object* v___x_451_; 
v_k_449_ = lean_ctor_get(v_c_447_, 2);
v___x_450_ = 0;
lean_inc(v_k_449_);
v___x_451_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_451_, 0, v_k_449_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*1, v___x_450_);
return v___x_451_;
}
else
{
lean_object* v_k_452_; uint8_t v___x_453_; lean_object* v___x_454_; 
v_k_452_ = lean_ctor_get(v_c_447_, 2);
v___x_453_ = 1;
lean_inc(v_k_452_);
v___x_454_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_454_, 0, v_k_452_);
lean_ctor_set_uint8(v___x_454_, sizeof(void*)*1, v___x_453_);
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg___boxed(lean_object* v_c_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_455_);
lean_dec_ref(v_c_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight(lean_object* v_00_u03b1_457_, lean_object* v_c_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___boxed(lean_object* v_00_u03b1_460_, lean_object* v_c_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight(v_00_u03b1_460_, v_c_461_);
lean_dec_ref(v_c_461_);
return v_res_462_;
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
