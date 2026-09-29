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
lean_object* l_Ordering_ctorIdx(uint8_t);
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
static lean_once_cell_t l_Lean_Meta_Grind_Order_instDecidableLEWeight___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_instDecidableLEWeight___closed__0;
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
static lean_object* _init_l_Lean_Meta_Grind_Order_instDecidableLEWeight___closed__0(void){
_start:
{
uint8_t v___x_136_; lean_object* v___x_137_; 
v___x_136_ = 2;
v___x_137_ = l_Ordering_ctorIdx(v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLEWeight(lean_object* v_a_138_, lean_object* v_b_139_){
_start:
{
uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_140_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_138_, v_b_139_);
v___x_141_ = l_Ordering_ctorIdx(v___x_140_);
v___x_142_ = lean_obj_once(&l_Lean_Meta_Grind_Order_instDecidableLEWeight___closed__0, &l_Lean_Meta_Grind_Order_instDecidableLEWeight___closed__0_once, _init_l_Lean_Meta_Grind_Order_instDecidableLEWeight___closed__0);
v___x_143_ = lean_nat_dec_eq(v___x_141_, v___x_142_);
lean_dec(v___x_141_);
if (v___x_143_ == 0)
{
uint8_t v___x_144_; 
v___x_144_ = 1;
return v___x_144_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = 0;
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLEWeight___boxed(lean_object* v_a_146_, lean_object* v_b_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l_Lean_Meta_Grind_Order_instDecidableLEWeight(v_a_146_, v_b_147_);
lean_dec_ref(v_b_147_);
lean_dec_ref(v_a_146_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLTWeight(lean_object* v_a_150_, lean_object* v_b_151_){
_start:
{
uint8_t v___x_152_; uint8_t v___x_153_; uint8_t v___x_154_; 
v___x_152_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_150_, v_b_151_);
v___x_153_ = 0;
v___x_154_ = l_instDecidableEqOrdering(v___x_152_, v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLTWeight___boxed(lean_object* v_a_155_, lean_object* v_b_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Lean_Meta_Grind_Order_instDecidableLTWeight(v_a_155_, v_b_156_);
lean_dec_ref(v_b_156_);
lean_dec_ref(v_a_155_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add(lean_object* v_a_159_, lean_object* v_b_160_){
_start:
{
lean_object* v_k_161_; uint8_t v_strict_162_; lean_object* v_k_163_; uint8_t v_strict_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_175_; 
v_k_161_ = lean_ctor_get(v_a_159_, 0);
v_strict_162_ = lean_ctor_get_uint8(v_a_159_, sizeof(void*)*1);
v_k_163_ = lean_ctor_get(v_b_160_, 0);
v_strict_164_ = lean_ctor_get_uint8(v_b_160_, sizeof(void*)*1);
v_isSharedCheck_175_ = !lean_is_exclusive(v_b_160_);
if (v_isSharedCheck_175_ == 0)
{
v___x_166_ = v_b_160_;
v_isShared_167_ = v_isSharedCheck_175_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_k_163_);
lean_dec(v_b_160_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_175_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; 
v___x_168_ = lean_int_add(v_k_161_, v_k_163_);
lean_dec(v_k_163_);
if (v_strict_162_ == 0)
{
lean_object* v___x_170_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_168_);
v___x_170_ = v___x_166_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
lean_ctor_set_uint8(v_reuseFailAlloc_171_, sizeof(void*)*1, v_strict_164_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
else
{
lean_object* v___x_173_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_168_);
v___x_173_ = v___x_166_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_ctor_set_uint8(v___x_173_, sizeof(void*)*1, v_strict_162_);
return v___x_173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add___boxed(lean_object* v_a_176_, lean_object* v_b_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Meta_Grind_Order_Weight_add(v_a_176_, v_b_177_);
lean_dec_ref(v_a_176_);
return v_res_178_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isNeg(lean_object* v_a_181_){
_start:
{
lean_object* v_k_182_; uint8_t v_strict_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v_k_182_ = lean_ctor_get(v_a_181_, 0);
v_strict_183_ = lean_ctor_get_uint8(v_a_181_, sizeof(void*)*1);
v___x_184_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0);
v___x_185_ = lean_int_dec_lt(v_k_182_, v___x_184_);
if (v___x_185_ == 0)
{
uint8_t v___x_186_; 
v___x_186_ = lean_int_dec_eq(v_k_182_, v___x_184_);
if (v___x_186_ == 0)
{
return v___x_186_;
}
else
{
return v_strict_183_;
}
}
else
{
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isNeg___boxed(lean_object* v_a_187_){
_start:
{
uint8_t v_res_188_; lean_object* v_r_189_; 
v_res_188_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v_a_187_);
lean_dec_ref(v_a_187_);
v_r_189_ = lean_box(v_res_188_);
return v_r_189_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isZero(lean_object* v_a_190_){
_start:
{
lean_object* v_k_191_; uint8_t v_strict_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_k_191_ = lean_ctor_get(v_a_190_, 0);
v_strict_192_ = lean_ctor_get_uint8(v_a_190_, sizeof(void*)*1);
v___x_193_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___redArg___closed__0);
v___x_194_ = lean_int_dec_eq(v_k_191_, v___x_193_);
if (v___x_194_ == 0)
{
return v___x_194_;
}
else
{
if (v_strict_192_ == 0)
{
return v___x_194_;
}
else
{
uint8_t v___x_195_; 
v___x_195_ = 0;
return v___x_195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isZero___boxed(lean_object* v_a_196_){
_start:
{
uint8_t v_res_197_; lean_object* v_r_198_; 
v_res_197_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_a_196_);
lean_dec_ref(v_a_196_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(lean_object* v_a_200_){
_start:
{
uint8_t v_strict_201_; 
v_strict_201_ = lean_ctor_get_uint8(v_a_200_, sizeof(void*)*1);
if (v_strict_201_ == 0)
{
lean_object* v_k_202_; lean_object* v___x_203_; 
v_k_202_ = lean_ctor_get(v_a_200_, 0);
v___x_203_ = l_Int_repr(v_k_202_);
return v___x_203_;
}
else
{
lean_object* v_k_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_k_204_ = lean_ctor_get(v_a_200_, 0);
v___x_205_ = l_Int_repr(v_k_204_);
v___x_206_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_207_ = lean_string_append(v___x_205_, v___x_206_);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed(lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(v_a_208_);
lean_dec_ref(v_a_208_);
return v_res_209_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__0));
v___x_214_ = l_Lean_stringToMessageData(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__2));
v___x_217_ = l_Lean_stringToMessageData(v___x_216_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__5(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__4));
v___x_220_ = l_Lean_stringToMessageData(v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__7(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__6));
v___x_223_ = l_Lean_stringToMessageData(v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg(lean_object* v_todo_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
switch(lean_obj_tag(v_todo_224_))
{
case 0:
{
lean_object* v_e_229_; lean_object* v_u_230_; lean_object* v_v_231_; lean_object* v_k_232_; lean_object* v_k_x27_233_; lean_object* v___x_234_; 
v_e_229_ = lean_ctor_get(v_todo_224_, 1);
lean_inc_ref(v_e_229_);
v_u_230_ = lean_ctor_get(v_todo_224_, 2);
lean_inc(v_u_230_);
v_v_231_ = lean_ctor_get(v_todo_224_, 3);
lean_inc(v_v_231_);
v_k_232_ = lean_ctor_get(v_todo_224_, 4);
lean_inc_ref(v_k_232_);
v_k_x27_233_ = lean_ctor_get(v_todo_224_, 5);
lean_inc_ref(v_k_x27_233_);
lean_dec_ref_known(v_todo_224_, 6);
v___x_234_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_230_, v_a_225_, v_a_226_, v_a_227_);
lean_dec(v_u_230_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_236_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref_known(v___x_234_, 1);
v___x_236_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_231_, v_a_225_, v_a_226_, v_a_227_);
lean_dec(v_v_231_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_279_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_279_ == 0)
{
v___x_239_ = v___x_236_;
v_isShared_240_ = v_isSharedCheck_279_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_279_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v_k_255_; uint8_t v_strict_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___y_264_; 
v___x_250_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__1, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__1);
v___x_251_ = l_Lean_MessageData_ofExpr(v_e_229_);
v___x_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3);
v___x_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v_k_255_ = lean_ctor_get(v_k_232_, 0);
lean_inc(v_k_255_);
v_strict_256_ = lean_ctor_get_uint8(v_k_232_, sizeof(void*)*1);
lean_dec_ref(v_k_232_);
v___x_257_ = l_Lean_MessageData_ofExpr(v_a_235_);
v___x_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_254_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___x_253_);
v___x_260_ = l_Lean_MessageData_ofExpr(v_a_237_);
v___x_261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_259_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_253_);
if (v_strict_256_ == 0)
{
lean_object* v___x_275_; 
v___x_275_ = l_Int_repr(v_k_255_);
lean_dec(v_k_255_);
v___y_264_ = v___x_275_;
goto v___jp_263_;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = l_Int_repr(v_k_255_);
lean_dec(v_k_255_);
v___x_277_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_278_ = lean_string_append(v___x_276_, v___x_277_);
v___y_264_ = v___x_278_;
goto v___jp_263_;
}
v___jp_241_:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_244_, 0, v___y_243_);
v___x_245_ = l_Lean_MessageData_ofFormat(v___x_244_);
v___x_246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_246_, 0, v___y_242_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v___x_246_);
v___x_248_ = v___x_239_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
v___jp_263_:
{
lean_object* v_k_265_; uint8_t v_strict_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_k_265_ = lean_ctor_get(v_k_x27_233_, 0);
lean_inc(v_k_265_);
v_strict_266_ = lean_ctor_get_uint8(v_k_x27_233_, sizeof(void*)*1);
lean_dec_ref(v_k_x27_233_);
v___x_267_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_267_, 0, v___y_264_);
v___x_268_ = l_Lean_MessageData_ofFormat(v___x_267_);
v___x_269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_262_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_253_);
if (v_strict_266_ == 0)
{
lean_object* v___x_271_; 
v___x_271_ = l_Int_repr(v_k_265_);
lean_dec(v_k_265_);
v___y_242_ = v___x_270_;
v___y_243_ = v___x_271_;
goto v___jp_241_;
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = l_Int_repr(v_k_265_);
lean_dec(v_k_265_);
v___x_273_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_274_ = lean_string_append(v___x_272_, v___x_273_);
v___y_242_ = v___x_270_;
v___y_243_ = v___x_274_;
goto v___jp_241_;
}
}
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_dec(v_a_235_);
lean_dec_ref(v_k_x27_233_);
lean_dec_ref(v_k_232_);
lean_dec_ref(v_e_229_);
v_a_280_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_236_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_236_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec_ref(v_k_x27_233_);
lean_dec_ref(v_k_232_);
lean_dec(v_v_231_);
lean_dec_ref(v_e_229_);
v_a_288_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_234_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_234_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
case 1:
{
lean_object* v_e_296_; lean_object* v_u_297_; lean_object* v_v_298_; lean_object* v_k_299_; lean_object* v_k_x27_300_; lean_object* v___x_301_; 
v_e_296_ = lean_ctor_get(v_todo_224_, 1);
lean_inc_ref(v_e_296_);
v_u_297_ = lean_ctor_get(v_todo_224_, 2);
lean_inc(v_u_297_);
v_v_298_ = lean_ctor_get(v_todo_224_, 3);
lean_inc(v_v_298_);
v_k_299_ = lean_ctor_get(v_todo_224_, 4);
lean_inc_ref(v_k_299_);
v_k_x27_300_ = lean_ctor_get(v_todo_224_, 5);
lean_inc_ref(v_k_x27_300_);
lean_dec_ref_known(v_todo_224_, 6);
v___x_301_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_297_, v_a_225_, v_a_226_, v_a_227_);
lean_dec(v_u_297_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_303_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_301_, 1);
v___x_303_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_298_, v_a_225_, v_a_226_, v_a_227_);
lean_dec(v_v_298_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_346_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_346_ == 0)
{
v___x_306_ = v___x_303_;
v_isShared_307_ = v_isSharedCheck_346_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_346_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v_k_322_; uint8_t v_strict_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___y_331_; 
v___x_317_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__5, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__5);
v___x_318_ = l_Lean_MessageData_ofExpr(v_e_296_);
v___x_319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3);
v___x_321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v_k_322_ = lean_ctor_get(v_k_299_, 0);
lean_inc(v_k_322_);
v_strict_323_ = lean_ctor_get_uint8(v_k_299_, sizeof(void*)*1);
lean_dec_ref(v_k_299_);
v___x_324_ = l_Lean_MessageData_ofExpr(v_a_302_);
v___x_325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_321_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_320_);
v___x_327_ = l_Lean_MessageData_ofExpr(v_a_304_);
v___x_328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_320_);
if (v_strict_323_ == 0)
{
lean_object* v___x_342_; 
v___x_342_ = l_Int_repr(v_k_322_);
lean_dec(v_k_322_);
v___y_331_ = v___x_342_;
goto v___jp_330_;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = l_Int_repr(v_k_322_);
lean_dec(v_k_322_);
v___x_344_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_345_ = lean_string_append(v___x_343_, v___x_344_);
v___y_331_ = v___x_345_;
goto v___jp_330_;
}
v___jp_308_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_311_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_311_, 0, v___y_310_);
v___x_312_ = l_Lean_MessageData_ofFormat(v___x_311_);
v___x_313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_313_, 0, v___y_309_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_313_);
v___x_315_ = v___x_306_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
v___jp_330_:
{
lean_object* v_k_332_; uint8_t v_strict_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_k_332_ = lean_ctor_get(v_k_x27_300_, 0);
lean_inc(v_k_332_);
v_strict_333_ = lean_ctor_get_uint8(v_k_x27_300_, sizeof(void*)*1);
lean_dec_ref(v_k_x27_300_);
v___x_334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_334_, 0, v___y_331_);
v___x_335_ = l_Lean_MessageData_ofFormat(v___x_334_);
v___x_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_329_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_320_);
if (v_strict_333_ == 0)
{
lean_object* v___x_338_; 
v___x_338_ = l_Int_repr(v_k_332_);
lean_dec(v_k_332_);
v___y_309_ = v___x_337_;
v___y_310_ = v___x_338_;
goto v___jp_308_;
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = l_Int_repr(v_k_332_);
lean_dec(v_k_332_);
v___x_340_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_341_ = lean_string_append(v___x_339_, v___x_340_);
v___y_309_ = v___x_337_;
v___y_310_ = v___x_341_;
goto v___jp_308_;
}
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_a_302_);
lean_dec_ref(v_k_x27_300_);
lean_dec_ref(v_k_299_);
lean_dec_ref(v_e_296_);
v_a_347_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_303_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_303_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec_ref(v_k_x27_300_);
lean_dec_ref(v_k_299_);
lean_dec(v_v_298_);
lean_dec_ref(v_e_296_);
v_a_355_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_301_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_301_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
default: 
{
lean_object* v_u_363_; lean_object* v_v_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_404_; 
v_u_363_ = lean_ctor_get(v_todo_224_, 0);
v_v_364_ = lean_ctor_get(v_todo_224_, 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v_todo_224_);
if (v_isSharedCheck_404_ == 0)
{
v___x_366_ = v_todo_224_;
v_isShared_367_ = v_isSharedCheck_404_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_v_364_);
lean_inc(v_u_363_);
lean_dec(v_todo_224_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_404_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_363_, v_a_225_, v_a_226_, v_a_227_);
lean_dec(v_u_363_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_370_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_368_, 1);
v___x_370_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_364_, v_a_225_, v_a_226_, v_a_227_);
lean_dec(v_v_364_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_387_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_387_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_387_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_387_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_375_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__7, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__7_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__7);
v___x_376_ = l_Lean_MessageData_ofExpr(v_a_369_);
if (v_isShared_367_ == 0)
{
lean_ctor_set_tag(v___x_366_, 7);
lean_ctor_set(v___x_366_, 1, v___x_376_);
lean_ctor_set(v___x_366_, 0, v___x_375_);
v___x_378_ = v___x_366_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v___x_376_);
v___x_378_ = v_reuseFailAlloc_386_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_379_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___closed__3);
v___x_380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = l_Lean_MessageData_ofExpr(v_a_371_);
v___x_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_382_);
v___x_384_ = v___x_373_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec(v_a_369_);
lean_del_object(v___x_366_);
v_a_388_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_370_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_370_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_del_object(v___x_366_);
lean_dec(v_v_364_);
v_a_396_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_368_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_368_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg___boxed(lean_object* v_todo_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg(v_todo_405_, v_a_406_, v_a_407_, v_a_408_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
lean_dec(v_a_406_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object* v_todo_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg(v_todo_411_, v_a_412_, v_a_413_, v_a_421_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___boxed(lean_object* v_todo_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Meta_Grind_Order_ToPropagate_pp(v_todo_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec(v_a_427_);
lean_dec(v_a_426_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(lean_object* v_c_439_){
_start:
{
uint8_t v_kind_440_; 
v_kind_440_ = lean_ctor_get_uint8(v_c_439_, sizeof(void*)*5);
if (v_kind_440_ == 0)
{
lean_object* v_k_441_; uint8_t v___x_442_; lean_object* v___x_443_; 
v_k_441_ = lean_ctor_get(v_c_439_, 2);
v___x_442_ = 0;
lean_inc(v_k_441_);
v___x_443_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_443_, 0, v_k_441_);
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*1, v___x_442_);
return v___x_443_;
}
else
{
lean_object* v_k_444_; uint8_t v___x_445_; lean_object* v___x_446_; 
v_k_444_ = lean_ctor_get(v_c_439_, 2);
v___x_445_ = 1;
lean_inc(v_k_444_);
v___x_446_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_446_, 0, v_k_444_);
lean_ctor_set_uint8(v___x_446_, sizeof(void*)*1, v___x_445_);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg___boxed(lean_object* v_c_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_447_);
lean_dec_ref(v_c_447_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight(lean_object* v_00_u03b1_449_, lean_object* v_c_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___boxed(lean_object* v_00_u03b1_452_, lean_object* v_c_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight(v_00_u03b1_452_, v_c_453_);
lean_dec_ref(v_c_453_);
return v_res_454_;
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
