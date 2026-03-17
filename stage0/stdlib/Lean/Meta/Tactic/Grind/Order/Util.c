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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
lean_object* lean_int_add(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0;
static const lean_string_object l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__1));
v___x_5_ = l_Lean_stringToMessageData(v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__3));
v___x_8_ = l_Lean_stringToMessageData(v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp(lean_object* v_c_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
uint8_t v_kind_25_; lean_object* v_u_26_; lean_object* v_v_27_; lean_object* v_k_28_; lean_object* v___x_29_; 
v_kind_25_ = lean_ctor_get_uint8(v_c_12_, sizeof(void*)*5);
v_u_26_ = lean_ctor_get(v_c_12_, 0);
v_v_27_ = lean_ctor_get(v_c_12_, 1);
v_k_28_ = lean_ctor_get(v_c_12_, 2);
v___x_29_ = l_Lean_Meta_Grind_Order_getExpr(v_u_26_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_94_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_94_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_94_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_94_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Meta_Grind_Order_getExpr(v_v_27_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_85_; 
v_a_35_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_85_ == 0)
{
v___x_37_ = v___x_34_;
v_isShared_38_ = v_isSharedCheck_85_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_34_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_85_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___y_40_; lean_object* v___y_41_; lean_object* v___y_49_; 
if (v_kind_25_ == 0)
{
lean_object* v___x_83_; 
v___x_83_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6));
v___y_49_ = v___x_83_;
goto v___jp_48_;
}
else
{
lean_object* v___x_84_; 
v___x_84_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__7));
v___y_49_ = v___x_84_;
goto v___jp_48_;
}
v___jp_39_:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_42_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_42_, 0, v___y_41_);
v___x_43_ = l_Lean_MessageData_ofFormat(v___x_42_);
v___x_44_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_44_, 0, v___y_40_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 0, v___x_44_);
v___x_46_ = v___x_37_;
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
v___jp_48_:
{
lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_50_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v___x_51_ = lean_int_dec_eq(v_k_28_, v___x_50_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v_isNeg_62_; 
lean_del_object(v___x_32_);
v___x_52_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_30_);
v___x_53_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2);
v___x_54_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
v___x_55_ = l_Lean_stringToMessageData(v___y_49_);
v___x_56_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_54_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_53_);
v___x_58_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_35_);
v___x_59_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_57_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
v___x_60_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4);
v___x_61_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_59_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v_isNeg_62_ = lean_int_dec_lt(v_k_28_, v___x_50_);
if (v_isNeg_62_ == 0)
{
lean_object* v_a_63_; lean_object* v___x_64_; 
v_a_63_ = lean_nat_abs(v_k_28_);
v___x_64_ = l_Nat_reprFast(v_a_63_);
v___y_40_ = v___x_61_;
v___y_41_ = v___x_64_;
goto v___jp_39_;
}
else
{
lean_object* v_abs_65_; lean_object* v_one_66_; lean_object* v_a_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_abs_65_ = lean_nat_abs(v_k_28_);
v_one_66_ = lean_unsigned_to_nat(1u);
v_a_67_ = lean_nat_sub(v_abs_65_, v_one_66_);
lean_dec(v_abs_65_);
v___x_68_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
v___x_69_ = lean_nat_add(v_a_67_, v_one_66_);
lean_dec(v_a_67_);
v___x_70_ = l_Nat_reprFast(v___x_69_);
v___x_71_ = lean_string_append(v___x_68_, v___x_70_);
lean_dec_ref(v___x_70_);
v___y_40_ = v___x_61_;
v___y_41_ = v___x_71_;
goto v___jp_39_;
}
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_81_; 
lean_del_object(v___x_37_);
v___x_72_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_30_);
v___x_73_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2);
v___x_74_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_72_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = l_Lean_stringToMessageData(v___y_49_);
v___x_76_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___x_73_);
v___x_78_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_35_);
v___x_79_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 0, v___x_79_);
v___x_81_ = v___x_32_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_79_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
}
else
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_93_; 
lean_del_object(v___x_32_);
lean_dec(v_a_30_);
v_a_86_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_93_ == 0)
{
v___x_88_ = v___x_34_;
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_34_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_91_; 
if (v_isShared_89_ == 0)
{
v___x_91_ = v___x_88_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_a_86_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
}
else
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
v_a_95_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v___x_29_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_29_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___boxed(lean_object* v_c_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec(v_a_105_);
lean_dec(v_a_104_);
lean_dec_ref(v_c_103_);
return v_res_116_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_compare(lean_object* v_a_117_, lean_object* v_b_118_){
_start:
{
lean_object* v_k_119_; uint8_t v_strict_120_; lean_object* v_k_121_; uint8_t v_strict_122_; uint8_t v___x_127_; 
v_k_119_ = lean_ctor_get(v_a_117_, 0);
v_strict_120_ = lean_ctor_get_uint8(v_a_117_, sizeof(void*)*1);
v_k_121_ = lean_ctor_get(v_b_118_, 0);
v_strict_122_ = lean_ctor_get_uint8(v_b_118_, sizeof(void*)*1);
v___x_127_ = lean_int_dec_lt(v_k_119_, v_k_121_);
if (v___x_127_ == 0)
{
uint8_t v___x_128_; 
v___x_128_ = lean_int_dec_lt(v_k_121_, v_k_119_);
if (v___x_128_ == 0)
{
if (v_strict_120_ == 0)
{
if (v_strict_122_ == 0)
{
uint8_t v___x_129_; 
v___x_129_ = 1;
return v___x_129_;
}
else
{
goto v___jp_123_;
}
}
else
{
if (v_strict_122_ == 0)
{
goto v___jp_123_;
}
else
{
uint8_t v___x_130_; 
v___x_130_ = 1;
return v___x_130_;
}
}
}
else
{
uint8_t v___x_131_; 
v___x_131_ = 2;
return v___x_131_;
}
}
else
{
uint8_t v___x_132_; 
v___x_132_ = 0;
return v___x_132_;
}
v___jp_123_:
{
if (v_strict_120_ == 0)
{
uint8_t v___x_124_; 
v___x_124_ = 2;
return v___x_124_;
}
else
{
if (v_strict_122_ == 0)
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = 2;
return v___x_126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_compare___boxed(lean_object* v_a_133_, lean_object* v_b_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_133_, v_b_134_);
lean_dec_ref(v_b_134_);
lean_dec_ref(v_a_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instLEWeight(void){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_box(0);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instLTWeight(void){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_box(0);
return v___x_140_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLEWeight(lean_object* v_a_141_, lean_object* v_b_142_){
_start:
{
uint8_t v___x_143_; uint8_t v___x_144_; uint8_t v___x_145_; 
v___x_143_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_141_, v_b_142_);
v___x_144_ = 2;
v___x_145_ = l_instDecidableEqOrdering(v___x_143_, v___x_144_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLEWeight___boxed(lean_object* v_a_148_, lean_object* v_b_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_Lean_Meta_Grind_Order_instDecidableLEWeight(v_a_148_, v_b_149_);
lean_dec_ref(v_b_149_);
lean_dec_ref(v_a_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLTWeight(lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
uint8_t v___x_154_; uint8_t v___x_155_; uint8_t v___x_156_; 
v___x_154_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_152_, v_b_153_);
v___x_155_ = 0;
v___x_156_ = l_instDecidableEqOrdering(v___x_154_, v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLTWeight___boxed(lean_object* v_a_157_, lean_object* v_b_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_Lean_Meta_Grind_Order_instDecidableLTWeight(v_a_157_, v_b_158_);
lean_dec_ref(v_b_158_);
lean_dec_ref(v_a_157_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add(lean_object* v_a_161_, lean_object* v_b_162_){
_start:
{
lean_object* v_k_163_; uint8_t v_strict_164_; lean_object* v_k_165_; uint8_t v_strict_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_177_; 
v_k_163_ = lean_ctor_get(v_a_161_, 0);
v_strict_164_ = lean_ctor_get_uint8(v_a_161_, sizeof(void*)*1);
v_k_165_ = lean_ctor_get(v_b_162_, 0);
v_strict_166_ = lean_ctor_get_uint8(v_b_162_, sizeof(void*)*1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_b_162_);
if (v_isSharedCheck_177_ == 0)
{
v___x_168_ = v_b_162_;
v_isShared_169_ = v_isSharedCheck_177_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_k_165_);
lean_dec(v_b_162_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_177_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; 
v___x_170_ = lean_int_add(v_k_163_, v_k_165_);
lean_dec(v_k_165_);
if (v_strict_164_ == 0)
{
lean_object* v___x_172_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_170_);
v___x_172_ = v___x_168_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
lean_ctor_set_uint8(v_reuseFailAlloc_173_, sizeof(void*)*1, v_strict_166_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
else
{
lean_object* v___x_175_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_170_);
v___x_175_ = v___x_168_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*1, v_strict_164_);
return v___x_175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add___boxed(lean_object* v_a_178_, lean_object* v_b_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Meta_Grind_Order_Weight_add(v_a_178_, v_b_179_);
lean_dec_ref(v_a_178_);
return v_res_180_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isNeg(lean_object* v_a_183_){
_start:
{
lean_object* v_k_184_; uint8_t v_strict_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v_k_184_ = lean_ctor_get(v_a_183_, 0);
v_strict_185_ = lean_ctor_get_uint8(v_a_183_, sizeof(void*)*1);
v___x_186_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v___x_187_ = lean_int_dec_lt(v_k_184_, v___x_186_);
if (v___x_187_ == 0)
{
uint8_t v___x_188_; 
v___x_188_ = lean_int_dec_eq(v_k_184_, v___x_186_);
if (v___x_188_ == 0)
{
return v___x_188_;
}
else
{
return v_strict_185_;
}
}
else
{
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isNeg___boxed(lean_object* v_a_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v_a_189_);
lean_dec_ref(v_a_189_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isZero(lean_object* v_a_192_){
_start:
{
lean_object* v_k_193_; uint8_t v_strict_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_k_193_ = lean_ctor_get(v_a_192_, 0);
v_strict_194_ = lean_ctor_get_uint8(v_a_192_, sizeof(void*)*1);
v___x_195_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v___x_196_ = lean_int_dec_eq(v_k_193_, v___x_195_);
if (v___x_196_ == 0)
{
return v___x_196_;
}
else
{
if (v_strict_194_ == 0)
{
return v___x_196_;
}
else
{
uint8_t v___x_197_; 
v___x_197_ = 0;
return v___x_197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isZero___boxed(lean_object* v_a_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_a_198_);
lean_dec_ref(v_a_198_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(lean_object* v_a_202_){
_start:
{
lean_object* v___y_204_; uint8_t v_strict_207_; 
v_strict_207_ = lean_ctor_get_uint8(v_a_202_, sizeof(void*)*1);
if (v_strict_207_ == 0)
{
lean_object* v_k_208_; lean_object* v_intZero_209_; uint8_t v_isNeg_210_; 
v_k_208_ = lean_ctor_get(v_a_202_, 0);
v_intZero_209_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v_isNeg_210_ = lean_int_dec_lt(v_k_208_, v_intZero_209_);
if (v_isNeg_210_ == 0)
{
lean_object* v_a_211_; lean_object* v___x_212_; 
v_a_211_ = lean_nat_abs(v_k_208_);
v___x_212_ = l_Nat_reprFast(v_a_211_);
return v___x_212_;
}
else
{
lean_object* v_abs_213_; lean_object* v_one_214_; lean_object* v_a_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_abs_213_ = lean_nat_abs(v_k_208_);
v_one_214_ = lean_unsigned_to_nat(1u);
v_a_215_ = lean_nat_sub(v_abs_213_, v_one_214_);
lean_dec(v_abs_213_);
v___x_216_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
v___x_217_ = lean_nat_add(v_a_215_, v_one_214_);
lean_dec(v_a_215_);
v___x_218_ = l_Nat_reprFast(v___x_217_);
v___x_219_ = lean_string_append(v___x_216_, v___x_218_);
lean_dec_ref(v___x_218_);
return v___x_219_;
}
}
else
{
lean_object* v_k_220_; lean_object* v_intZero_221_; uint8_t v_isNeg_222_; 
v_k_220_ = lean_ctor_get(v_a_202_, 0);
v_intZero_221_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v_isNeg_222_ = lean_int_dec_lt(v_k_220_, v_intZero_221_);
if (v_isNeg_222_ == 0)
{
lean_object* v_a_223_; lean_object* v___x_224_; 
v_a_223_ = lean_nat_abs(v_k_220_);
v___x_224_ = l_Nat_reprFast(v_a_223_);
v___y_204_ = v___x_224_;
goto v___jp_203_;
}
else
{
lean_object* v_abs_225_; lean_object* v_one_226_; lean_object* v_a_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_abs_225_ = lean_nat_abs(v_k_220_);
v_one_226_ = lean_unsigned_to_nat(1u);
v_a_227_ = lean_nat_sub(v_abs_225_, v_one_226_);
lean_dec(v_abs_225_);
v___x_228_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
v___x_229_ = lean_nat_add(v_a_227_, v_one_226_);
lean_dec(v_a_227_);
v___x_230_ = l_Nat_reprFast(v___x_229_);
v___x_231_ = lean_string_append(v___x_228_, v___x_230_);
lean_dec_ref(v___x_230_);
v___y_204_ = v___x_231_;
goto v___jp_203_;
}
}
v___jp_203_:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_206_ = lean_string_append(v___y_204_, v___x_205_);
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed(lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(v_a_232_);
lean_dec_ref(v_a_232_);
return v_res_233_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__0));
v___x_238_ = l_Lean_stringToMessageData(v___x_237_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__2));
v___x_241_ = l_Lean_stringToMessageData(v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__4));
v___x_244_ = l_Lean_stringToMessageData(v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__6));
v___x_247_ = l_Lean_stringToMessageData(v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object* v_todo_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
switch(lean_obj_tag(v_todo_248_))
{
case 0:
{
lean_object* v_e_261_; lean_object* v_u_262_; lean_object* v_v_263_; lean_object* v_k_264_; lean_object* v_k_x27_265_; lean_object* v___x_266_; 
v_e_261_ = lean_ctor_get(v_todo_248_, 1);
lean_inc_ref(v_e_261_);
v_u_262_ = lean_ctor_get(v_todo_248_, 2);
lean_inc(v_u_262_);
v_v_263_ = lean_ctor_get(v_todo_248_, 3);
lean_inc(v_v_263_);
v_k_264_ = lean_ctor_get(v_todo_248_, 4);
lean_inc_ref(v_k_264_);
v_k_x27_265_ = lean_ctor_get(v_todo_248_, 5);
lean_inc_ref(v_k_x27_265_);
lean_dec_ref(v_todo_248_);
v___x_266_ = l_Lean_Meta_Grind_Order_getExpr(v_u_262_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
lean_dec(v_u_262_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_268_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_267_);
lean_dec_ref(v___x_266_);
v___x_268_ = l_Lean_Meta_Grind_Order_getExpr(v_v_263_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
lean_dec(v_v_263_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_356_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_356_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_356_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_356_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v_k_292_; uint8_t v_strict_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___y_301_; lean_object* v___y_331_; 
v___x_287_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1);
v___x_288_ = l_Lean_MessageData_ofExpr(v_e_261_);
v___x_289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
v___x_291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v_k_292_ = lean_ctor_get(v_k_264_, 0);
lean_inc(v_k_292_);
v_strict_293_ = lean_ctor_get_uint8(v_k_264_, sizeof(void*)*1);
lean_dec_ref(v_k_264_);
v___x_294_ = l_Lean_MessageData_ofExpr(v_a_267_);
v___x_295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_291_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___x_290_);
v___x_297_ = l_Lean_MessageData_ofExpr(v_a_269_);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_290_);
if (v_strict_293_ == 0)
{
lean_object* v_intZero_334_; uint8_t v_isNeg_335_; 
v_intZero_334_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v_isNeg_335_ = lean_int_dec_lt(v_k_292_, v_intZero_334_);
if (v_isNeg_335_ == 0)
{
lean_object* v_a_336_; lean_object* v___x_337_; 
v_a_336_ = lean_nat_abs(v_k_292_);
lean_dec(v_k_292_);
v___x_337_ = l_Nat_reprFast(v_a_336_);
v___y_301_ = v___x_337_;
goto v___jp_300_;
}
else
{
lean_object* v_abs_338_; lean_object* v_one_339_; lean_object* v_a_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_abs_338_ = lean_nat_abs(v_k_292_);
lean_dec(v_k_292_);
v_one_339_ = lean_unsigned_to_nat(1u);
v_a_340_ = lean_nat_sub(v_abs_338_, v_one_339_);
lean_dec(v_abs_338_);
v___x_341_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
v___x_342_ = lean_nat_add(v_a_340_, v_one_339_);
lean_dec(v_a_340_);
v___x_343_ = l_Nat_reprFast(v___x_342_);
v___x_344_ = lean_string_append(v___x_341_, v___x_343_);
lean_dec_ref(v___x_343_);
v___y_301_ = v___x_344_;
goto v___jp_300_;
}
}
else
{
lean_object* v_intZero_345_; uint8_t v_isNeg_346_; 
v_intZero_345_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v_isNeg_346_ = lean_int_dec_lt(v_k_292_, v_intZero_345_);
if (v_isNeg_346_ == 0)
{
lean_object* v_a_347_; lean_object* v___x_348_; 
v_a_347_ = lean_nat_abs(v_k_292_);
lean_dec(v_k_292_);
v___x_348_ = l_Nat_reprFast(v_a_347_);
v___y_331_ = v___x_348_;
goto v___jp_330_;
}
else
{
lean_object* v_abs_349_; lean_object* v_one_350_; lean_object* v_a_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_abs_349_ = lean_nat_abs(v_k_292_);
lean_dec(v_k_292_);
v_one_350_ = lean_unsigned_to_nat(1u);
v_a_351_ = lean_nat_sub(v_abs_349_, v_one_350_);
lean_dec(v_abs_349_);
v___x_352_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
v___x_353_ = lean_nat_add(v_a_351_, v_one_350_);
lean_dec(v_a_351_);
v___x_354_ = l_Nat_reprFast(v___x_353_);
v___x_355_ = lean_string_append(v___x_352_, v___x_354_);
lean_dec_ref(v___x_354_);
v___y_331_ = v___x_355_;
goto v___jp_330_;
}
}
v___jp_273_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_276_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_276_, 0, v___y_275_);
v___x_277_ = l_Lean_MessageData_ofFormat(v___x_276_);
v___x_278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_278_, 0, v___y_274_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_278_);
v___x_280_ = v___x_271_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
v___jp_282_:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_286_ = lean_string_append(v___y_284_, v___x_285_);
v___y_274_ = v___y_283_;
v___y_275_ = v___x_286_;
goto v___jp_273_;
}
v___jp_300_:
{
lean_object* v_k_302_; uint8_t v_strict_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_k_302_ = lean_ctor_get(v_k_x27_265_, 0);
lean_inc(v_k_302_);
v_strict_303_ = lean_ctor_get_uint8(v_k_x27_265_, sizeof(void*)*1);
lean_dec_ref(v_k_x27_265_);
v___x_304_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_304_, 0, v___y_301_);
v___x_305_ = l_Lean_MessageData_ofFormat(v___x_304_);
v___x_306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_299_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v___x_290_);
if (v_strict_303_ == 0)
{
lean_object* v_intZero_308_; uint8_t v_isNeg_309_; 
v_intZero_308_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v_isNeg_309_ = lean_int_dec_lt(v_k_302_, v_intZero_308_);
if (v_isNeg_309_ == 0)
{
lean_object* v_a_310_; lean_object* v___x_311_; 
v_a_310_ = lean_nat_abs(v_k_302_);
lean_dec(v_k_302_);
v___x_311_ = l_Nat_reprFast(v_a_310_);
v___y_274_ = v___x_307_;
v___y_275_ = v___x_311_;
goto v___jp_273_;
}
else
{
lean_object* v_abs_312_; lean_object* v_one_313_; lean_object* v_a_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_abs_312_ = lean_nat_abs(v_k_302_);
lean_dec(v_k_302_);
v_one_313_ = lean_unsigned_to_nat(1u);
v_a_314_ = lean_nat_sub(v_abs_312_, v_one_313_);
lean_dec(v_abs_312_);
v___x_315_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
v___x_316_ = lean_nat_add(v_a_314_, v_one_313_);
lean_dec(v_a_314_);
v___x_317_ = l_Nat_reprFast(v___x_316_);
v___x_318_ = lean_string_append(v___x_315_, v___x_317_);
lean_dec_ref(v___x_317_);
v___y_274_ = v___x_307_;
v___y_275_ = v___x_318_;
goto v___jp_273_;
}
}
else
{
lean_object* v_intZero_319_; uint8_t v_isNeg_320_; 
v_intZero_319_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v_isNeg_320_ = lean_int_dec_lt(v_k_302_, v_intZero_319_);
if (v_isNeg_320_ == 0)
{
lean_object* v_a_321_; lean_object* v___x_322_; 
v_a_321_ = lean_nat_abs(v_k_302_);
lean_dec(v_k_302_);
v___x_322_ = l_Nat_reprFast(v_a_321_);
v___y_283_ = v___x_307_;
v___y_284_ = v___x_322_;
goto v___jp_282_;
}
else
{
lean_object* v_abs_323_; lean_object* v_one_324_; lean_object* v_a_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_abs_323_ = lean_nat_abs(v_k_302_);
lean_dec(v_k_302_);
v_one_324_ = lean_unsigned_to_nat(1u);
v_a_325_ = lean_nat_sub(v_abs_323_, v_one_324_);
lean_dec(v_abs_323_);
v___x_326_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
v___x_327_ = lean_nat_add(v_a_325_, v_one_324_);
lean_dec(v_a_325_);
v___x_328_ = l_Nat_reprFast(v___x_327_);
v___x_329_ = lean_string_append(v___x_326_, v___x_328_);
lean_dec_ref(v___x_328_);
v___y_283_ = v___x_307_;
v___y_284_ = v___x_329_;
goto v___jp_282_;
}
}
}
v___jp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_333_ = lean_string_append(v___y_331_, v___x_332_);
v___y_301_ = v___x_333_;
goto v___jp_300_;
}
}
}
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec(v_a_267_);
lean_dec_ref(v_k_x27_265_);
lean_dec_ref(v_k_264_);
lean_dec_ref(v_e_261_);
v_a_357_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_268_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_268_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
lean_dec_ref(v_k_x27_265_);
lean_dec_ref(v_k_264_);
lean_dec(v_v_263_);
lean_dec_ref(v_e_261_);
v_a_365_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_266_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_266_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
case 1:
{
lean_object* v_e_373_; lean_object* v_u_374_; lean_object* v_v_375_; lean_object* v_k_376_; lean_object* v_k_x27_377_; lean_object* v___x_378_; 
v_e_373_ = lean_ctor_get(v_todo_248_, 1);
lean_inc_ref(v_e_373_);
v_u_374_ = lean_ctor_get(v_todo_248_, 2);
lean_inc(v_u_374_);
v_v_375_ = lean_ctor_get(v_todo_248_, 3);
lean_inc(v_v_375_);
v_k_376_ = lean_ctor_get(v_todo_248_, 4);
lean_inc_ref(v_k_376_);
v_k_x27_377_ = lean_ctor_get(v_todo_248_, 5);
lean_inc_ref(v_k_x27_377_);
lean_dec_ref(v_todo_248_);
v___x_378_ = l_Lean_Meta_Grind_Order_getExpr(v_u_374_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
lean_dec(v_u_374_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_380_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref(v___x_378_);
v___x_380_ = l_Lean_Meta_Grind_Order_getExpr(v_v_375_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
lean_dec(v_v_375_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_468_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_468_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_468_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_468_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v_k_404_; uint8_t v_strict_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___y_413_; lean_object* v___y_443_; 
v___x_399_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5);
v___x_400_ = l_Lean_MessageData_ofExpr(v_e_373_);
v___x_401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
v___x_403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v_k_404_ = lean_ctor_get(v_k_376_, 0);
lean_inc(v_k_404_);
v_strict_405_ = lean_ctor_get_uint8(v_k_376_, sizeof(void*)*1);
lean_dec_ref(v_k_376_);
v___x_406_ = l_Lean_MessageData_ofExpr(v_a_379_);
v___x_407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_403_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_402_);
v___x_409_ = l_Lean_MessageData_ofExpr(v_a_381_);
v___x_410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v___x_402_);
if (v_strict_405_ == 0)
{
lean_object* v_intZero_446_; uint8_t v_isNeg_447_; 
v_intZero_446_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v_isNeg_447_ = lean_int_dec_lt(v_k_404_, v_intZero_446_);
if (v_isNeg_447_ == 0)
{
lean_object* v_a_448_; lean_object* v___x_449_; 
v_a_448_ = lean_nat_abs(v_k_404_);
lean_dec(v_k_404_);
v___x_449_ = l_Nat_reprFast(v_a_448_);
v___y_413_ = v___x_449_;
goto v___jp_412_;
}
else
{
lean_object* v_abs_450_; lean_object* v_one_451_; lean_object* v_a_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v_abs_450_ = lean_nat_abs(v_k_404_);
lean_dec(v_k_404_);
v_one_451_ = lean_unsigned_to_nat(1u);
v_a_452_ = lean_nat_sub(v_abs_450_, v_one_451_);
lean_dec(v_abs_450_);
v___x_453_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
v___x_454_ = lean_nat_add(v_a_452_, v_one_451_);
lean_dec(v_a_452_);
v___x_455_ = l_Nat_reprFast(v___x_454_);
v___x_456_ = lean_string_append(v___x_453_, v___x_455_);
lean_dec_ref(v___x_455_);
v___y_413_ = v___x_456_;
goto v___jp_412_;
}
}
else
{
lean_object* v_intZero_457_; uint8_t v_isNeg_458_; 
v_intZero_457_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v_isNeg_458_ = lean_int_dec_lt(v_k_404_, v_intZero_457_);
if (v_isNeg_458_ == 0)
{
lean_object* v_a_459_; lean_object* v___x_460_; 
v_a_459_ = lean_nat_abs(v_k_404_);
lean_dec(v_k_404_);
v___x_460_ = l_Nat_reprFast(v_a_459_);
v___y_443_ = v___x_460_;
goto v___jp_442_;
}
else
{
lean_object* v_abs_461_; lean_object* v_one_462_; lean_object* v_a_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_abs_461_ = lean_nat_abs(v_k_404_);
lean_dec(v_k_404_);
v_one_462_ = lean_unsigned_to_nat(1u);
v_a_463_ = lean_nat_sub(v_abs_461_, v_one_462_);
lean_dec(v_abs_461_);
v___x_464_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
v___x_465_ = lean_nat_add(v_a_463_, v_one_462_);
lean_dec(v_a_463_);
v___x_466_ = l_Nat_reprFast(v___x_465_);
v___x_467_ = lean_string_append(v___x_464_, v___x_466_);
lean_dec_ref(v___x_466_);
v___y_443_ = v___x_467_;
goto v___jp_442_;
}
}
v___jp_385_:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_388_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_388_, 0, v___y_387_);
v___x_389_ = l_Lean_MessageData_ofFormat(v___x_388_);
v___x_390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_390_, 0, v___y_386_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_390_);
v___x_392_ = v___x_383_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
v___jp_394_:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_398_ = lean_string_append(v___y_396_, v___x_397_);
v___y_386_ = v___y_395_;
v___y_387_ = v___x_398_;
goto v___jp_385_;
}
v___jp_412_:
{
lean_object* v_k_414_; uint8_t v_strict_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_k_414_ = lean_ctor_get(v_k_x27_377_, 0);
lean_inc(v_k_414_);
v_strict_415_ = lean_ctor_get_uint8(v_k_x27_377_, sizeof(void*)*1);
lean_dec_ref(v_k_x27_377_);
v___x_416_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_416_, 0, v___y_413_);
v___x_417_ = l_Lean_MessageData_ofFormat(v___x_416_);
v___x_418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_411_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v___x_419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v___x_402_);
if (v_strict_415_ == 0)
{
lean_object* v_intZero_420_; uint8_t v_isNeg_421_; 
v_intZero_420_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v_isNeg_421_ = lean_int_dec_lt(v_k_414_, v_intZero_420_);
if (v_isNeg_421_ == 0)
{
lean_object* v_a_422_; lean_object* v___x_423_; 
v_a_422_ = lean_nat_abs(v_k_414_);
lean_dec(v_k_414_);
v___x_423_ = l_Nat_reprFast(v_a_422_);
v___y_386_ = v___x_419_;
v___y_387_ = v___x_423_;
goto v___jp_385_;
}
else
{
lean_object* v_abs_424_; lean_object* v_one_425_; lean_object* v_a_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_abs_424_ = lean_nat_abs(v_k_414_);
lean_dec(v_k_414_);
v_one_425_ = lean_unsigned_to_nat(1u);
v_a_426_ = lean_nat_sub(v_abs_424_, v_one_425_);
lean_dec(v_abs_424_);
v___x_427_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
v___x_428_ = lean_nat_add(v_a_426_, v_one_425_);
lean_dec(v_a_426_);
v___x_429_ = l_Nat_reprFast(v___x_428_);
v___x_430_ = lean_string_append(v___x_427_, v___x_429_);
lean_dec_ref(v___x_429_);
v___y_386_ = v___x_419_;
v___y_387_ = v___x_430_;
goto v___jp_385_;
}
}
else
{
lean_object* v_intZero_431_; uint8_t v_isNeg_432_; 
v_intZero_431_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v_isNeg_432_ = lean_int_dec_lt(v_k_414_, v_intZero_431_);
if (v_isNeg_432_ == 0)
{
lean_object* v_a_433_; lean_object* v___x_434_; 
v_a_433_ = lean_nat_abs(v_k_414_);
lean_dec(v_k_414_);
v___x_434_ = l_Nat_reprFast(v_a_433_);
v___y_395_ = v___x_419_;
v___y_396_ = v___x_434_;
goto v___jp_394_;
}
else
{
lean_object* v_abs_435_; lean_object* v_one_436_; lean_object* v_a_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v_abs_435_ = lean_nat_abs(v_k_414_);
lean_dec(v_k_414_);
v_one_436_ = lean_unsigned_to_nat(1u);
v_a_437_ = lean_nat_sub(v_abs_435_, v_one_436_);
lean_dec(v_abs_435_);
v___x_438_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
v___x_439_ = lean_nat_add(v_a_437_, v_one_436_);
lean_dec(v_a_437_);
v___x_440_ = l_Nat_reprFast(v___x_439_);
v___x_441_ = lean_string_append(v___x_438_, v___x_440_);
lean_dec_ref(v___x_440_);
v___y_395_ = v___x_419_;
v___y_396_ = v___x_441_;
goto v___jp_394_;
}
}
}
v___jp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_445_ = lean_string_append(v___y_443_, v___x_444_);
v___y_413_ = v___x_445_;
goto v___jp_412_;
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec(v_a_379_);
lean_dec_ref(v_k_x27_377_);
lean_dec_ref(v_k_376_);
lean_dec_ref(v_e_373_);
v_a_469_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_380_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_380_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
lean_dec_ref(v_k_x27_377_);
lean_dec_ref(v_k_376_);
lean_dec(v_v_375_);
lean_dec_ref(v_e_373_);
v_a_477_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_378_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_378_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
default: 
{
lean_object* v_u_485_; lean_object* v_v_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_526_; 
v_u_485_ = lean_ctor_get(v_todo_248_, 0);
v_v_486_ = lean_ctor_get(v_todo_248_, 1);
v_isSharedCheck_526_ = !lean_is_exclusive(v_todo_248_);
if (v_isSharedCheck_526_ == 0)
{
v___x_488_ = v_todo_248_;
v_isShared_489_ = v_isSharedCheck_526_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_v_486_);
lean_inc(v_u_485_);
lean_dec(v_todo_248_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_526_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Meta_Grind_Order_getExpr(v_u_485_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
lean_dec(v_u_485_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_492_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref(v___x_490_);
v___x_492_ = l_Lean_Meta_Grind_Order_getExpr(v_v_486_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
lean_dec(v_v_486_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_509_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_509_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_509_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_509_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_497_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7);
v___x_498_ = l_Lean_MessageData_ofExpr(v_a_491_);
if (v_isShared_489_ == 0)
{
lean_ctor_set_tag(v___x_488_, 7);
lean_ctor_set(v___x_488_, 1, v___x_498_);
lean_ctor_set(v___x_488_, 0, v___x_497_);
v___x_500_ = v___x_488_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v___x_498_);
v___x_500_ = v_reuseFailAlloc_508_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_501_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
v___x_502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = l_Lean_MessageData_ofExpr(v_a_493_);
v___x_504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_502_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_504_);
v___x_506_ = v___x_495_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec(v_a_491_);
lean_del_object(v___x_488_);
v_a_510_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_492_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_492_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_del_object(v___x_488_);
lean_dec(v_v_486_);
v_a_518_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_490_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_490_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___boxed(lean_object* v_todo_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Meta_Grind_Order_ToPropagate_pp(v_todo_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec(v_a_529_);
lean_dec(v_a_528_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(lean_object* v_c_541_){
_start:
{
uint8_t v_kind_542_; 
v_kind_542_ = lean_ctor_get_uint8(v_c_541_, sizeof(void*)*5);
if (v_kind_542_ == 0)
{
lean_object* v_k_543_; uint8_t v___x_544_; lean_object* v___x_545_; 
v_k_543_ = lean_ctor_get(v_c_541_, 2);
v___x_544_ = 0;
lean_inc(v_k_543_);
v___x_545_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_545_, 0, v_k_543_);
lean_ctor_set_uint8(v___x_545_, sizeof(void*)*1, v___x_544_);
return v___x_545_;
}
else
{
lean_object* v_k_546_; uint8_t v___x_547_; lean_object* v___x_548_; 
v_k_546_ = lean_ctor_get(v_c_541_, 2);
v___x_547_ = 1;
lean_inc(v_k_546_);
v___x_548_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_548_, 0, v_k_546_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*1, v___x_547_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg___boxed(lean_object* v_c_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_549_);
lean_dec_ref(v_c_549_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight(lean_object* v_00_u03b1_551_, lean_object* v_c_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___boxed(lean_object* v_00_u03b1_554_, lean_object* v_c_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight(v_00_u03b1_554_, v_c_555_);
lean_dec_ref(v_c_555_);
return v_res_556_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
