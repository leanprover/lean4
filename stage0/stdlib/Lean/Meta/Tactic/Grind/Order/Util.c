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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≤"};
static const lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp(lean_object* v_c_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
uint8_t v_kind_24_; lean_object* v_u_25_; lean_object* v_v_26_; lean_object* v_k_27_; lean_object* v___x_28_; 
v_kind_24_ = lean_ctor_get_uint8(v_c_11_, sizeof(void*)*5);
v_u_25_ = lean_ctor_get(v_c_11_, 0);
v_v_26_ = lean_ctor_get(v_c_11_, 1);
v_k_27_ = lean_ctor_get(v_c_11_, 2);
v___x_28_ = l_Lean_Meta_Grind_Order_getExpr(v_u_25_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v___x_30_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
lean_inc(v_a_29_);
lean_dec_ref_known(v___x_28_, 1);
v___x_30_ = l_Lean_Meta_Grind_Order_getExpr(v_v_26_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_70_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_70_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_70_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_70_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___y_36_; 
if (v_kind_24_ == 0)
{
lean_object* v___x_68_; 
v___x_68_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
v___y_36_ = v___x_68_;
goto v___jp_35_;
}
else
{
lean_object* v___x_69_; 
v___x_69_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6));
v___y_36_ = v___x_69_;
goto v___jp_35_;
}
v___jp_35_:
{
lean_object* v___x_37_; uint8_t v___x_38_; uint8_t v___x_39_; 
v___x_37_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v___x_38_ = lean_int_dec_eq(v_k_27_, v___x_37_);
v___x_39_ = lean_bool_not(v___x_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_49_; 
v___x_40_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_29_);
v___x_41_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2);
v___x_42_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_40_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
lean_inc_ref(v___y_36_);
v___x_43_ = l_Lean_stringToMessageData(v___y_36_);
v___x_44_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_42_);
lean_ctor_set(v___x_44_, 1, v___x_43_);
v___x_45_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_41_);
v___x_46_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_31_);
v___x_47_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_45_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 0, v___x_47_);
v___x_49_ = v___x_33_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_47_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_51_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_29_);
v___x_52_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2);
v___x_53_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_51_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
lean_inc_ref(v___y_36_);
v___x_54_ = l_Lean_stringToMessageData(v___y_36_);
v___x_55_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_53_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v___x_56_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_52_);
v___x_57_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_31_);
v___x_58_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4);
v___x_60_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = l_Int_repr(v_k_27_);
v___x_62_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
v___x_63_ = l_Lean_MessageData_ofFormat(v___x_62_);
v___x_64_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_60_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 0, v___x_64_);
v___x_66_ = v___x_33_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_64_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
else
{
lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_78_; 
lean_dec(v_a_29_);
v_a_71_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_78_ == 0)
{
v___x_73_ = v___x_30_;
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_a_71_);
lean_dec(v___x_30_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_76_; 
if (v_isShared_74_ == 0)
{
v___x_76_ = v___x_73_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_a_71_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
else
{
lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
v_a_79_ = lean_ctor_get(v___x_28_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v___x_28_;
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_dec(v___x_28_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_a_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___boxed(lean_object* v_c_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_c_87_);
return v_res_100_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_compare(lean_object* v_a_101_, lean_object* v_b_102_){
_start:
{
lean_object* v_k_103_; uint8_t v_strict_104_; lean_object* v_k_105_; uint8_t v_strict_106_; uint8_t v___x_112_; 
v_k_103_ = lean_ctor_get(v_a_101_, 0);
v_strict_104_ = lean_ctor_get_uint8(v_a_101_, sizeof(void*)*1);
v_k_105_ = lean_ctor_get(v_b_102_, 0);
v_strict_106_ = lean_ctor_get_uint8(v_b_102_, sizeof(void*)*1);
v___x_112_ = lean_int_dec_lt(v_k_103_, v_k_105_);
if (v___x_112_ == 0)
{
uint8_t v___x_113_; 
v___x_113_ = lean_int_dec_lt(v_k_105_, v_k_103_);
if (v___x_113_ == 0)
{
if (v_strict_104_ == 0)
{
if (v_strict_106_ == 0)
{
uint8_t v___x_114_; 
v___x_114_ = 1;
return v___x_114_;
}
else
{
goto v___jp_107_;
}
}
else
{
if (v_strict_106_ == 0)
{
goto v___jp_107_;
}
else
{
uint8_t v___x_115_; 
v___x_115_ = 1;
return v___x_115_;
}
}
}
else
{
uint8_t v___x_116_; 
v___x_116_ = 2;
return v___x_116_;
}
}
else
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
v___jp_107_:
{
if (v_strict_104_ == 0)
{
uint8_t v___x_108_; 
v___x_108_ = 2;
return v___x_108_;
}
else
{
uint8_t v___x_109_; 
v___x_109_ = lean_bool_not(v_strict_106_);
if (v___x_109_ == 0)
{
uint8_t v___x_110_; 
v___x_110_ = 2;
return v___x_110_;
}
else
{
uint8_t v___x_111_; 
v___x_111_ = 0;
return v___x_111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_compare___boxed(lean_object* v_a_118_, lean_object* v_b_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_118_, v_b_119_);
lean_dec_ref(v_b_119_);
lean_dec_ref(v_a_118_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instLEWeight(void){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_box(0);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instLTWeight(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_box(0);
return v___x_125_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLEWeight(lean_object* v_a_126_, lean_object* v_b_127_){
_start:
{
uint8_t v___x_128_; uint8_t v___x_129_; uint8_t v___x_130_; 
v___x_128_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_126_, v_b_127_);
v___x_129_ = 2;
v___x_130_ = l_instDecidableEqOrdering(v___x_128_, v___x_129_);
if (v___x_130_ == 0)
{
uint8_t v___x_131_; 
v___x_131_ = 1;
return v___x_131_;
}
else
{
uint8_t v___x_132_; 
v___x_132_ = 0;
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLEWeight___boxed(lean_object* v_a_133_, lean_object* v_b_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Lean_Meta_Grind_Order_instDecidableLEWeight(v_a_133_, v_b_134_);
lean_dec_ref(v_b_134_);
lean_dec_ref(v_a_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLTWeight(lean_object* v_a_137_, lean_object* v_b_138_){
_start:
{
uint8_t v___x_139_; uint8_t v___x_140_; uint8_t v___x_141_; 
v___x_139_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_137_, v_b_138_);
v___x_140_ = 0;
v___x_141_ = l_instDecidableEqOrdering(v___x_139_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLTWeight___boxed(lean_object* v_a_142_, lean_object* v_b_143_){
_start:
{
uint8_t v_res_144_; lean_object* v_r_145_; 
v_res_144_ = l_Lean_Meta_Grind_Order_instDecidableLTWeight(v_a_142_, v_b_143_);
lean_dec_ref(v_b_143_);
lean_dec_ref(v_a_142_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add(lean_object* v_a_146_, lean_object* v_b_147_){
_start:
{
lean_object* v_k_148_; uint8_t v_strict_149_; lean_object* v_k_150_; uint8_t v_strict_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_162_; 
v_k_148_ = lean_ctor_get(v_a_146_, 0);
v_strict_149_ = lean_ctor_get_uint8(v_a_146_, sizeof(void*)*1);
v_k_150_ = lean_ctor_get(v_b_147_, 0);
v_strict_151_ = lean_ctor_get_uint8(v_b_147_, sizeof(void*)*1);
v_isSharedCheck_162_ = !lean_is_exclusive(v_b_147_);
if (v_isSharedCheck_162_ == 0)
{
v___x_153_ = v_b_147_;
v_isShared_154_ = v_isSharedCheck_162_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_k_150_);
lean_dec(v_b_147_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_162_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; 
v___x_155_ = lean_int_add(v_k_148_, v_k_150_);
lean_dec(v_k_150_);
if (v_strict_149_ == 0)
{
lean_object* v___x_157_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_155_);
v___x_157_ = v___x_153_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, sizeof(void*)*1, v_strict_151_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
else
{
lean_object* v___x_160_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_155_);
v___x_160_ = v___x_153_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_ctor_set_uint8(v___x_160_, sizeof(void*)*1, v_strict_149_);
return v___x_160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add___boxed(lean_object* v_a_163_, lean_object* v_b_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Meta_Grind_Order_Weight_add(v_a_163_, v_b_164_);
lean_dec_ref(v_a_163_);
return v_res_165_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isNeg(lean_object* v_a_168_){
_start:
{
lean_object* v_k_169_; uint8_t v_strict_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v_k_169_ = lean_ctor_get(v_a_168_, 0);
v_strict_170_ = lean_ctor_get_uint8(v_a_168_, sizeof(void*)*1);
v___x_171_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v___x_172_ = lean_int_dec_lt(v_k_169_, v___x_171_);
if (v___x_172_ == 0)
{
uint8_t v___x_173_; 
v___x_173_ = lean_int_dec_eq(v_k_169_, v___x_171_);
if (v___x_173_ == 0)
{
return v___x_173_;
}
else
{
return v_strict_170_;
}
}
else
{
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isNeg___boxed(lean_object* v_a_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v_a_174_);
lean_dec_ref(v_a_174_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isZero(lean_object* v_a_177_){
_start:
{
lean_object* v_k_178_; uint8_t v_strict_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v_k_178_ = lean_ctor_get(v_a_177_, 0);
v_strict_179_ = lean_ctor_get_uint8(v_a_177_, sizeof(void*)*1);
v___x_180_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v___x_181_ = lean_int_dec_eq(v_k_178_, v___x_180_);
if (v___x_181_ == 0)
{
return v___x_181_;
}
else
{
uint8_t v___x_182_; 
v___x_182_ = lean_bool_not(v_strict_179_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isZero___boxed(lean_object* v_a_183_){
_start:
{
uint8_t v_res_184_; lean_object* v_r_185_; 
v_res_184_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_a_183_);
lean_dec_ref(v_a_183_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(lean_object* v_a_187_){
_start:
{
uint8_t v_strict_188_; 
v_strict_188_ = lean_ctor_get_uint8(v_a_187_, sizeof(void*)*1);
if (v_strict_188_ == 0)
{
lean_object* v_k_189_; lean_object* v___x_190_; 
v_k_189_ = lean_ctor_get(v_a_187_, 0);
v___x_190_ = l_Int_repr(v_k_189_);
return v___x_190_;
}
else
{
lean_object* v_k_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_k_191_ = lean_ctor_get(v_a_187_, 0);
v___x_192_ = l_Int_repr(v_k_191_);
v___x_193_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_194_ = lean_string_append(v___x_192_, v___x_193_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed(lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(v_a_195_);
lean_dec_ref(v_a_195_);
return v_res_196_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__0));
v___x_201_ = l_Lean_stringToMessageData(v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__2));
v___x_204_ = l_Lean_stringToMessageData(v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__4));
v___x_207_ = l_Lean_stringToMessageData(v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__6));
v___x_210_ = l_Lean_stringToMessageData(v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object* v_todo_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
switch(lean_obj_tag(v_todo_211_))
{
case 0:
{
lean_object* v_e_224_; lean_object* v_u_225_; lean_object* v_v_226_; lean_object* v_k_227_; lean_object* v_k_x27_228_; lean_object* v___x_229_; 
v_e_224_ = lean_ctor_get(v_todo_211_, 1);
lean_inc_ref(v_e_224_);
v_u_225_ = lean_ctor_get(v_todo_211_, 2);
lean_inc(v_u_225_);
v_v_226_ = lean_ctor_get(v_todo_211_, 3);
lean_inc(v_v_226_);
v_k_227_ = lean_ctor_get(v_todo_211_, 4);
lean_inc_ref(v_k_227_);
v_k_x27_228_ = lean_ctor_get(v_todo_211_, 5);
lean_inc_ref(v_k_x27_228_);
lean_dec_ref_known(v_todo_211_, 6);
v___x_229_ = l_Lean_Meta_Grind_Order_getExpr(v_u_225_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
lean_dec(v_u_225_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_231_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v___x_229_, 1);
v___x_231_ = l_Lean_Meta_Grind_Order_getExpr(v_v_226_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
lean_dec(v_v_226_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_274_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_274_ == 0)
{
v___x_234_ = v___x_231_;
v_isShared_235_ = v_isSharedCheck_274_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_274_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v_k_250_; uint8_t v_strict_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___y_259_; 
v___x_245_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1);
v___x_246_ = l_Lean_MessageData_ofExpr(v_e_224_);
v___x_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
v___x_249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v_k_250_ = lean_ctor_get(v_k_227_, 0);
lean_inc(v_k_250_);
v_strict_251_ = lean_ctor_get_uint8(v_k_227_, sizeof(void*)*1);
lean_dec_ref(v_k_227_);
v___x_252_ = l_Lean_MessageData_ofExpr(v_a_230_);
v___x_253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_249_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___x_248_);
v___x_255_ = l_Lean_MessageData_ofExpr(v_a_232_);
v___x_256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___x_248_);
if (v_strict_251_ == 0)
{
lean_object* v___x_270_; 
v___x_270_ = l_Int_repr(v_k_250_);
lean_dec(v_k_250_);
v___y_259_ = v___x_270_;
goto v___jp_258_;
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = l_Int_repr(v_k_250_);
lean_dec(v_k_250_);
v___x_272_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_273_ = lean_string_append(v___x_271_, v___x_272_);
v___y_259_ = v___x_273_;
goto v___jp_258_;
}
v___jp_236_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_239_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_239_, 0, v___y_238_);
v___x_240_ = l_Lean_MessageData_ofFormat(v___x_239_);
v___x_241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_241_, 0, v___y_237_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_241_);
v___x_243_ = v___x_234_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
v___jp_258_:
{
lean_object* v_k_260_; uint8_t v_strict_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_k_260_ = lean_ctor_get(v_k_x27_228_, 0);
lean_inc(v_k_260_);
v_strict_261_ = lean_ctor_get_uint8(v_k_x27_228_, sizeof(void*)*1);
lean_dec_ref(v_k_x27_228_);
v___x_262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_262_, 0, v___y_259_);
v___x_263_ = l_Lean_MessageData_ofFormat(v___x_262_);
v___x_264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_257_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___x_248_);
if (v_strict_261_ == 0)
{
lean_object* v___x_266_; 
v___x_266_ = l_Int_repr(v_k_260_);
lean_dec(v_k_260_);
v___y_237_ = v___x_265_;
v___y_238_ = v___x_266_;
goto v___jp_236_;
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = l_Int_repr(v_k_260_);
lean_dec(v_k_260_);
v___x_268_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_269_ = lean_string_append(v___x_267_, v___x_268_);
v___y_237_ = v___x_265_;
v___y_238_ = v___x_269_;
goto v___jp_236_;
}
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec(v_a_230_);
lean_dec_ref(v_k_x27_228_);
lean_dec_ref(v_k_227_);
lean_dec_ref(v_e_224_);
v_a_275_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_231_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_231_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_dec_ref(v_k_x27_228_);
lean_dec_ref(v_k_227_);
lean_dec(v_v_226_);
lean_dec_ref(v_e_224_);
v_a_283_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_229_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_229_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
case 1:
{
lean_object* v_e_291_; lean_object* v_u_292_; lean_object* v_v_293_; lean_object* v_k_294_; lean_object* v_k_x27_295_; lean_object* v___x_296_; 
v_e_291_ = lean_ctor_get(v_todo_211_, 1);
lean_inc_ref(v_e_291_);
v_u_292_ = lean_ctor_get(v_todo_211_, 2);
lean_inc(v_u_292_);
v_v_293_ = lean_ctor_get(v_todo_211_, 3);
lean_inc(v_v_293_);
v_k_294_ = lean_ctor_get(v_todo_211_, 4);
lean_inc_ref(v_k_294_);
v_k_x27_295_ = lean_ctor_get(v_todo_211_, 5);
lean_inc_ref(v_k_x27_295_);
lean_dec_ref_known(v_todo_211_, 6);
v___x_296_ = l_Lean_Meta_Grind_Order_getExpr(v_u_292_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
lean_dec(v_u_292_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_298_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v___x_296_, 1);
v___x_298_ = l_Lean_Meta_Grind_Order_getExpr(v_v_293_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
lean_dec(v_v_293_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_341_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_341_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_341_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_341_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___y_304_; lean_object* v___y_305_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v_k_317_; uint8_t v_strict_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___y_326_; 
v___x_312_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5);
v___x_313_ = l_Lean_MessageData_ofExpr(v_e_291_);
v___x_314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
v___x_316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v_k_317_ = lean_ctor_get(v_k_294_, 0);
lean_inc(v_k_317_);
v_strict_318_ = lean_ctor_get_uint8(v_k_294_, sizeof(void*)*1);
lean_dec_ref(v_k_294_);
v___x_319_ = l_Lean_MessageData_ofExpr(v_a_297_);
v___x_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_316_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_315_);
v___x_322_ = l_Lean_MessageData_ofExpr(v_a_299_);
v___x_323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_315_);
if (v_strict_318_ == 0)
{
lean_object* v___x_337_; 
v___x_337_ = l_Int_repr(v_k_317_);
lean_dec(v_k_317_);
v___y_326_ = v___x_337_;
goto v___jp_325_;
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = l_Int_repr(v_k_317_);
lean_dec(v_k_317_);
v___x_339_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_340_ = lean_string_append(v___x_338_, v___x_339_);
v___y_326_ = v___x_340_;
goto v___jp_325_;
}
v___jp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_306_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_306_, 0, v___y_305_);
v___x_307_ = l_Lean_MessageData_ofFormat(v___x_306_);
v___x_308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_308_, 0, v___y_304_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_308_);
v___x_310_ = v___x_301_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
v___jp_325_:
{
lean_object* v_k_327_; uint8_t v_strict_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_k_327_ = lean_ctor_get(v_k_x27_295_, 0);
lean_inc(v_k_327_);
v_strict_328_ = lean_ctor_get_uint8(v_k_x27_295_, sizeof(void*)*1);
lean_dec_ref(v_k_x27_295_);
v___x_329_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_329_, 0, v___y_326_);
v___x_330_ = l_Lean_MessageData_ofFormat(v___x_329_);
v___x_331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_324_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_315_);
if (v_strict_328_ == 0)
{
lean_object* v___x_333_; 
v___x_333_ = l_Int_repr(v_k_327_);
lean_dec(v_k_327_);
v___y_304_ = v___x_332_;
v___y_305_ = v___x_333_;
goto v___jp_303_;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = l_Int_repr(v_k_327_);
lean_dec(v_k_327_);
v___x_335_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_336_ = lean_string_append(v___x_334_, v___x_335_);
v___y_304_ = v___x_332_;
v___y_305_ = v___x_336_;
goto v___jp_303_;
}
}
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec(v_a_297_);
lean_dec_ref(v_k_x27_295_);
lean_dec_ref(v_k_294_);
lean_dec_ref(v_e_291_);
v_a_342_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_298_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_298_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec_ref(v_k_x27_295_);
lean_dec_ref(v_k_294_);
lean_dec(v_v_293_);
lean_dec_ref(v_e_291_);
v_a_350_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_296_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_296_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
default: 
{
lean_object* v_u_358_; lean_object* v_v_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_399_; 
v_u_358_ = lean_ctor_get(v_todo_211_, 0);
v_v_359_ = lean_ctor_get(v_todo_211_, 1);
v_isSharedCheck_399_ = !lean_is_exclusive(v_todo_211_);
if (v_isSharedCheck_399_ == 0)
{
v___x_361_ = v_todo_211_;
v_isShared_362_ = v_isSharedCheck_399_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_v_359_);
lean_inc(v_u_358_);
lean_dec(v_todo_211_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_399_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_Meta_Grind_Order_getExpr(v_u_358_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
lean_dec(v_u_358_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_365_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_363_, 1);
v___x_365_ = l_Lean_Meta_Grind_Order_getExpr(v_v_359_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
lean_dec(v_v_359_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_382_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_382_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_382_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_382_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_370_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7);
v___x_371_ = l_Lean_MessageData_ofExpr(v_a_364_);
if (v_isShared_362_ == 0)
{
lean_ctor_set_tag(v___x_361_, 7);
lean_ctor_set(v___x_361_, 1, v___x_371_);
lean_ctor_set(v___x_361_, 0, v___x_370_);
v___x_373_ = v___x_361_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v___x_371_);
v___x_373_ = v_reuseFailAlloc_381_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_374_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
v___x_375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = l_Lean_MessageData_ofExpr(v_a_366_);
v___x_377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_377_);
v___x_379_ = v___x_368_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec(v_a_364_);
lean_del_object(v___x_361_);
v_a_383_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_365_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_365_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_del_object(v___x_361_);
lean_dec(v_v_359_);
v_a_391_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_363_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_363_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___boxed(lean_object* v_todo_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Meta_Grind_Order_ToPropagate_pp(v_todo_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec(v_a_402_);
lean_dec(v_a_401_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(lean_object* v_c_414_){
_start:
{
uint8_t v_kind_415_; 
v_kind_415_ = lean_ctor_get_uint8(v_c_414_, sizeof(void*)*5);
if (v_kind_415_ == 0)
{
lean_object* v_k_416_; uint8_t v___x_417_; lean_object* v___x_418_; 
v_k_416_ = lean_ctor_get(v_c_414_, 2);
v___x_417_ = 0;
lean_inc(v_k_416_);
v___x_418_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_418_, 0, v_k_416_);
lean_ctor_set_uint8(v___x_418_, sizeof(void*)*1, v___x_417_);
return v___x_418_;
}
else
{
lean_object* v_k_419_; uint8_t v___x_420_; lean_object* v___x_421_; 
v_k_419_ = lean_ctor_get(v_c_414_, 2);
v___x_420_ = 1;
lean_inc(v_k_419_);
v___x_421_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_421_, 0, v_k_419_);
lean_ctor_set_uint8(v___x_421_, sizeof(void*)*1, v___x_420_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg___boxed(lean_object* v_c_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_422_);
lean_dec_ref(v_c_422_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight(lean_object* v_00_u03b1_424_, lean_object* v_c_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___boxed(lean_object* v_00_u03b1_427_, lean_object* v_c_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight(v_00_u03b1_427_, v_c_428_);
lean_dec_ref(v_c_428_);
return v_res_429_;
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
