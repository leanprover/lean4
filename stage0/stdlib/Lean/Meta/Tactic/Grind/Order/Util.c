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
lean_dec_ref(v___x_28_);
v___x_30_ = l_Lean_Meta_Grind_Order_getExpr(v_v_26_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_69_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_69_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_69_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_69_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___y_36_; 
if (v_kind_24_ == 0)
{
lean_object* v___x_67_; 
v___x_67_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__5));
v___y_36_ = v___x_67_;
goto v___jp_35_;
}
else
{
lean_object* v___x_68_; 
v___x_68_ = ((lean_object*)(l_Lean_Meta_Grind_Order_Cnstr_pp___closed__6));
v___y_36_ = v___x_68_;
goto v___jp_35_;
}
v___jp_35_:
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v___x_38_ = lean_int_dec_eq(v_k_27_, v___x_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_54_; 
v___x_39_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_29_);
v___x_40_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2);
v___x_41_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_39_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
lean_inc_ref(v___y_36_);
v___x_42_ = l_Lean_stringToMessageData(v___y_36_);
v___x_43_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_41_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
v___x_44_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_40_);
v___x_45_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_31_);
v___x_46_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_44_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
v___x_47_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__4);
v___x_48_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_46_);
lean_ctor_set(v___x_48_, 1, v___x_47_);
v___x_49_ = l_Int_repr(v_k_27_);
v___x_50_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
v___x_51_ = l_Lean_MessageData_ofFormat(v___x_50_);
v___x_52_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_48_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 0, v___x_52_);
v___x_54_ = v___x_33_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
else
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_56_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_29_);
v___x_57_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__2);
v___x_58_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
lean_inc_ref(v___y_36_);
v___x_59_ = l_Lean_stringToMessageData(v___y_36_);
v___x_60_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___x_57_);
v___x_62_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_31_);
v___x_63_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_61_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 0, v___x_63_);
v___x_65_ = v___x_33_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
}
else
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_77_; 
lean_dec(v_a_29_);
v_a_70_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_77_ == 0)
{
v___x_72_ = v___x_30_;
v_isShared_73_ = v_isSharedCheck_77_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_30_);
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
else
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
v_a_78_ = lean_ctor_get(v___x_28_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v___x_28_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_28_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_a_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___boxed(lean_object* v_c_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec(v_a_88_);
lean_dec(v_a_87_);
lean_dec_ref(v_c_86_);
return v_res_99_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_compare(lean_object* v_a_100_, lean_object* v_b_101_){
_start:
{
lean_object* v_k_102_; uint8_t v_strict_103_; lean_object* v_k_104_; uint8_t v_strict_105_; uint8_t v___x_110_; 
v_k_102_ = lean_ctor_get(v_a_100_, 0);
v_strict_103_ = lean_ctor_get_uint8(v_a_100_, sizeof(void*)*1);
v_k_104_ = lean_ctor_get(v_b_101_, 0);
v_strict_105_ = lean_ctor_get_uint8(v_b_101_, sizeof(void*)*1);
v___x_110_ = lean_int_dec_lt(v_k_102_, v_k_104_);
if (v___x_110_ == 0)
{
uint8_t v___x_111_; 
v___x_111_ = lean_int_dec_lt(v_k_104_, v_k_102_);
if (v___x_111_ == 0)
{
if (v_strict_103_ == 0)
{
if (v_strict_105_ == 0)
{
uint8_t v___x_112_; 
v___x_112_ = 1;
return v___x_112_;
}
else
{
goto v___jp_106_;
}
}
else
{
if (v_strict_105_ == 0)
{
goto v___jp_106_;
}
else
{
uint8_t v___x_113_; 
v___x_113_ = 1;
return v___x_113_;
}
}
}
else
{
uint8_t v___x_114_; 
v___x_114_ = 2;
return v___x_114_;
}
}
else
{
uint8_t v___x_115_; 
v___x_115_ = 0;
return v___x_115_;
}
v___jp_106_:
{
if (v_strict_103_ == 0)
{
uint8_t v___x_107_; 
v___x_107_ = 2;
return v___x_107_;
}
else
{
if (v_strict_105_ == 0)
{
uint8_t v___x_108_; 
v___x_108_ = 0;
return v___x_108_;
}
else
{
uint8_t v___x_109_; 
v___x_109_ = 2;
return v___x_109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_compare___boxed(lean_object* v_a_116_, lean_object* v_b_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_116_, v_b_117_);
lean_dec_ref(v_b_117_);
lean_dec_ref(v_a_116_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instLEWeight(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_box(0);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_instLTWeight(void){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_box(0);
return v___x_123_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLEWeight(lean_object* v_a_124_, lean_object* v_b_125_){
_start:
{
uint8_t v___x_126_; uint8_t v___x_127_; uint8_t v___x_128_; 
v___x_126_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_124_, v_b_125_);
v___x_127_ = 2;
v___x_128_ = l_instDecidableEqOrdering(v___x_126_, v___x_127_);
if (v___x_128_ == 0)
{
uint8_t v___x_129_; 
v___x_129_ = 1;
return v___x_129_;
}
else
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLEWeight___boxed(lean_object* v_a_131_, lean_object* v_b_132_){
_start:
{
uint8_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_Lean_Meta_Grind_Order_instDecidableLEWeight(v_a_131_, v_b_132_);
lean_dec_ref(v_b_132_);
lean_dec_ref(v_a_131_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_instDecidableLTWeight(lean_object* v_a_135_, lean_object* v_b_136_){
_start:
{
uint8_t v___x_137_; uint8_t v___x_138_; uint8_t v___x_139_; 
v___x_137_ = l_Lean_Meta_Grind_Order_Weight_compare(v_a_135_, v_b_136_);
v___x_138_ = 0;
v___x_139_ = l_instDecidableEqOrdering(v___x_137_, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instDecidableLTWeight___boxed(lean_object* v_a_140_, lean_object* v_b_141_){
_start:
{
uint8_t v_res_142_; lean_object* v_r_143_; 
v_res_142_ = l_Lean_Meta_Grind_Order_instDecidableLTWeight(v_a_140_, v_b_141_);
lean_dec_ref(v_b_141_);
lean_dec_ref(v_a_140_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add(lean_object* v_a_144_, lean_object* v_b_145_){
_start:
{
lean_object* v_k_146_; uint8_t v_strict_147_; lean_object* v_k_148_; uint8_t v_strict_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_160_; 
v_k_146_ = lean_ctor_get(v_a_144_, 0);
v_strict_147_ = lean_ctor_get_uint8(v_a_144_, sizeof(void*)*1);
v_k_148_ = lean_ctor_get(v_b_145_, 0);
v_strict_149_ = lean_ctor_get_uint8(v_b_145_, sizeof(void*)*1);
v_isSharedCheck_160_ = !lean_is_exclusive(v_b_145_);
if (v_isSharedCheck_160_ == 0)
{
v___x_151_ = v_b_145_;
v_isShared_152_ = v_isSharedCheck_160_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_k_148_);
lean_dec(v_b_145_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_160_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; 
v___x_153_ = lean_int_add(v_k_146_, v_k_148_);
lean_dec(v_k_148_);
if (v_strict_147_ == 0)
{
lean_object* v___x_155_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v___x_153_);
v___x_155_ = v___x_151_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, sizeof(void*)*1, v_strict_149_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
else
{
lean_object* v___x_158_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v___x_153_);
v___x_158_ = v___x_151_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_ctor_set_uint8(v___x_158_, sizeof(void*)*1, v_strict_147_);
return v___x_158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_add___boxed(lean_object* v_a_161_, lean_object* v_b_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_Meta_Grind_Order_Weight_add(v_a_161_, v_b_162_);
lean_dec_ref(v_a_161_);
return v_res_163_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isNeg(lean_object* v_a_166_){
_start:
{
lean_object* v_k_167_; uint8_t v_strict_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v_k_167_ = lean_ctor_get(v_a_166_, 0);
v_strict_168_ = lean_ctor_get_uint8(v_a_166_, sizeof(void*)*1);
v___x_169_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v___x_170_ = lean_int_dec_lt(v_k_167_, v___x_169_);
if (v___x_170_ == 0)
{
uint8_t v___x_171_; 
v___x_171_ = lean_int_dec_eq(v_k_167_, v___x_169_);
if (v___x_171_ == 0)
{
return v___x_171_;
}
else
{
return v_strict_168_;
}
}
else
{
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isNeg___boxed(lean_object* v_a_172_){
_start:
{
uint8_t v_res_173_; lean_object* v_r_174_; 
v_res_173_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v_a_172_);
lean_dec_ref(v_a_172_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Order_Weight_isZero(lean_object* v_a_175_){
_start:
{
lean_object* v_k_176_; uint8_t v_strict_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v_k_176_ = lean_ctor_get(v_a_175_, 0);
v_strict_177_ = lean_ctor_get_uint8(v_a_175_, sizeof(void*)*1);
v___x_178_ = lean_obj_once(&l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0, &l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0_once, _init_l_Lean_Meta_Grind_Order_Cnstr_pp___closed__0);
v___x_179_ = lean_int_dec_eq(v_k_176_, v___x_178_);
if (v___x_179_ == 0)
{
return v___x_179_;
}
else
{
if (v_strict_177_ == 0)
{
return v___x_179_;
}
else
{
uint8_t v___x_180_; 
v___x_180_ = 0;
return v___x_180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Weight_isZero___boxed(lean_object* v_a_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_a_181_);
lean_dec_ref(v_a_181_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(lean_object* v_a_185_){
_start:
{
uint8_t v_strict_186_; 
v_strict_186_ = lean_ctor_get_uint8(v_a_185_, sizeof(void*)*1);
if (v_strict_186_ == 0)
{
lean_object* v_k_187_; lean_object* v___x_188_; 
v_k_187_ = lean_ctor_get(v_a_185_, 0);
v___x_188_ = l_Int_repr(v_k_187_);
return v___x_188_;
}
else
{
lean_object* v_k_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_k_189_ = lean_ctor_get(v_a_185_, 0);
v___x_190_ = l_Int_repr(v_k_189_);
v___x_191_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_192_ = lean_string_append(v___x_190_, v___x_191_);
return v___x_192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___boxed(lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Meta_Grind_Order_instToStringWeight___lam__0(v_a_193_);
lean_dec_ref(v_a_193_);
return v_res_194_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__0));
v___x_199_ = l_Lean_stringToMessageData(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__2));
v___x_202_ = l_Lean_stringToMessageData(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__4));
v___x_205_ = l_Lean_stringToMessageData(v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__6));
v___x_208_ = l_Lean_stringToMessageData(v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object* v_todo_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
switch(lean_obj_tag(v_todo_209_))
{
case 0:
{
lean_object* v_e_222_; lean_object* v_u_223_; lean_object* v_v_224_; lean_object* v_k_225_; lean_object* v_k_x27_226_; lean_object* v___x_227_; 
v_e_222_ = lean_ctor_get(v_todo_209_, 1);
lean_inc_ref(v_e_222_);
v_u_223_ = lean_ctor_get(v_todo_209_, 2);
lean_inc(v_u_223_);
v_v_224_ = lean_ctor_get(v_todo_209_, 3);
lean_inc(v_v_224_);
v_k_225_ = lean_ctor_get(v_todo_209_, 4);
lean_inc_ref(v_k_225_);
v_k_x27_226_ = lean_ctor_get(v_todo_209_, 5);
lean_inc_ref(v_k_x27_226_);
lean_dec_ref(v_todo_209_);
v___x_227_ = l_Lean_Meta_Grind_Order_getExpr(v_u_223_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
lean_dec(v_u_223_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_229_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref(v___x_227_);
v___x_229_ = l_Lean_Meta_Grind_Order_getExpr(v_v_224_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
lean_dec(v_v_224_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_272_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_272_ == 0)
{
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_272_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_272_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v_k_248_; uint8_t v_strict_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___y_257_; 
v___x_243_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__1);
v___x_244_ = l_Lean_MessageData_ofExpr(v_e_222_);
v___x_245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
v___x_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v_k_248_ = lean_ctor_get(v_k_225_, 0);
lean_inc(v_k_248_);
v_strict_249_ = lean_ctor_get_uint8(v_k_225_, sizeof(void*)*1);
lean_dec_ref(v_k_225_);
v___x_250_ = l_Lean_MessageData_ofExpr(v_a_228_);
v___x_251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_247_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_246_);
v___x_253_ = l_Lean_MessageData_ofExpr(v_a_230_);
v___x_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_246_);
if (v_strict_249_ == 0)
{
lean_object* v___x_268_; 
v___x_268_ = l_Int_repr(v_k_248_);
lean_dec(v_k_248_);
v___y_257_ = v___x_268_;
goto v___jp_256_;
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = l_Int_repr(v_k_248_);
lean_dec(v_k_248_);
v___x_270_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_271_ = lean_string_append(v___x_269_, v___x_270_);
v___y_257_ = v___x_271_;
goto v___jp_256_;
}
v___jp_234_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_237_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_237_, 0, v___y_236_);
v___x_238_ = l_Lean_MessageData_ofFormat(v___x_237_);
v___x_239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_239_, 0, v___y_235_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_239_);
v___x_241_ = v___x_232_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
v___jp_256_:
{
lean_object* v_k_258_; uint8_t v_strict_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_k_258_ = lean_ctor_get(v_k_x27_226_, 0);
lean_inc(v_k_258_);
v_strict_259_ = lean_ctor_get_uint8(v_k_x27_226_, sizeof(void*)*1);
lean_dec_ref(v_k_x27_226_);
v___x_260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_260_, 0, v___y_257_);
v___x_261_ = l_Lean_MessageData_ofFormat(v___x_260_);
v___x_262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_255_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_246_);
if (v_strict_259_ == 0)
{
lean_object* v___x_264_; 
v___x_264_ = l_Int_repr(v_k_258_);
lean_dec(v_k_258_);
v___y_235_ = v___x_263_;
v___y_236_ = v___x_264_;
goto v___jp_234_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = l_Int_repr(v_k_258_);
lean_dec(v_k_258_);
v___x_266_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_267_ = lean_string_append(v___x_265_, v___x_266_);
v___y_235_ = v___x_263_;
v___y_236_ = v___x_267_;
goto v___jp_234_;
}
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec(v_a_228_);
lean_dec_ref(v_k_x27_226_);
lean_dec_ref(v_k_225_);
lean_dec_ref(v_e_222_);
v_a_273_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_229_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_229_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
lean_dec_ref(v_k_x27_226_);
lean_dec_ref(v_k_225_);
lean_dec(v_v_224_);
lean_dec_ref(v_e_222_);
v_a_281_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_227_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_227_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
case 1:
{
lean_object* v_e_289_; lean_object* v_u_290_; lean_object* v_v_291_; lean_object* v_k_292_; lean_object* v_k_x27_293_; lean_object* v___x_294_; 
v_e_289_ = lean_ctor_get(v_todo_209_, 1);
lean_inc_ref(v_e_289_);
v_u_290_ = lean_ctor_get(v_todo_209_, 2);
lean_inc(v_u_290_);
v_v_291_ = lean_ctor_get(v_todo_209_, 3);
lean_inc(v_v_291_);
v_k_292_ = lean_ctor_get(v_todo_209_, 4);
lean_inc_ref(v_k_292_);
v_k_x27_293_ = lean_ctor_get(v_todo_209_, 5);
lean_inc_ref(v_k_x27_293_);
lean_dec_ref(v_todo_209_);
v___x_294_ = l_Lean_Meta_Grind_Order_getExpr(v_u_290_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
lean_dec(v_u_290_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_296_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref(v___x_294_);
v___x_296_ = l_Lean_Meta_Grind_Order_getExpr(v_v_291_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
lean_dec(v_v_291_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_339_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_339_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_339_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_339_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v_k_315_; uint8_t v_strict_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___y_324_; 
v___x_310_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__5);
v___x_311_ = l_Lean_MessageData_ofExpr(v_e_289_);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
v___x_314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v_k_315_ = lean_ctor_get(v_k_292_, 0);
lean_inc(v_k_315_);
v_strict_316_ = lean_ctor_get_uint8(v_k_292_, sizeof(void*)*1);
lean_dec_ref(v_k_292_);
v___x_317_ = l_Lean_MessageData_ofExpr(v_a_295_);
v___x_318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_314_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_313_);
v___x_320_ = l_Lean_MessageData_ofExpr(v_a_297_);
v___x_321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_313_);
if (v_strict_316_ == 0)
{
lean_object* v___x_335_; 
v___x_335_ = l_Int_repr(v_k_315_);
lean_dec(v_k_315_);
v___y_324_ = v___x_335_;
goto v___jp_323_;
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = l_Int_repr(v_k_315_);
lean_dec(v_k_315_);
v___x_337_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_338_ = lean_string_append(v___x_336_, v___x_337_);
v___y_324_ = v___x_338_;
goto v___jp_323_;
}
v___jp_301_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_304_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_304_, 0, v___y_303_);
v___x_305_ = l_Lean_MessageData_ofFormat(v___x_304_);
v___x_306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_306_, 0, v___y_302_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_306_);
v___x_308_ = v___x_299_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
v___jp_323_:
{
lean_object* v_k_325_; uint8_t v_strict_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_k_325_ = lean_ctor_get(v_k_x27_293_, 0);
lean_inc(v_k_325_);
v_strict_326_ = lean_ctor_get_uint8(v_k_x27_293_, sizeof(void*)*1);
lean_dec_ref(v_k_x27_293_);
v___x_327_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_327_, 0, v___y_324_);
v___x_328_ = l_Lean_MessageData_ofFormat(v___x_327_);
v___x_329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_322_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_313_);
if (v_strict_326_ == 0)
{
lean_object* v___x_331_; 
v___x_331_ = l_Int_repr(v_k_325_);
lean_dec(v_k_325_);
v___y_302_ = v___x_330_;
v___y_303_ = v___x_331_;
goto v___jp_301_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = l_Int_repr(v_k_325_);
lean_dec(v_k_325_);
v___x_333_ = ((lean_object*)(l_Lean_Meta_Grind_Order_instToStringWeight___lam__0___closed__0));
v___x_334_ = lean_string_append(v___x_332_, v___x_333_);
v___y_302_ = v___x_330_;
v___y_303_ = v___x_334_;
goto v___jp_301_;
}
}
}
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec(v_a_295_);
lean_dec_ref(v_k_x27_293_);
lean_dec_ref(v_k_292_);
lean_dec_ref(v_e_289_);
v_a_340_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_296_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_296_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec_ref(v_k_x27_293_);
lean_dec_ref(v_k_292_);
lean_dec(v_v_291_);
lean_dec_ref(v_e_289_);
v_a_348_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_294_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_294_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
default: 
{
lean_object* v_u_356_; lean_object* v_v_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_397_; 
v_u_356_ = lean_ctor_get(v_todo_209_, 0);
v_v_357_ = lean_ctor_get(v_todo_209_, 1);
v_isSharedCheck_397_ = !lean_is_exclusive(v_todo_209_);
if (v_isSharedCheck_397_ == 0)
{
v___x_359_ = v_todo_209_;
v_isShared_360_ = v_isSharedCheck_397_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_v_357_);
lean_inc(v_u_356_);
lean_dec(v_todo_209_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_397_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Meta_Grind_Order_getExpr(v_u_356_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
lean_dec(v_u_356_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_363_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref(v___x_361_);
v___x_363_ = l_Lean_Meta_Grind_Order_getExpr(v_v_357_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
lean_dec(v_v_357_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_380_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_380_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_380_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_380_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_368_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__7);
v___x_369_ = l_Lean_MessageData_ofExpr(v_a_362_);
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 7);
lean_ctor_set(v___x_359_, 1, v___x_369_);
lean_ctor_set(v___x_359_, 0, v___x_368_);
v___x_371_ = v___x_359_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___x_369_);
v___x_371_ = v_reuseFailAlloc_379_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_372_ = lean_obj_once(&l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3, &l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3_once, _init_l_Lean_Meta_Grind_Order_ToPropagate_pp___closed__3);
v___x_373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = l_Lean_MessageData_ofExpr(v_a_364_);
v___x_375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_375_);
v___x_377_ = v___x_366_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec(v_a_362_);
lean_del_object(v___x_359_);
v_a_381_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_363_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_363_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_del_object(v___x_359_);
lean_dec(v_v_357_);
v_a_389_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_361_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_361_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___boxed(lean_object* v_todo_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Meta_Grind_Order_ToPropagate_pp(v_todo_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec(v_a_400_);
lean_dec(v_a_399_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(lean_object* v_c_412_){
_start:
{
uint8_t v_kind_413_; 
v_kind_413_ = lean_ctor_get_uint8(v_c_412_, sizeof(void*)*5);
if (v_kind_413_ == 0)
{
lean_object* v_k_414_; uint8_t v___x_415_; lean_object* v___x_416_; 
v_k_414_ = lean_ctor_get(v_c_412_, 2);
v___x_415_ = 0;
lean_inc(v_k_414_);
v___x_416_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_416_, 0, v_k_414_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*1, v___x_415_);
return v___x_416_;
}
else
{
lean_object* v_k_417_; uint8_t v___x_418_; lean_object* v___x_419_; 
v_k_417_ = lean_ctor_get(v_c_412_, 2);
v___x_418_ = 1;
lean_inc(v_k_417_);
v___x_419_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_419_, 0, v_k_417_);
lean_ctor_set_uint8(v___x_419_, sizeof(void*)*1, v___x_418_);
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg___boxed(lean_object* v_c_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_420_);
lean_dec_ref(v_c_420_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight(lean_object* v_00_u03b1_422_, lean_object* v_c_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___boxed(lean_object* v_00_u03b1_425_, lean_object* v_c_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight(v_00_u03b1_425_, v_c_426_);
lean_dec_ref(v_c_426_);
return v_res_427_;
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
