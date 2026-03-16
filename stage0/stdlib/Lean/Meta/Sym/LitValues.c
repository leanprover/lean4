// Lean compiler output
// Module: Lean.Meta.Sym.LitValues
// Imports: public import Lean.Expr public import Init.Data.Rat
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_int8_of_int(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
uint64_t lean_int64_of_int(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
uint32_t lean_int32_of_int(lean_object*);
uint16_t lean_int16_of_int(lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getNatValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Sym_getNatValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Sym_getNatValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Sym_getNatValue_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getIntValue_x3f_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getIntValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Sym_getIntValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_getIntValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Sym_getIntValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Sym_getIntValue_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getRatValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Lean_Meta_Sym_getRatValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_getRatValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Lean_Meta_Sym_getRatValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Lean_Meta_Sym_getRatValue_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getRatValue_x3f(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ofNatLT"};
static const lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 44, 243, 4, 118, 78, 150, 28)}};
static const lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt8Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt16Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt32Value_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt64Value_x3f(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getFinValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Lean_Meta_Sym_getFinValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getFinValue_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_getFinValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getFinValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_object* l_Lean_Meta_Sym_getFinValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getFinValue_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFinValue_x3f(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getCharValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l_Lean_Meta_Sym_getCharValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getCharValue_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getCharValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l_Lean_Meta_Sym_getCharValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCharValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getStringValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object* v_e_6_){
_start:
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = l_Lean_Expr_cleanupAnnotations(v_e_6_);
v___x_8_ = l_Lean_Expr_isApp(v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
lean_dec_ref(v___x_7_);
v___x_9_ = lean_box(0);
return v___x_9_;
}
else
{
lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_10_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7_);
v___x_11_ = l_Lean_Expr_isApp(v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; 
lean_dec_ref(v___x_10_);
v___x_12_ = lean_box(0);
return v___x_12_;
}
else
{
lean_object* v_arg_13_; lean_object* v___x_14_; uint8_t v___x_15_; 
v_arg_13_ = lean_ctor_get(v___x_10_, 1);
lean_inc_ref(v_arg_13_);
v___x_14_ = l_Lean_Expr_appFnCleanup___redArg(v___x_10_);
v___x_15_ = l_Lean_Expr_isApp(v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; 
lean_dec_ref(v___x_14_);
lean_dec_ref(v_arg_13_);
v___x_16_ = lean_box(0);
return v___x_16_;
}
else
{
lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_17_ = l_Lean_Expr_appFnCleanup___redArg(v___x_14_);
v___x_18_ = ((lean_object*)(l_Lean_Meta_Sym_getNatValue_x3f___closed__2));
v___x_19_ = l_Lean_Expr_isConstOf(v___x_17_, v___x_18_);
lean_dec_ref(v___x_17_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; 
lean_dec_ref(v_arg_13_);
v___x_20_ = lean_box(0);
return v___x_20_;
}
else
{
if (lean_obj_tag(v_arg_13_) == 9)
{
lean_object* v_a_21_; 
v_a_21_ = lean_ctor_get(v_arg_13_, 0);
lean_inc_ref(v_a_21_);
lean_dec_ref(v_arg_13_);
if (lean_obj_tag(v_a_21_) == 0)
{
lean_object* v_val_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
v_val_22_ = lean_ctor_get(v_a_21_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v_a_21_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v_a_21_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_val_22_);
lean_dec(v_a_21_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
lean_ctor_set_tag(v___x_24_, 1);
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_val_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
else
{
lean_object* v___x_30_; 
lean_dec_ref(v_a_21_);
v___x_30_ = lean_box(0);
return v___x_30_;
}
}
else
{
lean_object* v___x_31_; 
lean_dec_ref(v_arg_13_);
v___x_31_ = lean_box(0);
return v___x_31_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getIntValue_x3f_spec__0(lean_object* v_a_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_nat_to_int(v_a_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntValue_x3f(lean_object* v_e_39_){
_start:
{
lean_object* v___x_52_; uint8_t v___x_53_; 
lean_inc_ref(v_e_39_);
v___x_52_ = l_Lean_Expr_cleanupAnnotations(v_e_39_);
v___x_53_ = l_Lean_Expr_isApp(v___x_52_);
if (v___x_53_ == 0)
{
lean_dec_ref(v___x_52_);
goto v___jp_40_;
}
else
{
lean_object* v_arg_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v_arg_54_ = lean_ctor_get(v___x_52_, 1);
lean_inc_ref(v_arg_54_);
v___x_55_ = l_Lean_Expr_appFnCleanup___redArg(v___x_52_);
v___x_56_ = l_Lean_Expr_isApp(v___x_55_);
if (v___x_56_ == 0)
{
lean_dec_ref(v___x_55_);
lean_dec_ref(v_arg_54_);
goto v___jp_40_;
}
else
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = l_Lean_Expr_appFnCleanup___redArg(v___x_55_);
v___x_58_ = l_Lean_Expr_isApp(v___x_57_);
if (v___x_58_ == 0)
{
lean_dec_ref(v___x_57_);
lean_dec_ref(v_arg_54_);
goto v___jp_40_;
}
else
{
lean_object* v___x_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_59_ = l_Lean_Expr_appFnCleanup___redArg(v___x_57_);
v___x_60_ = ((lean_object*)(l_Lean_Meta_Sym_getIntValue_x3f___closed__2));
v___x_61_ = l_Lean_Expr_isConstOf(v___x_59_, v___x_60_);
lean_dec_ref(v___x_59_);
if (v___x_61_ == 0)
{
lean_dec_ref(v_arg_54_);
goto v___jp_40_;
}
else
{
lean_object* v___x_62_; 
lean_dec_ref(v_e_39_);
v___x_62_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_54_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v___x_63_; 
v___x_63_ = lean_box(0);
return v___x_63_;
}
else
{
lean_object* v_val_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_73_; 
v_val_64_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_73_ == 0)
{
v___x_66_ = v___x_62_;
v_isShared_67_ = v_isSharedCheck_73_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_val_64_);
lean_dec(v___x_62_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_73_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_68_ = lean_nat_to_int(v_val_64_);
v___x_69_ = lean_int_neg(v___x_68_);
lean_dec(v___x_68_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 0, v___x_69_);
v___x_71_ = v___x_66_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
}
}
}
v___jp_40_:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_39_);
if (lean_obj_tag(v___x_41_) == 0)
{
lean_object* v___x_42_; 
v___x_42_ = lean_box(0);
return v___x_42_;
}
else
{
lean_object* v_val_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_51_; 
v_val_43_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_51_ == 0)
{
v___x_45_ = v___x_41_;
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_val_43_);
lean_dec(v___x_41_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_49_; 
v___x_47_ = lean_nat_to_int(v_val_43_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 0, v___x_47_);
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_47_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__0(lean_object* v_a_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Rat_ofInt(v_a_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(lean_object* v_a_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_nat_to_int(v_a_76_);
v___x_78_ = l_Rat_ofInt(v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getRatValue_x3f(lean_object* v_e_84_){
_start:
{
lean_object* v___x_97_; uint8_t v___x_98_; 
lean_inc_ref(v_e_84_);
v___x_97_ = l_Lean_Expr_cleanupAnnotations(v_e_84_);
v___x_98_ = l_Lean_Expr_isApp(v___x_97_);
if (v___x_98_ == 0)
{
lean_dec_ref(v___x_97_);
goto v___jp_85_;
}
else
{
lean_object* v_arg_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v_arg_99_ = lean_ctor_get(v___x_97_, 1);
lean_inc_ref(v_arg_99_);
v___x_100_ = l_Lean_Expr_appFnCleanup___redArg(v___x_97_);
v___x_101_ = l_Lean_Expr_isApp(v___x_100_);
if (v___x_101_ == 0)
{
lean_dec_ref(v___x_100_);
lean_dec_ref(v_arg_99_);
goto v___jp_85_;
}
else
{
lean_object* v_arg_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_arg_102_ = lean_ctor_get(v___x_100_, 1);
lean_inc_ref(v_arg_102_);
v___x_103_ = l_Lean_Expr_appFnCleanup___redArg(v___x_100_);
v___x_104_ = l_Lean_Expr_isApp(v___x_103_);
if (v___x_104_ == 0)
{
lean_dec_ref(v___x_103_);
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_arg_99_);
goto v___jp_85_;
}
else
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = l_Lean_Expr_appFnCleanup___redArg(v___x_103_);
v___x_106_ = l_Lean_Expr_isApp(v___x_105_);
if (v___x_106_ == 0)
{
lean_dec_ref(v___x_105_);
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_arg_99_);
goto v___jp_85_;
}
else
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = l_Lean_Expr_appFnCleanup___redArg(v___x_105_);
v___x_108_ = l_Lean_Expr_isApp(v___x_107_);
if (v___x_108_ == 0)
{
lean_dec_ref(v___x_107_);
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_arg_99_);
goto v___jp_85_;
}
else
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = l_Lean_Expr_appFnCleanup___redArg(v___x_107_);
v___x_110_ = l_Lean_Expr_isApp(v___x_109_);
if (v___x_110_ == 0)
{
lean_dec_ref(v___x_109_);
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_arg_99_);
goto v___jp_85_;
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_111_ = l_Lean_Expr_appFnCleanup___redArg(v___x_109_);
v___x_112_ = ((lean_object*)(l_Lean_Meta_Sym_getRatValue_x3f___closed__2));
v___x_113_ = l_Lean_Expr_isConstOf(v___x_111_, v___x_112_);
lean_dec_ref(v___x_111_);
if (v___x_113_ == 0)
{
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_arg_99_);
goto v___jp_85_;
}
else
{
lean_object* v___x_114_; 
lean_dec_ref(v_e_84_);
v___x_114_ = l_Lean_Meta_Sym_getIntValue_x3f(v_arg_102_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v___x_115_; 
lean_dec_ref(v_arg_99_);
v___x_115_ = lean_box(0);
return v___x_115_;
}
else
{
lean_object* v_val_116_; lean_object* v___x_117_; 
v_val_116_ = lean_ctor_get(v___x_114_, 0);
lean_inc(v_val_116_);
lean_dec_ref(v___x_114_);
v___x_117_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_99_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v___x_118_; 
lean_dec(v_val_116_);
v___x_118_ = lean_box(0);
return v___x_118_;
}
else
{
lean_object* v_val_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_129_; 
v_val_119_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_129_ == 0)
{
v___x_121_ = v___x_117_;
v_isShared_122_ = v_isSharedCheck_129_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_val_119_);
lean_dec(v___x_117_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_129_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_123_ = l_Rat_ofInt(v_val_116_);
v___x_124_ = l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(v_val_119_);
v___x_125_ = l_Rat_div(v___x_123_, v___x_124_);
lean_dec_ref(v___x_123_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v___x_125_);
v___x_127_ = v___x_121_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
}
}
}
}
}
}
v___jp_85_:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_84_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v___x_87_; 
v___x_87_ = lean_box(0);
return v___x_87_;
}
else
{
lean_object* v_val_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_96_; 
v_val_88_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_96_ == 0)
{
v___x_90_ = v___x_86_;
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_val_88_);
lean_dec(v___x_86_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_92_ = l_Rat_ofInt(v_val_88_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 0, v___x_92_);
v___x_94_ = v___x_90_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object* v_e_140_){
_start:
{
lean_object* v_nExpr_142_; lean_object* v_vExpr_143_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = l_Lean_Expr_cleanupAnnotations(v_e_140_);
v___x_160_ = l_Lean_Expr_isApp(v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
lean_dec_ref(v___x_159_);
v___x_161_ = lean_box(0);
return v___x_161_;
}
else
{
lean_object* v_arg_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v_arg_162_ = lean_ctor_get(v___x_159_, 1);
lean_inc_ref(v_arg_162_);
v___x_163_ = l_Lean_Expr_appFnCleanup___redArg(v___x_159_);
v___x_164_ = l_Lean_Expr_isApp(v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; 
lean_dec_ref(v___x_163_);
lean_dec_ref(v_arg_162_);
v___x_165_ = lean_box(0);
return v___x_165_;
}
else
{
lean_object* v_arg_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_arg_166_ = lean_ctor_get(v___x_163_, 1);
lean_inc_ref(v_arg_166_);
v___x_167_ = l_Lean_Expr_appFnCleanup___redArg(v___x_163_);
v___x_168_ = ((lean_object*)(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1));
v___x_169_ = l_Lean_Expr_isConstOf(v___x_167_, v___x_168_);
if (v___x_169_ == 0)
{
uint8_t v___x_170_; 
lean_dec_ref(v_arg_162_);
v___x_170_ = l_Lean_Expr_isApp(v___x_167_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; 
lean_dec_ref(v___x_167_);
lean_dec_ref(v_arg_166_);
v___x_171_ = lean_box(0);
return v___x_171_;
}
else
{
lean_object* v_arg_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v_arg_172_ = lean_ctor_get(v___x_167_, 1);
lean_inc_ref(v_arg_172_);
v___x_173_ = l_Lean_Expr_appFnCleanup___redArg(v___x_167_);
v___x_174_ = ((lean_object*)(l_Lean_Meta_Sym_getNatValue_x3f___closed__2));
v___x_175_ = l_Lean_Expr_isConstOf(v___x_173_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = ((lean_object*)(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3));
v___x_177_ = l_Lean_Expr_isConstOf(v___x_173_, v___x_176_);
lean_dec_ref(v___x_173_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
lean_dec_ref(v_arg_172_);
lean_dec_ref(v_arg_166_);
v___x_178_ = lean_box(0);
return v___x_178_;
}
else
{
v_nExpr_142_ = v_arg_172_;
v_vExpr_143_ = v_arg_166_;
goto v___jp_141_;
}
}
else
{
lean_object* v___x_179_; uint8_t v___x_180_; 
lean_dec_ref(v___x_173_);
v___x_179_ = l_Lean_Expr_cleanupAnnotations(v_arg_172_);
v___x_180_ = l_Lean_Expr_isApp(v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; 
lean_dec_ref(v___x_179_);
lean_dec_ref(v_arg_166_);
v___x_181_ = lean_box(0);
return v___x_181_;
}
else
{
lean_object* v_arg_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v_arg_182_ = lean_ctor_get(v___x_179_, 1);
lean_inc_ref(v_arg_182_);
v___x_183_ = l_Lean_Expr_appFnCleanup___redArg(v___x_179_);
v___x_184_ = ((lean_object*)(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4));
v___x_185_ = l_Lean_Expr_isConstOf(v___x_183_, v___x_184_);
lean_dec_ref(v___x_183_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
lean_dec_ref(v_arg_182_);
lean_dec_ref(v_arg_166_);
v___x_186_ = lean_box(0);
return v___x_186_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_182_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v___x_188_; 
lean_dec_ref(v_arg_166_);
v___x_188_ = lean_box(0);
return v___x_188_;
}
else
{
if (lean_obj_tag(v_arg_166_) == 9)
{
lean_object* v_a_189_; 
v_a_189_ = lean_ctor_get(v_arg_166_, 0);
lean_inc_ref(v_a_189_);
lean_dec_ref(v_arg_166_);
if (lean_obj_tag(v_a_189_) == 0)
{
lean_object* v_val_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_200_; 
v_val_190_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_200_ == 0)
{
v___x_192_ = v___x_187_;
v_isShared_193_ = v_isSharedCheck_200_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_val_190_);
lean_dec(v___x_187_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_200_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v_val_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v_val_194_ = lean_ctor_get(v_a_189_, 0);
lean_inc(v_val_194_);
lean_dec_ref(v_a_189_);
v___x_195_ = l_BitVec_ofNat(v_val_190_, v_val_194_);
lean_dec(v_val_194_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v_val_190_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_196_);
v___x_198_ = v___x_192_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
else
{
lean_object* v___x_201_; 
lean_dec_ref(v_a_189_);
lean_dec_ref(v___x_187_);
v___x_201_ = lean_box(0);
return v___x_201_;
}
}
else
{
lean_object* v___x_202_; 
lean_dec_ref(v___x_187_);
lean_dec_ref(v_arg_166_);
v___x_202_ = lean_box(0);
return v___x_202_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_167_);
v_nExpr_142_ = v_arg_166_;
v_vExpr_143_ = v_arg_162_;
goto v___jp_141_;
}
}
}
v___jp_141_:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Meta_Sym_getNatValue_x3f(v_nExpr_142_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v___x_145_; 
lean_dec_ref(v_vExpr_143_);
v___x_145_ = lean_box(0);
return v___x_145_;
}
else
{
lean_object* v_val_146_; lean_object* v___x_147_; 
v_val_146_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_val_146_);
lean_dec_ref(v___x_144_);
v___x_147_ = l_Lean_Meta_Sym_getNatValue_x3f(v_vExpr_143_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v___x_148_; 
lean_dec(v_val_146_);
v___x_148_ = lean_box(0);
return v___x_148_;
}
else
{
lean_object* v_val_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_158_; 
v_val_149_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_158_ == 0)
{
v___x_151_ = v___x_147_;
v_isShared_152_ = v_isSharedCheck_158_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_val_149_);
lean_dec(v___x_147_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_158_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_153_ = l_BitVec_ofNat(v_val_146_, v_val_149_);
lean_dec(v_val_149_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v_val_146_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v___x_154_);
v___x_156_ = v___x_151_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f(lean_object* v_e_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_203_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v___x_205_; 
v___x_205_ = lean_box(0);
return v___x_205_;
}
else
{
lean_object* v_val_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_215_; 
v_val_206_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_215_ == 0)
{
v___x_208_ = v___x_204_;
v_isShared_209_ = v_isSharedCheck_215_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_val_206_);
lean_dec(v___x_204_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_215_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
uint8_t v___x_210_; lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_210_ = lean_uint8_of_nat(v_val_206_);
lean_dec(v_val_206_);
v___x_211_ = lean_box(v___x_210_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_211_);
v___x_213_ = v___x_208_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f(lean_object* v_e_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_216_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v___x_218_; 
v___x_218_ = lean_box(0);
return v___x_218_;
}
else
{
lean_object* v_val_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_228_; 
v_val_219_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_228_ == 0)
{
v___x_221_ = v___x_217_;
v_isShared_222_ = v_isSharedCheck_228_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_val_219_);
lean_dec(v___x_217_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_228_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
uint16_t v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_223_ = lean_uint16_of_nat(v_val_219_);
lean_dec(v_val_219_);
v___x_224_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_224_);
v___x_226_ = v___x_221_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f(lean_object* v_e_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v___x_231_; 
v___x_231_ = lean_box(0);
return v___x_231_;
}
else
{
lean_object* v_val_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_241_; 
v_val_232_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_241_ == 0)
{
v___x_234_ = v___x_230_;
v_isShared_235_ = v_isSharedCheck_241_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_val_232_);
lean_dec(v___x_230_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_241_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
uint32_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_236_ = lean_uint32_of_nat(v_val_232_);
lean_dec(v_val_232_);
v___x_237_ = lean_box_uint32(v___x_236_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_237_);
v___x_239_ = v___x_234_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f(lean_object* v_e_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_242_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v___x_244_; 
v___x_244_ = lean_box(0);
return v___x_244_;
}
else
{
lean_object* v_val_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_254_; 
v_val_245_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_254_ == 0)
{
v___x_247_ = v___x_243_;
v_isShared_248_ = v_isSharedCheck_254_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_val_245_);
lean_dec(v___x_243_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_254_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
uint64_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_249_ = lean_uint64_of_nat(v_val_245_);
lean_dec(v_val_245_);
v___x_250_ = lean_box_uint64(v___x_249_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_250_);
v___x_252_ = v___x_247_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt8Value_x3f(lean_object* v_e_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_255_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v___x_257_; 
v___x_257_ = lean_box(0);
return v___x_257_;
}
else
{
lean_object* v_val_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_267_; 
v_val_258_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_267_ == 0)
{
v___x_260_ = v___x_256_;
v_isShared_261_ = v_isSharedCheck_267_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_val_258_);
lean_dec(v___x_256_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_267_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
uint8_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_262_ = lean_int8_of_int(v_val_258_);
lean_dec(v_val_258_);
v___x_263_ = lean_box(v___x_262_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v___x_263_);
v___x_265_ = v___x_260_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt16Value_x3f(lean_object* v_e_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_268_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v___x_270_; 
v___x_270_ = lean_box(0);
return v___x_270_;
}
else
{
lean_object* v_val_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_280_; 
v_val_271_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_280_ == 0)
{
v___x_273_ = v___x_269_;
v_isShared_274_ = v_isSharedCheck_280_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_val_271_);
lean_dec(v___x_269_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_280_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
uint16_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_275_ = lean_int16_of_int(v_val_271_);
lean_dec(v_val_271_);
v___x_276_ = lean_box(v___x_275_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_276_);
v___x_278_ = v___x_273_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt32Value_x3f(lean_object* v_e_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_281_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v___x_283_; 
v___x_283_ = lean_box(0);
return v___x_283_;
}
else
{
lean_object* v_val_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_293_; 
v_val_284_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_293_ == 0)
{
v___x_286_ = v___x_282_;
v_isShared_287_ = v_isSharedCheck_293_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_val_284_);
lean_dec(v___x_282_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_293_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
uint32_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_288_ = lean_int32_of_int(v_val_284_);
lean_dec(v_val_284_);
v___x_289_ = lean_box_uint32(v___x_288_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_289_);
v___x_291_ = v___x_286_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt64Value_x3f(lean_object* v_e_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_294_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v___x_296_; 
v___x_296_ = lean_box(0);
return v___x_296_;
}
else
{
lean_object* v_val_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_306_; 
v_val_297_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_306_ == 0)
{
v___x_299_ = v___x_295_;
v_isShared_300_ = v_isSharedCheck_306_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_val_297_);
lean_dec(v___x_295_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_306_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
uint64_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_301_ = lean_int64_of_int(v_val_297_);
lean_dec(v_val_297_);
v___x_302_ = lean_box_uint64(v___x_301_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_302_);
v___x_304_ = v___x_299_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFinValue_x3f(lean_object* v_e_310_){
_start:
{
lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_311_ = l_Lean_Expr_cleanupAnnotations(v_e_310_);
v___x_312_ = l_Lean_Expr_isApp(v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; 
lean_dec_ref(v___x_311_);
v___x_313_ = lean_box(0);
return v___x_313_;
}
else
{
lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = l_Lean_Expr_appFnCleanup___redArg(v___x_311_);
v___x_315_ = l_Lean_Expr_isApp(v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
lean_dec_ref(v___x_314_);
v___x_316_ = lean_box(0);
return v___x_316_;
}
else
{
lean_object* v_arg_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v_arg_317_ = lean_ctor_get(v___x_314_, 1);
lean_inc_ref(v_arg_317_);
v___x_318_ = l_Lean_Expr_appFnCleanup___redArg(v___x_314_);
v___x_319_ = l_Lean_Expr_isApp(v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
lean_dec_ref(v___x_318_);
lean_dec_ref(v_arg_317_);
v___x_320_ = lean_box(0);
return v___x_320_;
}
else
{
lean_object* v_arg_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_arg_321_ = lean_ctor_get(v___x_318_, 1);
lean_inc_ref(v_arg_321_);
v___x_322_ = l_Lean_Expr_appFnCleanup___redArg(v___x_318_);
v___x_323_ = ((lean_object*)(l_Lean_Meta_Sym_getNatValue_x3f___closed__2));
v___x_324_ = l_Lean_Expr_isConstOf(v___x_322_, v___x_323_);
lean_dec_ref(v___x_322_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
lean_dec_ref(v_arg_321_);
lean_dec_ref(v_arg_317_);
v___x_325_ = lean_box(0);
return v___x_325_;
}
else
{
lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_326_ = l_Lean_Expr_cleanupAnnotations(v_arg_321_);
v___x_327_ = l_Lean_Expr_isApp(v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; 
lean_dec_ref(v___x_326_);
lean_dec_ref(v_arg_317_);
v___x_328_ = lean_box(0);
return v___x_328_;
}
else
{
lean_object* v_arg_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v_arg_329_ = lean_ctor_get(v___x_326_, 1);
lean_inc_ref(v_arg_329_);
v___x_330_ = l_Lean_Expr_appFnCleanup___redArg(v___x_326_);
v___x_331_ = ((lean_object*)(l_Lean_Meta_Sym_getFinValue_x3f___closed__1));
v___x_332_ = l_Lean_Expr_isConstOf(v___x_330_, v___x_331_);
lean_dec_ref(v___x_330_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
lean_dec_ref(v_arg_329_);
lean_dec_ref(v_arg_317_);
v___x_333_ = lean_box(0);
return v___x_333_;
}
else
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_329_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v___x_335_; 
lean_dec_ref(v_arg_317_);
v___x_335_ = lean_box(0);
return v___x_335_;
}
else
{
if (lean_obj_tag(v_arg_317_) == 9)
{
lean_object* v_a_336_; 
v_a_336_ = lean_ctor_get(v_arg_317_, 0);
lean_inc_ref(v_a_336_);
lean_dec_ref(v_arg_317_);
if (lean_obj_tag(v_a_336_) == 0)
{
lean_object* v_val_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_350_; 
v_val_337_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_350_ == 0)
{
v___x_339_ = v___x_334_;
v_isShared_340_ = v_isSharedCheck_350_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_val_337_);
lean_dec(v___x_334_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_350_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v_val_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_val_341_ = lean_ctor_get(v_a_336_, 0);
lean_inc(v_val_341_);
lean_dec_ref(v_a_336_);
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = lean_nat_dec_eq(v_val_337_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_344_ = lean_nat_mod(v_val_341_, v_val_337_);
lean_dec(v_val_341_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v_val_337_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v___x_345_);
v___x_347_ = v___x_339_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
else
{
lean_object* v___x_349_; 
lean_dec(v_val_341_);
lean_del_object(v___x_339_);
lean_dec(v_val_337_);
v___x_349_ = lean_box(0);
return v___x_349_;
}
}
}
else
{
lean_object* v___x_351_; 
lean_dec_ref(v_a_336_);
lean_dec_ref(v___x_334_);
v___x_351_ = lean_box(0);
return v___x_351_;
}
}
else
{
lean_object* v___x_352_; 
lean_dec_ref(v___x_334_);
lean_dec_ref(v_arg_317_);
v___x_352_ = lean_box(0);
return v___x_352_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCharValue_x3f(lean_object* v_e_357_){
_start:
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = l_Lean_Expr_cleanupAnnotations(v_e_357_);
v___x_359_ = l_Lean_Expr_isApp(v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; 
lean_dec_ref(v___x_358_);
v___x_360_ = lean_box(0);
return v___x_360_;
}
else
{
lean_object* v_arg_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_arg_361_ = lean_ctor_get(v___x_358_, 1);
lean_inc_ref(v_arg_361_);
v___x_362_ = l_Lean_Expr_appFnCleanup___redArg(v___x_358_);
v___x_363_ = ((lean_object*)(l_Lean_Meta_Sym_getCharValue_x3f___closed__1));
v___x_364_ = l_Lean_Expr_isConstOf(v___x_362_, v___x_363_);
lean_dec_ref(v___x_362_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
lean_dec_ref(v_arg_361_);
v___x_365_ = lean_box(0);
return v___x_365_;
}
else
{
if (lean_obj_tag(v_arg_361_) == 9)
{
lean_object* v_a_366_; 
v_a_366_ = lean_ctor_get(v_arg_361_, 0);
lean_inc_ref(v_a_366_);
lean_dec_ref(v_arg_361_);
if (lean_obj_tag(v_a_366_) == 0)
{
lean_object* v_val_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_376_; 
v_val_367_ = lean_ctor_get(v_a_366_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v_a_366_);
if (v_isSharedCheck_376_ == 0)
{
v___x_369_ = v_a_366_;
v_isShared_370_ = v_isSharedCheck_376_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_val_367_);
lean_dec(v_a_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_376_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
uint32_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_371_ = l_Char_ofNat(v_val_367_);
lean_dec(v_val_367_);
v___x_372_ = lean_box_uint32(v___x_371_);
if (v_isShared_370_ == 0)
{
lean_ctor_set_tag(v___x_369_, 1);
lean_ctor_set(v___x_369_, 0, v___x_372_);
v___x_374_ = v___x_369_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
else
{
lean_object* v___x_377_; 
lean_dec_ref(v_a_366_);
v___x_377_ = lean_box(0);
return v___x_377_;
}
}
else
{
lean_object* v___x_378_; 
lean_dec_ref(v_arg_361_);
v___x_378_ = lean_box(0);
return v___x_378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getStringValue_x3f(lean_object* v_e_379_){
_start:
{
if (lean_obj_tag(v_e_379_) == 9)
{
lean_object* v_a_380_; 
v_a_380_ = lean_ctor_get(v_e_379_, 0);
lean_inc_ref(v_a_380_);
lean_dec_ref(v_e_379_);
if (lean_obj_tag(v_a_380_) == 1)
{
lean_object* v_val_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
v_val_381_ = lean_ctor_get(v_a_380_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v_a_380_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v_a_380_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_val_381_);
lean_dec(v_a_380_);
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
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_val_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
else
{
lean_object* v___x_389_; 
lean_dec_ref(v_a_380_);
v___x_389_ = lean_box(0);
return v___x_389_;
}
}
else
{
lean_object* v___x_390_; 
lean_dec_ref(v_e_379_);
v___x_390_ = lean_box(0);
return v___x_390_;
}
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Rat(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Rat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Init_Data_Rat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Rat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_LitValues(builtin);
}
#ifdef __cplusplus
}
#endif
