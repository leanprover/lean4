// Lean compiler output
// Module: Lean.Meta.HasNotBit
// Imports: public import Lean.Meta.Basic import Lean.Meta.MatchUtil
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
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchNe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_reflBoolTrue;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_mkHasNotBit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_mkHasNotBit___closed__0 = (const lean_object*)&l_mkHasNotBit___closed__0_value;
static const lean_string_object l_mkHasNotBit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "hasNotBit"};
static const lean_object* l_mkHasNotBit___closed__1 = (const lean_object*)&l_mkHasNotBit___closed__1_value;
static const lean_ctor_object l_mkHasNotBit___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkHasNotBit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_mkHasNotBit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_mkHasNotBit___closed__2_value_aux_0),((lean_object*)&l_mkHasNotBit___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 117, 142, 139, 222, 16, 37, 88)}};
static const lean_object* l_mkHasNotBit___closed__2 = (const lean_object*)&l_mkHasNotBit___closed__2_value;
static lean_once_cell_t l_mkHasNotBit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBit___closed__3;
LEAN_EXPORT lean_object* l_mkHasNotBit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkHasNotBit___boxed(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00mkHasNotBitProof_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00mkHasNotBitProof_spec__0___closed__0 = (const lean_object*)&l_panic___at___00mkHasNotBitProof_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00mkHasNotBitProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00mkHasNotBitProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_mkHasNotBitProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ne_of_beq_eq_false"};
static const lean_object* l_mkHasNotBitProof___closed__0 = (const lean_object*)&l_mkHasNotBitProof___closed__0_value;
static const lean_ctor_object l_mkHasNotBitProof___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkHasNotBit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_mkHasNotBitProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_mkHasNotBitProof___closed__1_value_aux_0),((lean_object*)&l_mkHasNotBitProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 213, 144, 137, 140, 238, 73, 24)}};
static const lean_object* l_mkHasNotBitProof___closed__1 = (const lean_object*)&l_mkHasNotBitProof___closed__1_value;
static lean_once_cell_t l_mkHasNotBitProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBitProof___closed__2;
static const lean_string_object l_mkHasNotBitProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_mkHasNotBitProof___closed__3 = (const lean_object*)&l_mkHasNotBitProof___closed__3_value;
static const lean_string_object l_mkHasNotBitProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_mkHasNotBitProof___closed__4 = (const lean_object*)&l_mkHasNotBitProof___closed__4_value;
static const lean_ctor_object l_mkHasNotBitProof___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkHasNotBitProof___closed__3_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_mkHasNotBitProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_mkHasNotBitProof___closed__5_value_aux_0),((lean_object*)&l_mkHasNotBitProof___closed__4_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_mkHasNotBitProof___closed__5 = (const lean_object*)&l_mkHasNotBitProof___closed__5_value;
static lean_once_cell_t l_mkHasNotBitProof___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBitProof___closed__6;
static lean_once_cell_t l_mkHasNotBitProof___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBitProof___closed__7;
static lean_once_cell_t l_mkHasNotBitProof___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBitProof___closed__8;
static const lean_string_object l_mkHasNotBitProof___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_mkHasNotBitProof___closed__9 = (const lean_object*)&l_mkHasNotBitProof___closed__9_value;
static const lean_ctor_object l_mkHasNotBitProof___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkHasNotBitProof___closed__9_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_mkHasNotBitProof___closed__10 = (const lean_object*)&l_mkHasNotBitProof___closed__10_value;
static lean_once_cell_t l_mkHasNotBitProof___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBitProof___closed__11;
static const lean_string_object l_mkHasNotBitProof___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_mkHasNotBitProof___closed__12 = (const lean_object*)&l_mkHasNotBitProof___closed__12_value;
static const lean_ctor_object l_mkHasNotBitProof___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkHasNotBitProof___closed__9_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_mkHasNotBitProof___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_mkHasNotBitProof___closed__13_value_aux_0),((lean_object*)&l_mkHasNotBitProof___closed__12_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_mkHasNotBitProof___closed__13 = (const lean_object*)&l_mkHasNotBitProof___closed__13_value;
static lean_once_cell_t l_mkHasNotBitProof___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBitProof___closed__14;
static lean_once_cell_t l_mkHasNotBitProof___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBitProof___closed__15;
static const lean_string_object l_mkHasNotBitProof___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Meta.HasNotBit"};
static const lean_object* l_mkHasNotBitProof___closed__16 = (const lean_object*)&l_mkHasNotBitProof___closed__16_value;
static const lean_string_object l_mkHasNotBitProof___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "mkHasNotBitProof"};
static const lean_object* l_mkHasNotBitProof___closed__17 = (const lean_object*)&l_mkHasNotBitProof___closed__17_value;
static const lean_string_object l_mkHasNotBitProof___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_mkHasNotBitProof___closed__18 = (const lean_object*)&l_mkHasNotBitProof___closed__18_value;
static lean_once_cell_t l_mkHasNotBitProof___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkHasNotBitProof___closed__19;
LEAN_EXPORT lean_object* l_mkHasNotBitProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkHasNotBitProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_isHasNotBit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00refutableHasNotBit_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00refutableHasNotBit_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_refutableHasNotBit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "eq_of_beq_eq_true"};
static const lean_object* l_refutableHasNotBit_x3f___closed__0 = (const lean_object*)&l_refutableHasNotBit_x3f___closed__0_value;
static const lean_ctor_object l_refutableHasNotBit_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkHasNotBit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_refutableHasNotBit_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_refutableHasNotBit_x3f___closed__1_value_aux_0),((lean_object*)&l_refutableHasNotBit_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 61, 33, 216, 114, 139, 90, 184)}};
static const lean_object* l_refutableHasNotBit_x3f___closed__1 = (const lean_object*)&l_refutableHasNotBit_x3f___closed__1_value;
static lean_once_cell_t l_refutableHasNotBit_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_refutableHasNotBit_x3f___closed__2;
static const lean_string_object l_refutableHasNotBit_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "refutableHasNotBit\?"};
static const lean_object* l_refutableHasNotBit_x3f___closed__3 = (const lean_object*)&l_refutableHasNotBit_x3f___closed__3_value;
static lean_once_cell_t l_refutableHasNotBit_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_refutableHasNotBit_x3f___closed__4;
LEAN_EXPORT lean_object* l_refutableHasNotBit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_refutableHasNotBit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0(lean_object* v_as_1_, size_t v_sz_2_, size_t v_i_3_, lean_object* v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_usize_dec_lt(v_i_3_, v_sz_2_);
if (v___x_5_ == 0)
{
return v_b_4_;
}
else
{
lean_object* v_a_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; size_t v___x_10_; size_t v___x_11_; 
v_a_6_ = lean_array_uget_borrowed(v_as_1_, v_i_3_);
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_nat_shiftl(v___x_7_, v_a_6_);
v___x_9_ = lean_nat_lor(v_b_4_, v___x_8_);
lean_dec(v___x_8_);
lean_dec(v_b_4_);
v___x_10_ = ((size_t)1ULL);
v___x_11_ = lean_usize_add(v_i_3_, v___x_10_);
v_i_3_ = v___x_11_;
v_b_4_ = v___x_9_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0___boxed(lean_object* v_as_13_, lean_object* v_sz_14_, lean_object* v_i_15_, lean_object* v_b_16_){
_start:
{
size_t v_sz_boxed_17_; size_t v_i_boxed_18_; lean_object* v_res_19_; 
v_sz_boxed_17_ = lean_unbox_usize(v_sz_14_);
lean_dec(v_sz_14_);
v_i_boxed_18_ = lean_unbox_usize(v_i_15_);
lean_dec(v_i_15_);
v_res_19_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0(v_as_13_, v_sz_boxed_17_, v_i_boxed_18_, v_b_16_);
lean_dec_ref(v_as_13_);
return v_res_19_;
}
}
static lean_object* _init_l_mkHasNotBit___closed__3(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = lean_box(0);
v___x_26_ = ((lean_object*)(l_mkHasNotBit___closed__2));
v___x_27_ = l_Lean_mkConst(v___x_26_, v___x_25_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_mkHasNotBit(lean_object* v_e_28_, lean_object* v_ns_29_){
_start:
{
lean_object* v_mask_30_; size_t v_sz_31_; size_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_mask_30_ = lean_unsigned_to_nat(0u);
v_sz_31_ = lean_array_size(v_ns_29_);
v___x_32_ = ((size_t)0ULL);
v___x_33_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0(v_ns_29_, v_sz_31_, v___x_32_, v_mask_30_);
v___x_34_ = lean_obj_once(&l_mkHasNotBit___closed__3, &l_mkHasNotBit___closed__3_once, _init_l_mkHasNotBit___closed__3);
v___x_35_ = l_Lean_mkRawNatLit(v___x_33_);
v___x_36_ = l_Lean_mkAppB(v___x_34_, v___x_35_, v_e_28_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_mkHasNotBit___boxed(lean_object* v_e_37_, lean_object* v_ns_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_mkHasNotBit(v_e_37_, v_ns_38_);
lean_dec_ref(v_ns_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00mkHasNotBitProof_spec__0(lean_object* v_msg_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___f_47_; lean_object* v___x_344__overap_48_; lean_object* v___x_49_; 
v___f_47_ = ((lean_object*)(l_panic___at___00mkHasNotBitProof_spec__0___closed__0));
v___x_344__overap_48_ = lean_panic_fn(v___f_47_, v_msg_41_);
lean_inc(v___y_45_);
lean_inc_ref(v___y_44_);
lean_inc(v___y_43_);
lean_inc_ref(v___y_42_);
v___x_49_ = lean_apply_5(v___x_344__overap_48_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, lean_box(0));
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00mkHasNotBitProof_spec__0___boxed(lean_object* v_msg_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_panic___at___00mkHasNotBitProof_spec__0(v_msg_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
return v_res_56_;
}
}
static lean_object* _init_l_mkHasNotBitProof___closed__2(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_box(0);
v___x_62_ = ((lean_object*)(l_mkHasNotBitProof___closed__1));
v___x_63_ = l_Lean_mkConst(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l_mkHasNotBitProof___closed__6(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(1u);
v___x_70_ = l_Lean_Level_ofNat(v___x_69_);
return v___x_70_;
}
}
static lean_object* _init_l_mkHasNotBitProof___closed__7(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_box(0);
v___x_72_ = lean_obj_once(&l_mkHasNotBitProof___closed__6, &l_mkHasNotBitProof___closed__6_once, _init_l_mkHasNotBitProof___closed__6);
v___x_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
return v___x_73_;
}
}
static lean_object* _init_l_mkHasNotBitProof___closed__8(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_74_ = lean_obj_once(&l_mkHasNotBitProof___closed__7, &l_mkHasNotBitProof___closed__7_once, _init_l_mkHasNotBitProof___closed__7);
v___x_75_ = ((lean_object*)(l_mkHasNotBitProof___closed__5));
v___x_76_ = l_Lean_mkConst(v___x_75_, v___x_74_);
return v___x_76_;
}
}
static lean_object* _init_l_mkHasNotBitProof___closed__11(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_box(0);
v___x_81_ = ((lean_object*)(l_mkHasNotBitProof___closed__10));
v___x_82_ = l_Lean_mkConst(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_l_mkHasNotBitProof___closed__14(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_box(0);
v___x_88_ = ((lean_object*)(l_mkHasNotBitProof___closed__13));
v___x_89_ = l_Lean_mkConst(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l_mkHasNotBitProof___closed__15(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_90_ = lean_obj_once(&l_mkHasNotBitProof___closed__14, &l_mkHasNotBitProof___closed__14_once, _init_l_mkHasNotBitProof___closed__14);
v___x_91_ = lean_obj_once(&l_mkHasNotBitProof___closed__11, &l_mkHasNotBitProof___closed__11_once, _init_l_mkHasNotBitProof___closed__11);
v___x_92_ = lean_obj_once(&l_mkHasNotBitProof___closed__8, &l_mkHasNotBitProof___closed__8_once, _init_l_mkHasNotBitProof___closed__8);
v___x_93_ = l_Lean_mkAppB(v___x_92_, v___x_91_, v___x_90_);
return v___x_93_;
}
}
static lean_object* _init_l_mkHasNotBitProof___closed__19(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_97_ = ((lean_object*)(l_mkHasNotBitProof___closed__18));
v___x_98_ = lean_unsigned_to_nat(57u);
v___x_99_ = lean_unsigned_to_nat(33u);
v___x_100_ = ((lean_object*)(l_mkHasNotBitProof___closed__17));
v___x_101_ = ((lean_object*)(l_mkHasNotBitProof___closed__16));
v___x_102_ = l_mkPanicMessageWithDecl(v___x_101_, v___x_100_, v___x_99_, v___x_98_, v___x_97_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_mkHasNotBitProof(lean_object* v_e_103_, lean_object* v_ns_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = l_mkHasNotBit(v_e_103_, v_ns_104_);
v___x_111_ = l_Lean_Meta_matchNe_x3f(v___x_110_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_128_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_128_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_128_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_128_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
if (lean_obj_tag(v_a_112_) == 1)
{
lean_object* v_val_116_; lean_object* v_snd_117_; lean_object* v_fst_118_; lean_object* v_snd_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v_val_116_ = lean_ctor_get(v_a_112_, 0);
lean_inc(v_val_116_);
lean_dec_ref(v_a_112_);
v_snd_117_ = lean_ctor_get(v_val_116_, 1);
lean_inc(v_snd_117_);
lean_dec(v_val_116_);
v_fst_118_ = lean_ctor_get(v_snd_117_, 0);
lean_inc(v_fst_118_);
v_snd_119_ = lean_ctor_get(v_snd_117_, 1);
lean_inc(v_snd_119_);
lean_dec(v_snd_117_);
v___x_120_ = lean_obj_once(&l_mkHasNotBitProof___closed__2, &l_mkHasNotBitProof___closed__2_once, _init_l_mkHasNotBitProof___closed__2);
v___x_121_ = lean_obj_once(&l_mkHasNotBitProof___closed__15, &l_mkHasNotBitProof___closed__15_once, _init_l_mkHasNotBitProof___closed__15);
v___x_122_ = l_Lean_mkApp3(v___x_120_, v_fst_118_, v_snd_119_, v___x_121_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_122_);
v___x_124_ = v___x_114_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_del_object(v___x_114_);
lean_dec(v_a_112_);
v___x_126_ = lean_obj_once(&l_mkHasNotBitProof___closed__19, &l_mkHasNotBitProof___closed__19_once, _init_l_mkHasNotBitProof___closed__19);
v___x_127_ = l_panic___at___00mkHasNotBitProof_spec__0(v___x_126_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
return v___x_127_;
}
}
}
else
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_136_; 
v_a_129_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_136_ == 0)
{
v___x_131_ = v___x_111_;
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___x_111_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_a_129_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_mkHasNotBitProof___boxed(lean_object* v_e_137_, lean_object* v_ns_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_mkHasNotBitProof(v_e_137_, v_ns_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
lean_dec_ref(v_ns_138_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_isHasNotBit_x3f(lean_object* v_e_145_){
_start:
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = l_Lean_Expr_cleanupAnnotations(v_e_145_);
v___x_147_ = l_Lean_Expr_isApp(v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; 
lean_dec_ref(v___x_146_);
v___x_148_ = lean_box(0);
return v___x_148_;
}
else
{
lean_object* v_arg_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v_arg_149_ = lean_ctor_get(v___x_146_, 1);
lean_inc_ref(v_arg_149_);
v___x_150_ = l_Lean_Expr_appFnCleanup___redArg(v___x_146_);
v___x_151_ = l_Lean_Expr_isApp(v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; 
lean_dec_ref(v___x_150_);
lean_dec_ref(v_arg_149_);
v___x_152_ = lean_box(0);
return v___x_152_;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_153_ = l_Lean_Expr_appFnCleanup___redArg(v___x_150_);
v___x_154_ = ((lean_object*)(l_mkHasNotBit___closed__2));
v___x_155_ = l_Lean_Expr_isConstOf(v___x_153_, v___x_154_);
lean_dec_ref(v___x_153_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; 
lean_dec_ref(v_arg_149_);
v___x_156_ = lean_box(0);
return v___x_156_;
}
else
{
lean_object* v___x_157_; 
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v_arg_149_);
return v___x_157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00refutableHasNotBit_x3f_spec__0(lean_object* v_msg_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v___f_164_; lean_object* v___x_1859__overap_165_; lean_object* v___x_166_; 
v___f_164_ = ((lean_object*)(l_panic___at___00mkHasNotBitProof_spec__0___closed__0));
v___x_1859__overap_165_ = lean_panic_fn(v___f_164_, v_msg_158_);
lean_inc(v___y_162_);
lean_inc_ref(v___y_161_);
lean_inc(v___y_160_);
lean_inc_ref(v___y_159_);
v___x_166_ = lean_apply_5(v___x_1859__overap_165_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, lean_box(0));
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00refutableHasNotBit_x3f_spec__0___boxed(lean_object* v_msg_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_panic___at___00refutableHasNotBit_x3f_spec__0(v_msg_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
return v_res_173_;
}
}
static lean_object* _init_l_refutableHasNotBit_x3f___closed__2(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_box(0);
v___x_179_ = ((lean_object*)(l_refutableHasNotBit_x3f___closed__1));
v___x_180_ = l_Lean_mkConst(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l_refutableHasNotBit_x3f___closed__4(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_182_ = ((lean_object*)(l_mkHasNotBitProof___closed__18));
v___x_183_ = lean_unsigned_to_nat(84u);
v___x_184_ = lean_unsigned_to_nat(53u);
v___x_185_ = ((lean_object*)(l_refutableHasNotBit_x3f___closed__3));
v___x_186_ = ((lean_object*)(l_mkHasNotBitProof___closed__16));
v___x_187_ = l_mkPanicMessageWithDecl(v___x_186_, v___x_185_, v___x_184_, v___x_183_, v___x_182_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_refutableHasNotBit_x3f(lean_object* v_e_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_188_, v_a_190_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_282_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_282_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_282_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_282_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_204_ = l_Lean_Expr_cleanupAnnotations(v_a_195_);
v___x_205_ = l_Lean_Expr_isApp(v___x_204_);
if (v___x_205_ == 0)
{
lean_dec_ref(v___x_204_);
goto v___jp_199_;
}
else
{
lean_object* v_arg_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_arg_206_ = lean_ctor_get(v___x_204_, 1);
lean_inc_ref(v_arg_206_);
v___x_207_ = l_Lean_Expr_appFnCleanup___redArg(v___x_204_);
v___x_208_ = l_Lean_Expr_isApp(v___x_207_);
if (v___x_208_ == 0)
{
lean_dec_ref(v___x_207_);
lean_dec_ref(v_arg_206_);
goto v___jp_199_;
}
else
{
lean_object* v_arg_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_arg_209_ = lean_ctor_get(v___x_207_, 1);
lean_inc_ref(v_arg_209_);
v___x_210_ = l_Lean_Expr_appFnCleanup___redArg(v___x_207_);
v___x_211_ = ((lean_object*)(l_mkHasNotBit___closed__2));
v___x_212_ = l_Lean_Expr_isConstOf(v___x_210_, v___x_211_);
lean_dec_ref(v___x_210_);
if (v___x_212_ == 0)
{
lean_dec_ref(v_arg_209_);
lean_dec_ref(v_arg_206_);
goto v___jp_199_;
}
else
{
lean_object* v___x_213_; 
lean_del_object(v___x_197_);
lean_inc(v_a_192_);
lean_inc_ref(v_a_191_);
lean_inc(v_a_190_);
lean_inc_ref(v_a_189_);
v___x_213_ = lean_whnf(v_arg_206_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_273_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_273_ == 0)
{
v___x_216_ = v___x_213_;
v_isShared_217_ = v_isSharedCheck_273_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_213_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_273_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
uint8_t v___x_218_; 
v___x_218_ = l_Lean_Expr_hasFVar(v_a_214_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
lean_del_object(v___x_216_);
v___x_219_ = lean_obj_once(&l_mkHasNotBit___closed__3, &l_mkHasNotBit___closed__3_once, _init_l_mkHasNotBit___closed__3);
v___x_220_ = l_Lean_mkAppB(v___x_219_, v_arg_209_, v_a_214_);
v___x_221_ = l_Lean_Meta_matchNe_x3f(v___x_220_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_a_222_);
lean_dec_ref(v___x_221_);
if (lean_obj_tag(v_a_222_) == 1)
{
lean_object* v_val_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_258_; 
v_val_223_ = lean_ctor_get(v_a_222_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v_a_222_);
if (v_isSharedCheck_258_ == 0)
{
v___x_225_ = v_a_222_;
v_isShared_226_ = v_isSharedCheck_258_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_val_223_);
lean_dec(v_a_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_258_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v_snd_227_; lean_object* v_fst_228_; lean_object* v_snd_229_; lean_object* v___x_230_; 
v_snd_227_ = lean_ctor_get(v_val_223_, 1);
lean_inc(v_snd_227_);
lean_dec(v_val_223_);
v_fst_228_ = lean_ctor_get(v_snd_227_, 0);
lean_inc(v_fst_228_);
v_snd_229_ = lean_ctor_get(v_snd_227_, 1);
lean_inc(v_snd_229_);
lean_dec(v_snd_227_);
lean_inc(v_snd_229_);
lean_inc(v_fst_228_);
v___x_230_ = l_Lean_Meta_isExprDefEq(v_fst_228_, v_snd_229_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_249_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_249_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_249_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_249_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
uint8_t v___x_235_; 
v___x_235_ = lean_unbox(v_a_231_);
lean_dec(v_a_231_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_238_; 
lean_dec(v_snd_229_);
lean_dec(v_fst_228_);
lean_del_object(v___x_225_);
v___x_236_ = lean_box(0);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_236_);
v___x_238_ = v___x_233_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_240_ = lean_obj_once(&l_refutableHasNotBit_x3f___closed__2, &l_refutableHasNotBit_x3f___closed__2_once, _init_l_refutableHasNotBit_x3f___closed__2);
v___x_241_ = l_Lean_reflBoolTrue;
v___x_242_ = l_Lean_mkApp3(v___x_240_, v_fst_228_, v_snd_229_, v___x_241_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_242_);
v___x_244_ = v___x_225_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_248_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_246_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_244_);
v___x_246_ = v___x_233_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
lean_dec(v_snd_229_);
lean_dec(v_fst_228_);
lean_del_object(v___x_225_);
v_a_250_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_230_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_230_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec(v_a_222_);
v___x_259_ = lean_obj_once(&l_refutableHasNotBit_x3f___closed__4, &l_refutableHasNotBit_x3f___closed__4_once, _init_l_refutableHasNotBit_x3f___closed__4);
v___x_260_ = l_panic___at___00refutableHasNotBit_x3f_spec__0(v___x_259_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
return v___x_260_;
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
v_a_261_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_221_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_221_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
else
{
lean_object* v___x_269_; lean_object* v___x_271_; 
lean_dec(v_a_214_);
lean_dec_ref(v_arg_209_);
v___x_269_ = lean_box(0);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_269_);
v___x_271_ = v___x_216_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec_ref(v_arg_209_);
v_a_274_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_213_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_213_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
v___jp_199_:
{
lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_200_ = lean_box(0);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_200_);
v___x_202_ = v___x_197_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
v_a_283_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_194_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_194_);
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
}
LEAN_EXPORT lean_object* l_refutableHasNotBit_x3f___boxed(lean_object* v_e_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_refutableHasNotBit_x3f(v_e_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
return v_res_297_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_MatchUtil(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_HasNotBit(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_HasNotBit(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_HasNotBit(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_HasNotBit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_HasNotBit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_HasNotBit(builtin);
}
#ifdef __cplusplus
}
#endif
