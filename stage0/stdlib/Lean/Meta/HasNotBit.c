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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Level_ofNat(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchNe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_reflBoolTrue;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkHasNotBit_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkHasNotBit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkHasNotBit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_mkHasNotBit___closed__0 = (const lean_object*)&l_Lean_mkHasNotBit___closed__0_value;
static const lean_string_object l_Lean_mkHasNotBit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "hasNotBit"};
static const lean_object* l_Lean_mkHasNotBit___closed__1 = (const lean_object*)&l_Lean_mkHasNotBit___closed__1_value;
static const lean_ctor_object l_Lean_mkHasNotBit___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkHasNotBit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_mkHasNotBit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkHasNotBit___closed__2_value_aux_0),((lean_object*)&l_Lean_mkHasNotBit___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 117, 142, 139, 222, 16, 37, 88)}};
static const lean_object* l_Lean_mkHasNotBit___closed__2 = (const lean_object*)&l_Lean_mkHasNotBit___closed__2_value;
static lean_once_cell_t l_Lean_mkHasNotBit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkHasNotBit___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkHasNotBit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHasNotBit___boxed(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_mkHasNotBitProof_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_mkHasNotBitProof_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_mkHasNotBitProof_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkHasNotBitProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkHasNotBitProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkHasNotBitProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ne_of_beq_eq_false"};
static const lean_object* l_Lean_mkHasNotBitProof___closed__0 = (const lean_object*)&l_Lean_mkHasNotBitProof___closed__0_value;
static const lean_ctor_object l_Lean_mkHasNotBitProof___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkHasNotBit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_mkHasNotBitProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkHasNotBitProof___closed__1_value_aux_0),((lean_object*)&l_Lean_mkHasNotBitProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 213, 144, 137, 140, 238, 73, 24)}};
static const lean_object* l_Lean_mkHasNotBitProof___closed__1 = (const lean_object*)&l_Lean_mkHasNotBitProof___closed__1_value;
static lean_once_cell_t l_Lean_mkHasNotBitProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkHasNotBitProof___closed__2;
static const lean_string_object l_Lean_mkHasNotBitProof___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_mkHasNotBitProof___closed__3 = (const lean_object*)&l_Lean_mkHasNotBitProof___closed__3_value;
static const lean_string_object l_Lean_mkHasNotBitProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_mkHasNotBitProof___closed__4 = (const lean_object*)&l_Lean_mkHasNotBitProof___closed__4_value;
static const lean_ctor_object l_Lean_mkHasNotBitProof___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkHasNotBitProof___closed__3_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_mkHasNotBitProof___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkHasNotBitProof___closed__5_value_aux_0),((lean_object*)&l_Lean_mkHasNotBitProof___closed__4_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_mkHasNotBitProof___closed__5 = (const lean_object*)&l_Lean_mkHasNotBitProof___closed__5_value;
static lean_once_cell_t l_Lean_mkHasNotBitProof___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkHasNotBitProof___closed__6;
static lean_once_cell_t l_Lean_mkHasNotBitProof___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkHasNotBitProof___closed__7;
static lean_once_cell_t l_Lean_mkHasNotBitProof___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkHasNotBitProof___closed__8;
static const lean_string_object l_Lean_mkHasNotBitProof___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_mkHasNotBitProof___closed__9 = (const lean_object*)&l_Lean_mkHasNotBitProof___closed__9_value;
static const lean_ctor_object l_Lean_mkHasNotBitProof___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkHasNotBitProof___closed__9_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_mkHasNotBitProof___closed__10 = (const lean_object*)&l_Lean_mkHasNotBitProof___closed__10_value;
static lean_once_cell_t l_Lean_mkHasNotBitProof___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkHasNotBitProof___closed__11;
static const lean_string_object l_Lean_mkHasNotBitProof___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_mkHasNotBitProof___closed__12 = (const lean_object*)&l_Lean_mkHasNotBitProof___closed__12_value;
static const lean_ctor_object l_Lean_mkHasNotBitProof___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkHasNotBitProof___closed__9_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_mkHasNotBitProof___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkHasNotBitProof___closed__13_value_aux_0),((lean_object*)&l_Lean_mkHasNotBitProof___closed__12_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_mkHasNotBitProof___closed__13 = (const lean_object*)&l_Lean_mkHasNotBitProof___closed__13_value;
static lean_once_cell_t l_Lean_mkHasNotBitProof___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkHasNotBitProof___closed__14;
static lean_once_cell_t l_Lean_mkHasNotBitProof___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkHasNotBitProof___closed__15;
static const lean_string_object l_Lean_mkHasNotBitProof___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Meta.HasNotBit"};
static const lean_object* l_Lean_mkHasNotBitProof___closed__16 = (const lean_object*)&l_Lean_mkHasNotBitProof___closed__16_value;
static const lean_string_object l_Lean_mkHasNotBitProof___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.mkHasNotBitProof"};
static const lean_object* l_Lean_mkHasNotBitProof___closed__17 = (const lean_object*)&l_Lean_mkHasNotBitProof___closed__17_value;
static const lean_string_object l_Lean_mkHasNotBitProof___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_mkHasNotBitProof___closed__18 = (const lean_object*)&l_Lean_mkHasNotBitProof___closed__18_value;
static lean_once_cell_t l_Lean_mkHasNotBitProof___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkHasNotBitProof___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkHasNotBitProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHasNotBitProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isHasNotBit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_refutableHasNotBit_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_refutableHasNotBit_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_refutableHasNotBit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "eq_of_beq_eq_true"};
static const lean_object* l_Lean_refutableHasNotBit_x3f___closed__0 = (const lean_object*)&l_Lean_refutableHasNotBit_x3f___closed__0_value;
static const lean_ctor_object l_Lean_refutableHasNotBit_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkHasNotBit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_refutableHasNotBit_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_refutableHasNotBit_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_refutableHasNotBit_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 61, 33, 216, 114, 139, 90, 184)}};
static const lean_object* l_Lean_refutableHasNotBit_x3f___closed__1 = (const lean_object*)&l_Lean_refutableHasNotBit_x3f___closed__1_value;
static lean_once_cell_t l_Lean_refutableHasNotBit_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_refutableHasNotBit_x3f___closed__2;
static const lean_string_object l_Lean_refutableHasNotBit_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.refutableHasNotBit\?"};
static const lean_object* l_Lean_refutableHasNotBit_x3f___closed__3 = (const lean_object*)&l_Lean_refutableHasNotBit_x3f___closed__3_value;
static lean_once_cell_t l_Lean_refutableHasNotBit_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_refutableHasNotBit_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_refutableHasNotBit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_refutableHasNotBit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkHasNotBit_spec__0(lean_object* v_as_1_, size_t v_sz_2_, size_t v_i_3_, lean_object* v_b_4_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkHasNotBit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1_ = stack[0].m_obj;
size_t v_sz_2_ = stack[1].m_num;
size_t v_i_3_ = stack[2].m_num;
lean_object* v_b_4_ = stack[3].m_obj;
lean_object* v_res_13_;
v_res_13_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkHasNotBit_spec__0(v_as_1_, v_sz_2_, v_i_3_, v_b_4_);
stack->m_obj
 = v_res_13_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkHasNotBit_spec__0___boxed(lean_object* v_as_14_, lean_object* v_sz_15_, lean_object* v_i_16_, lean_object* v_b_17_){
_start:
{
size_t v_sz_boxed_18_; size_t v_i_boxed_19_; lean_object* v_res_20_; 
v_sz_boxed_18_ = lean_unbox_usize(v_sz_15_);
lean_dec(v_sz_15_);
v_i_boxed_19_ = lean_unbox_usize(v_i_16_);
lean_dec(v_i_16_);
v_res_20_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkHasNotBit_spec__0(v_as_14_, v_sz_boxed_18_, v_i_boxed_19_, v_b_17_);
lean_dec_ref(v_as_14_);
return v_res_20_;
}
}
static lean_object* _init_l_Lean_mkHasNotBit___closed__3(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_26_ = lean_box(0);
v___x_27_ = ((lean_object*)(l_Lean_mkHasNotBit___closed__2));
v___x_28_ = l_Lean_mkConst(v___x_27_, v___x_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHasNotBit(lean_object* v_e_29_, lean_object* v_ns_30_){
_start:
{
lean_object* v_mask_31_; size_t v_sz_32_; size_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v_mask_31_ = lean_unsigned_to_nat(0u);
v_sz_32_ = lean_array_size(v_ns_30_);
v___x_33_ = ((size_t)0ULL);
v___x_34_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkHasNotBit_spec__0(v_ns_30_, v_sz_32_, v___x_33_, v_mask_31_);
v___x_35_ = lean_obj_once(&l_Lean_mkHasNotBit___closed__3, &l_Lean_mkHasNotBit___closed__3_once, _init_l_Lean_mkHasNotBit___closed__3);
v___x_36_ = l_Lean_mkRawNatLit(v___x_34_);
v___x_37_ = l_Lean_mkAppB(v___x_35_, v___x_36_, v_e_29_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHasNotBit___boxed(lean_object* v_e_38_, lean_object* v_ns_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_mkHasNotBit(v_e_38_, v_ns_39_);
lean_dec_ref(v_ns_39_);
return v_res_40_;
}
}
lean_object* l_panic___at___00Lean_mkHasNotBitProof_spec__0(lean_object* v_msg_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v___f_48_; lean_object* v___x_340__overap_49_; lean_object* v___x_50_; 
v___f_48_ = ((lean_object*)(l_panic___at___00Lean_mkHasNotBitProof_spec__0___closed__0));
v___x_340__overap_49_ = lean_panic_fn_borrowed(v___f_48_, v_msg_42_);
lean_inc(v___y_46_);
lean_inc_ref(v___y_45_);
lean_inc(v___y_44_);
lean_inc_ref(v___y_43_);
v___x_50_ = lean_apply_5(v___x_340__overap_49_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, lean_box(0));
return v___x_50_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_mkHasNotBitProof_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_42_ = stack[0].m_obj;
lean_object* v___y_43_ = stack[1].m_obj;
lean_object* v___y_44_ = stack[2].m_obj;
lean_object* v___y_45_ = stack[3].m_obj;
lean_object* v___y_46_ = stack[4].m_obj;
lean_object* v_res_51_;
v_res_51_ = l_panic___at___00Lean_mkHasNotBitProof_spec__0(v_msg_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_);
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkHasNotBitProof_spec__0___boxed(lean_object* v_msg_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_panic___at___00Lean_mkHasNotBitProof_spec__0(v_msg_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
return v_res_58_;
}
}
static lean_object* _init_l_Lean_mkHasNotBitProof___closed__2(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_box(0);
v___x_64_ = ((lean_object*)(l_Lean_mkHasNotBitProof___closed__1));
v___x_65_ = l_Lean_mkConst(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_mkHasNotBitProof___closed__6(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(1u);
v___x_72_ = l_Lean_Level_ofNat(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_mkHasNotBitProof___closed__7(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = lean_box(0);
v___x_74_ = lean_obj_once(&l_Lean_mkHasNotBitProof___closed__6, &l_Lean_mkHasNotBitProof___closed__6_once, _init_l_Lean_mkHasNotBitProof___closed__6);
v___x_75_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_mkHasNotBitProof___closed__8(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_obj_once(&l_Lean_mkHasNotBitProof___closed__7, &l_Lean_mkHasNotBitProof___closed__7_once, _init_l_Lean_mkHasNotBitProof___closed__7);
v___x_77_ = ((lean_object*)(l_Lean_mkHasNotBitProof___closed__5));
v___x_78_ = l_Lean_mkConst(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_mkHasNotBitProof___closed__11(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_box(0);
v___x_83_ = ((lean_object*)(l_Lean_mkHasNotBitProof___closed__10));
v___x_84_ = l_Lean_mkConst(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_mkHasNotBitProof___closed__14(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_box(0);
v___x_90_ = ((lean_object*)(l_Lean_mkHasNotBitProof___closed__13));
v___x_91_ = l_Lean_mkConst(v___x_90_, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_mkHasNotBitProof___closed__15(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_92_ = lean_obj_once(&l_Lean_mkHasNotBitProof___closed__14, &l_Lean_mkHasNotBitProof___closed__14_once, _init_l_Lean_mkHasNotBitProof___closed__14);
v___x_93_ = lean_obj_once(&l_Lean_mkHasNotBitProof___closed__11, &l_Lean_mkHasNotBitProof___closed__11_once, _init_l_Lean_mkHasNotBitProof___closed__11);
v___x_94_ = lean_obj_once(&l_Lean_mkHasNotBitProof___closed__8, &l_Lean_mkHasNotBitProof___closed__8_once, _init_l_Lean_mkHasNotBitProof___closed__8);
v___x_95_ = l_Lean_mkAppB(v___x_94_, v___x_93_, v___x_92_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_mkHasNotBitProof___closed__19(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_99_ = ((lean_object*)(l_Lean_mkHasNotBitProof___closed__18));
v___x_100_ = lean_unsigned_to_nat(57u);
v___x_101_ = lean_unsigned_to_nat(35u);
v___x_102_ = ((lean_object*)(l_Lean_mkHasNotBitProof___closed__17));
v___x_103_ = ((lean_object*)(l_Lean_mkHasNotBitProof___closed__16));
v___x_104_ = l_mkPanicMessageWithDecl(v___x_103_, v___x_102_, v___x_101_, v___x_100_, v___x_99_);
return v___x_104_;
}
}
lean_object* l_Lean_mkHasNotBitProof(lean_object* v_e_105_, lean_object* v_ns_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = l_Lean_mkHasNotBit(v_e_105_, v_ns_106_);
v___x_113_ = l_Lean_Meta_matchNe_x3f(v___x_112_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_130_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_130_ == 0)
{
v___x_116_ = v___x_113_;
v_isShared_117_ = v_isSharedCheck_130_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_113_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_130_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
if (lean_obj_tag(v_a_114_) == 1)
{
lean_object* v_val_118_; lean_object* v_snd_119_; lean_object* v_fst_120_; lean_object* v_snd_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
v_val_118_ = lean_ctor_get(v_a_114_, 0);
lean_inc(v_val_118_);
lean_dec_ref_known(v_a_114_, 1);
v_snd_119_ = lean_ctor_get(v_val_118_, 1);
lean_inc(v_snd_119_);
lean_dec(v_val_118_);
v_fst_120_ = lean_ctor_get(v_snd_119_, 0);
lean_inc(v_fst_120_);
v_snd_121_ = lean_ctor_get(v_snd_119_, 1);
lean_inc(v_snd_121_);
lean_dec(v_snd_119_);
v___x_122_ = lean_obj_once(&l_Lean_mkHasNotBitProof___closed__2, &l_Lean_mkHasNotBitProof___closed__2_once, _init_l_Lean_mkHasNotBitProof___closed__2);
v___x_123_ = lean_obj_once(&l_Lean_mkHasNotBitProof___closed__15, &l_Lean_mkHasNotBitProof___closed__15_once, _init_l_Lean_mkHasNotBitProof___closed__15);
v___x_124_ = l_Lean_mkApp3(v___x_122_, v_fst_120_, v_snd_121_, v___x_123_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_124_);
v___x_126_ = v___x_116_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_del_object(v___x_116_);
lean_dec(v_a_114_);
v___x_128_ = lean_obj_once(&l_Lean_mkHasNotBitProof___closed__19, &l_Lean_mkHasNotBitProof___closed__19_once, _init_l_Lean_mkHasNotBitProof___closed__19);
v___x_129_ = l_panic___at___00Lean_mkHasNotBitProof_spec__0(v___x_128_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
return v___x_129_;
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
v_a_131_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_113_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_113_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkHasNotBitProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_105_ = stack[0].m_obj;
lean_object* v_ns_106_ = stack[1].m_obj;
lean_object* v_a_107_ = stack[2].m_obj;
lean_object* v_a_108_ = stack[3].m_obj;
lean_object* v_a_109_ = stack[4].m_obj;
lean_object* v_a_110_ = stack[5].m_obj;
lean_object* v_res_139_;
v_res_139_ = l_Lean_mkHasNotBitProof(v_e_105_, v_ns_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_Lean_mkHasNotBitProof___boxed(lean_object* v_e_140_, lean_object* v_ns_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_mkHasNotBitProof(v_e_140_, v_ns_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec_ref(v_ns_141_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_isHasNotBit_x3f(lean_object* v_e_148_){
_start:
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = l_Lean_Expr_cleanupAnnotations(v_e_148_);
v___x_150_ = l_Lean_Expr_isApp(v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; 
lean_dec_ref(v___x_149_);
v___x_151_ = lean_box(0);
return v___x_151_;
}
else
{
lean_object* v_arg_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_arg_152_ = lean_ctor_get(v___x_149_, 1);
lean_inc_ref(v_arg_152_);
v___x_153_ = l_Lean_Expr_appFnCleanup___redArg(v___x_149_);
v___x_154_ = l_Lean_Expr_isApp(v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; 
lean_dec_ref(v___x_153_);
lean_dec_ref(v_arg_152_);
v___x_155_ = lean_box(0);
return v___x_155_;
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_156_ = l_Lean_Expr_appFnCleanup___redArg(v___x_153_);
v___x_157_ = ((lean_object*)(l_Lean_mkHasNotBit___closed__2));
v___x_158_ = l_Lean_Expr_isConstOf(v___x_156_, v___x_157_);
lean_dec_ref(v___x_156_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; 
lean_dec_ref(v_arg_152_);
v___x_159_ = lean_box(0);
return v___x_159_;
}
else
{
lean_object* v___x_160_; 
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v_arg_152_);
return v___x_160_;
}
}
}
}
}
lean_object* l_panic___at___00Lean_refutableHasNotBit_x3f_spec__0(lean_object* v_msg_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v___f_167_; lean_object* v___x_1136__overap_168_; lean_object* v___x_169_; 
v___f_167_ = ((lean_object*)(l_panic___at___00Lean_mkHasNotBitProof_spec__0___closed__0));
v___x_1136__overap_168_ = lean_panic_fn_borrowed(v___f_167_, v_msg_161_);
lean_inc(v___y_165_);
lean_inc_ref(v___y_164_);
lean_inc(v___y_163_);
lean_inc_ref(v___y_162_);
v___x_169_ = lean_apply_5(v___x_1136__overap_168_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, lean_box(0));
return v___x_169_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_refutableHasNotBit_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_161_ = stack[0].m_obj;
lean_object* v___y_162_ = stack[1].m_obj;
lean_object* v___y_163_ = stack[2].m_obj;
lean_object* v___y_164_ = stack[3].m_obj;
lean_object* v___y_165_ = stack[4].m_obj;
lean_object* v_res_170_;
v_res_170_ = l_panic___at___00Lean_refutableHasNotBit_x3f_spec__0(v_msg_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
stack->m_obj
 = v_res_170_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_refutableHasNotBit_x3f_spec__0___boxed(lean_object* v_msg_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_panic___at___00Lean_refutableHasNotBit_x3f_spec__0(v_msg_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_177_;
}
}
static lean_object* _init_l_Lean_refutableHasNotBit_x3f___closed__2(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_box(0);
v___x_183_ = ((lean_object*)(l_Lean_refutableHasNotBit_x3f___closed__1));
v___x_184_ = l_Lean_mkConst(v___x_183_, v___x_182_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_refutableHasNotBit_x3f___closed__4(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_186_ = ((lean_object*)(l_Lean_mkHasNotBitProof___closed__18));
v___x_187_ = lean_unsigned_to_nat(84u);
v___x_188_ = lean_unsigned_to_nat(55u);
v___x_189_ = ((lean_object*)(l_Lean_refutableHasNotBit_x3f___closed__3));
v___x_190_ = ((lean_object*)(l_Lean_mkHasNotBitProof___closed__16));
v___x_191_ = l_mkPanicMessageWithDecl(v___x_190_, v___x_189_, v___x_188_, v___x_187_, v___x_186_);
return v___x_191_;
}
}
lean_object* l_Lean_refutableHasNotBit_x3f(lean_object* v_e_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_192_, v_a_194_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_201_, 1);
v___x_203_ = l_Lean_Expr_cleanupAnnotations(v_a_202_);
v___x_204_ = l_Lean_Expr_isApp(v___x_203_);
if (v___x_204_ == 0)
{
lean_dec_ref(v___x_203_);
goto v___jp_198_;
}
else
{
lean_object* v_arg_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v_arg_205_ = lean_ctor_get(v___x_203_, 1);
lean_inc_ref(v_arg_205_);
v___x_206_ = l_Lean_Expr_appFnCleanup___redArg(v___x_203_);
v___x_207_ = l_Lean_Expr_isApp(v___x_206_);
if (v___x_207_ == 0)
{
lean_dec_ref(v___x_206_);
lean_dec_ref(v_arg_205_);
goto v___jp_198_;
}
else
{
lean_object* v_arg_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v_arg_208_ = lean_ctor_get(v___x_206_, 1);
lean_inc_ref(v_arg_208_);
v___x_209_ = l_Lean_Expr_appFnCleanup___redArg(v___x_206_);
v___x_210_ = ((lean_object*)(l_Lean_mkHasNotBit___closed__2));
v___x_211_ = l_Lean_Expr_isConstOf(v___x_209_, v___x_210_);
lean_dec_ref(v___x_209_);
if (v___x_211_ == 0)
{
lean_dec_ref(v_arg_208_);
lean_dec_ref(v_arg_205_);
goto v___jp_198_;
}
else
{
lean_object* v___x_212_; 
lean_inc(v_a_196_);
lean_inc_ref(v_a_195_);
lean_inc(v_a_194_);
lean_inc_ref(v_a_193_);
v___x_212_ = lean_whnf(v_arg_205_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_272_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_272_ == 0)
{
v___x_215_ = v___x_212_;
v_isShared_216_ = v_isSharedCheck_272_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_212_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_272_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
uint8_t v___x_217_; 
v___x_217_ = l_Lean_Expr_hasFVar(v_a_213_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
lean_del_object(v___x_215_);
v___x_218_ = lean_obj_once(&l_Lean_mkHasNotBit___closed__3, &l_Lean_mkHasNotBit___closed__3_once, _init_l_Lean_mkHasNotBit___closed__3);
v___x_219_ = l_Lean_mkAppB(v___x_218_, v_arg_208_, v_a_213_);
v___x_220_ = l_Lean_Meta_matchNe_x3f(v___x_219_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref_known(v___x_220_, 1);
if (lean_obj_tag(v_a_221_) == 1)
{
lean_object* v_val_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_257_; 
v_val_222_ = lean_ctor_get(v_a_221_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v_a_221_);
if (v_isSharedCheck_257_ == 0)
{
v___x_224_ = v_a_221_;
v_isShared_225_ = v_isSharedCheck_257_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_val_222_);
lean_dec(v_a_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_257_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v_snd_226_; lean_object* v_fst_227_; lean_object* v_snd_228_; lean_object* v___x_229_; 
v_snd_226_ = lean_ctor_get(v_val_222_, 1);
lean_inc(v_snd_226_);
lean_dec(v_val_222_);
v_fst_227_ = lean_ctor_get(v_snd_226_, 0);
lean_inc_n(v_fst_227_, 2);
v_snd_228_ = lean_ctor_get(v_snd_226_, 1);
lean_inc_n(v_snd_228_, 2);
lean_dec(v_snd_226_);
v___x_229_ = l_Lean_Meta_isExprDefEq(v_fst_227_, v_snd_228_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_248_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_248_ == 0)
{
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_248_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_248_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
uint8_t v___x_234_; 
v___x_234_ = lean_unbox(v_a_230_);
lean_dec(v_a_230_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_237_; 
lean_dec(v_snd_228_);
lean_dec(v_fst_227_);
lean_del_object(v___x_224_);
v___x_235_ = lean_box(0);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_235_);
v___x_237_ = v___x_232_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_239_ = lean_obj_once(&l_Lean_refutableHasNotBit_x3f___closed__2, &l_Lean_refutableHasNotBit_x3f___closed__2_once, _init_l_Lean_refutableHasNotBit_x3f___closed__2);
v___x_240_ = l_Lean_reflBoolTrue;
v___x_241_ = l_Lean_mkApp3(v___x_239_, v_fst_227_, v_snd_228_, v___x_240_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_241_);
v___x_243_ = v___x_224_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_247_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_245_; 
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_243_);
v___x_245_ = v___x_232_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
else
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
lean_dec(v_snd_228_);
lean_dec(v_fst_227_);
lean_del_object(v___x_224_);
v_a_249_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_229_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_229_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec(v_a_221_);
v___x_258_ = lean_obj_once(&l_Lean_refutableHasNotBit_x3f___closed__4, &l_Lean_refutableHasNotBit_x3f___closed__4_once, _init_l_Lean_refutableHasNotBit_x3f___closed__4);
v___x_259_ = l_panic___at___00Lean_refutableHasNotBit_x3f_spec__0(v___x_258_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
return v___x_259_;
}
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
v_a_260_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_220_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_220_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
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
else
{
lean_object* v___x_268_; lean_object* v___x_270_; 
lean_dec(v_a_213_);
lean_dec_ref(v_arg_208_);
v___x_268_ = lean_box(0);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_268_);
v___x_270_ = v___x_215_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec_ref(v_arg_208_);
v_a_273_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_212_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_212_);
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
}
}
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
v_a_281_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_201_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_201_);
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
v___jp_198_:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_box(0);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
}
LEAN_EXPORT void l_Lean_refutableHasNotBit_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_192_ = stack[0].m_obj;
lean_object* v_a_193_ = stack[1].m_obj;
lean_object* v_a_194_ = stack[2].m_obj;
lean_object* v_a_195_ = stack[3].m_obj;
lean_object* v_a_196_ = stack[4].m_obj;
lean_object* v_res_289_;
v_res_289_ = l_Lean_refutableHasNotBit_x3f(v_e_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
stack->m_obj
 = v_res_289_;
}
LEAN_EXPORT lean_object* l_Lean_refutableHasNotBit_x3f___boxed(lean_object* v_e_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_refutableHasNotBit_x3f(v_e_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
return v_res_296_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_MatchUtil(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_HasNotBit(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
