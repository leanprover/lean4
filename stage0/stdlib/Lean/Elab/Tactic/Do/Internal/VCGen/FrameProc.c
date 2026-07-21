// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.FrameProc
// Imports: public import Lean.Elab.Tactic.Do.Internal.VCGen.WPApp import Std.Internal.Do.Order.Basic import Lean.Meta.AppBuilder
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(194, 193, 63, 6, 53, 61, 199, 176)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__1___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__4_value)} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__5_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__4_value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__5_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___closed__8_value;
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__0, &l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__2(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__1, &l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__1);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__2, &l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs___closed__2);
return v___x_9_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(lean_object* v_a_10_, lean_object* v_x_11_){
_start:
{
if (lean_obj_tag(v_x_11_) == 0)
{
uint8_t v___x_12_; 
v___x_12_ = 0;
return v___x_12_;
}
else
{
lean_object* v_key_13_; lean_object* v_tail_14_; uint8_t v___x_15_; 
v_key_13_ = lean_ctor_get(v_x_11_, 0);
v_tail_14_ = lean_ctor_get(v_x_11_, 2);
v___x_15_ = lean_name_eq(v_key_13_, v_a_10_);
if (v___x_15_ == 0)
{
v_x_11_ = v_tail_14_;
goto _start;
}
else
{
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___redArg___boxed(lean_object* v_a_17_, lean_object* v_x_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(v_a_17_, v_x_18_);
lean_dec(v_x_18_);
lean_dec(v_a_17_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(lean_object* v_a_21_, lean_object* v_b_22_, lean_object* v_x_23_){
_start:
{
if (lean_obj_tag(v_x_23_) == 0)
{
lean_dec(v_b_22_);
lean_dec(v_a_21_);
return v_x_23_;
}
else
{
lean_object* v_key_24_; lean_object* v_value_25_; lean_object* v_tail_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_38_; 
v_key_24_ = lean_ctor_get(v_x_23_, 0);
v_value_25_ = lean_ctor_get(v_x_23_, 1);
v_tail_26_ = lean_ctor_get(v_x_23_, 2);
v_isSharedCheck_38_ = !lean_is_exclusive(v_x_23_);
if (v_isSharedCheck_38_ == 0)
{
v___x_28_ = v_x_23_;
v_isShared_29_ = v_isSharedCheck_38_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_tail_26_);
lean_inc(v_value_25_);
lean_inc(v_key_24_);
lean_dec(v_x_23_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_38_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
uint8_t v___x_30_; 
v___x_30_ = lean_name_eq(v_key_24_, v_a_21_);
if (v___x_30_ == 0)
{
lean_object* v___x_31_; lean_object* v___x_33_; 
v___x_31_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(v_a_21_, v_b_22_, v_tail_26_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 2, v___x_31_);
v___x_33_ = v___x_28_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_key_24_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v_value_25_);
lean_ctor_set(v_reuseFailAlloc_34_, 2, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
else
{
lean_object* v___x_36_; 
lean_dec(v_value_25_);
lean_dec(v_key_24_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 1, v_b_22_);
lean_ctor_set(v___x_28_, 0, v_a_21_);
v___x_36_ = v___x_28_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_21_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_b_22_);
lean_ctor_set(v_reuseFailAlloc_37_, 2, v_tail_26_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
}
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_39_; uint64_t v___x_40_; 
v___x_39_ = lean_unsigned_to_nat(1723u);
v___x_40_ = lean_uint64_of_nat(v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
return v_x_41_;
}
else
{
lean_object* v_key_43_; lean_object* v_value_44_; lean_object* v_tail_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_71_; 
v_key_43_ = lean_ctor_get(v_x_42_, 0);
v_value_44_ = lean_ctor_get(v_x_42_, 1);
v_tail_45_ = lean_ctor_get(v_x_42_, 2);
v_isSharedCheck_71_ = !lean_is_exclusive(v_x_42_);
if (v_isSharedCheck_71_ == 0)
{
v___x_47_ = v_x_42_;
v_isShared_48_ = v_isSharedCheck_71_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_tail_45_);
lean_inc(v_value_44_);
lean_inc(v_key_43_);
lean_dec(v_x_42_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_71_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; uint64_t v___y_51_; 
v___x_49_ = lean_array_get_size(v_x_41_);
if (lean_obj_tag(v_key_43_) == 0)
{
uint64_t v___x_69_; 
v___x_69_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_51_ = v___x_69_;
goto v___jp_50_;
}
else
{
uint64_t v_hash_70_; 
v_hash_70_ = lean_ctor_get_uint64(v_key_43_, sizeof(void*)*2);
v___y_51_ = v_hash_70_;
goto v___jp_50_;
}
v___jp_50_:
{
uint64_t v___x_52_; uint64_t v___x_53_; uint64_t v_fold_54_; uint64_t v___x_55_; uint64_t v___x_56_; uint64_t v___x_57_; size_t v___x_58_; size_t v___x_59_; size_t v___x_60_; size_t v___x_61_; size_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_52_ = 32ULL;
v___x_53_ = lean_uint64_shift_right(v___y_51_, v___x_52_);
v_fold_54_ = lean_uint64_xor(v___y_51_, v___x_53_);
v___x_55_ = 16ULL;
v___x_56_ = lean_uint64_shift_right(v_fold_54_, v___x_55_);
v___x_57_ = lean_uint64_xor(v_fold_54_, v___x_56_);
v___x_58_ = lean_uint64_to_usize(v___x_57_);
v___x_59_ = lean_usize_of_nat(v___x_49_);
v___x_60_ = ((size_t)1ULL);
v___x_61_ = lean_usize_sub(v___x_59_, v___x_60_);
v___x_62_ = lean_usize_land(v___x_58_, v___x_61_);
v___x_63_ = lean_array_uget_borrowed(v_x_41_, v___x_62_);
lean_inc(v___x_63_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 2, v___x_63_);
v___x_65_ = v___x_47_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_key_43_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_value_44_);
lean_ctor_set(v_reuseFailAlloc_68_, 2, v___x_63_);
v___x_65_ = v_reuseFailAlloc_68_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
lean_object* v___x_66_; 
v___x_66_ = lean_array_uset(v_x_41_, v___x_62_, v___x_65_);
v_x_41_ = v___x_66_;
v_x_42_ = v_tail_45_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2___redArg(lean_object* v_i_72_, lean_object* v_source_73_, lean_object* v_target_74_){
_start:
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = lean_array_get_size(v_source_73_);
v___x_76_ = lean_nat_dec_lt(v_i_72_, v___x_75_);
if (v___x_76_ == 0)
{
lean_dec_ref(v_source_73_);
lean_dec(v_i_72_);
return v_target_74_;
}
else
{
lean_object* v_es_77_; lean_object* v___x_78_; lean_object* v_source_79_; lean_object* v_target_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_es_77_ = lean_array_fget(v_source_73_, v_i_72_);
v___x_78_ = lean_box(0);
v_source_79_ = lean_array_fset(v_source_73_, v_i_72_, v___x_78_);
v_target_80_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_target_74_, v_es_77_);
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_add(v_i_72_, v___x_81_);
lean_dec(v_i_72_);
v_i_72_ = v___x_82_;
v_source_73_ = v_source_79_;
v_target_74_ = v_target_80_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1___redArg(lean_object* v_data_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v_nbuckets_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_85_ = lean_array_get_size(v_data_84_);
v___x_86_ = lean_unsigned_to_nat(2u);
v_nbuckets_87_ = lean_nat_mul(v___x_85_, v___x_86_);
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = lean_box(0);
v___x_90_ = lean_mk_array(v_nbuckets_87_, v___x_89_);
v___x_91_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2___redArg(v___x_88_, v_data_84_, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0___redArg(lean_object* v_m_92_, lean_object* v_a_93_, lean_object* v_b_94_){
_start:
{
lean_object* v_size_95_; lean_object* v_buckets_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_142_; 
v_size_95_ = lean_ctor_get(v_m_92_, 0);
v_buckets_96_ = lean_ctor_get(v_m_92_, 1);
v_isSharedCheck_142_ = !lean_is_exclusive(v_m_92_);
if (v_isSharedCheck_142_ == 0)
{
v___x_98_ = v_m_92_;
v_isShared_99_ = v_isSharedCheck_142_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_buckets_96_);
lean_inc(v_size_95_);
lean_dec(v_m_92_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_142_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; uint64_t v___y_102_; 
v___x_100_ = lean_array_get_size(v_buckets_96_);
if (lean_obj_tag(v_a_93_) == 0)
{
uint64_t v___x_140_; 
v___x_140_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_102_ = v___x_140_;
goto v___jp_101_;
}
else
{
uint64_t v_hash_141_; 
v_hash_141_ = lean_ctor_get_uint64(v_a_93_, sizeof(void*)*2);
v___y_102_ = v_hash_141_;
goto v___jp_101_;
}
v___jp_101_:
{
uint64_t v___x_103_; uint64_t v___x_104_; uint64_t v_fold_105_; uint64_t v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; size_t v___x_109_; size_t v___x_110_; size_t v___x_111_; size_t v___x_112_; size_t v___x_113_; lean_object* v_bkt_114_; uint8_t v___x_115_; 
v___x_103_ = 32ULL;
v___x_104_ = lean_uint64_shift_right(v___y_102_, v___x_103_);
v_fold_105_ = lean_uint64_xor(v___y_102_, v___x_104_);
v___x_106_ = 16ULL;
v___x_107_ = lean_uint64_shift_right(v_fold_105_, v___x_106_);
v___x_108_ = lean_uint64_xor(v_fold_105_, v___x_107_);
v___x_109_ = lean_uint64_to_usize(v___x_108_);
v___x_110_ = lean_usize_of_nat(v___x_100_);
v___x_111_ = ((size_t)1ULL);
v___x_112_ = lean_usize_sub(v___x_110_, v___x_111_);
v___x_113_ = lean_usize_land(v___x_109_, v___x_112_);
v_bkt_114_ = lean_array_uget_borrowed(v_buckets_96_, v___x_113_);
v___x_115_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(v_a_93_, v_bkt_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v_size_x27_117_; lean_object* v___x_118_; lean_object* v_buckets_x27_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_116_ = lean_unsigned_to_nat(1u);
v_size_x27_117_ = lean_nat_add(v_size_95_, v___x_116_);
lean_dec(v_size_95_);
lean_inc(v_bkt_114_);
v___x_118_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_118_, 0, v_a_93_);
lean_ctor_set(v___x_118_, 1, v_b_94_);
lean_ctor_set(v___x_118_, 2, v_bkt_114_);
v_buckets_x27_119_ = lean_array_uset(v_buckets_96_, v___x_113_, v___x_118_);
v___x_120_ = lean_unsigned_to_nat(4u);
v___x_121_ = lean_nat_mul(v_size_x27_117_, v___x_120_);
v___x_122_ = lean_unsigned_to_nat(3u);
v___x_123_ = lean_nat_div(v___x_121_, v___x_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_array_get_size(v_buckets_x27_119_);
v___x_125_ = lean_nat_dec_le(v___x_123_, v___x_124_);
lean_dec(v___x_123_);
if (v___x_125_ == 0)
{
lean_object* v_val_126_; lean_object* v___x_128_; 
v_val_126_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1___redArg(v_buckets_x27_119_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v_val_126_);
lean_ctor_set(v___x_98_, 0, v_size_x27_117_);
v___x_128_ = v___x_98_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_size_x27_117_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_val_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
else
{
lean_object* v___x_131_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v_buckets_x27_119_);
lean_ctor_set(v___x_98_, 0, v_size_x27_117_);
v___x_131_ = v___x_98_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_size_x27_117_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_buckets_x27_119_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
else
{
lean_object* v___x_133_; lean_object* v_buckets_x27_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
lean_inc(v_bkt_114_);
v___x_133_ = lean_box(0);
v_buckets_x27_134_ = lean_array_uset(v_buckets_96_, v___x_113_, v___x_133_);
v___x_135_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(v_a_93_, v_b_94_, v_bkt_114_);
v___x_136_ = lean_array_uset(v_buckets_x27_134_, v___x_113_, v___x_135_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 1, v___x_136_);
v___x_138_ = v___x_98_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_size_95_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert(lean_object* v_s_143_, lean_object* v_fp_144_){
_start:
{
lean_object* v_op_145_; lean_object* v_byProg_146_; lean_object* v_latticeOps_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_158_; 
v_op_145_ = lean_ctor_get(v_fp_144_, 3);
lean_inc_ref(v_op_145_);
v_byProg_146_ = lean_ctor_get(v_s_143_, 0);
v_latticeOps_147_ = lean_ctor_get(v_s_143_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v_s_143_);
if (v_isSharedCheck_158_ == 0)
{
v___x_149_ = v_s_143_;
v_isShared_150_ = v_isSharedCheck_158_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_latticeOps_147_);
lean_inc(v_byProg_146_);
lean_dec(v_s_143_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_158_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v_prog_151_; lean_object* v_head_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v_prog_151_ = lean_ctor_get(v_fp_144_, 0);
lean_inc(v_prog_151_);
v_head_152_ = lean_ctor_get(v_op_145_, 0);
lean_inc(v_head_152_);
v___x_153_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0___redArg(v_byProg_146_, v_prog_151_, v_fp_144_);
v___x_154_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0___redArg(v_latticeOps_147_, v_head_152_, v_op_145_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 1, v___x_154_);
lean_ctor_set(v___x_149_, 0, v___x_153_);
v___x_156_ = v___x_149_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v___x_154_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0(lean_object* v_00_u03b2_159_, lean_object* v_m_160_, lean_object* v_a_161_, lean_object* v_b_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0___redArg(v_m_160_, v_a_161_, v_b_162_);
return v___x_163_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0(lean_object* v_00_u03b2_164_, lean_object* v_a_165_, lean_object* v_x_166_){
_start:
{
uint8_t v___x_167_; 
v___x_167_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___redArg(v_a_165_, v_x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_168_, lean_object* v_a_169_, lean_object* v_x_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__0(v_00_u03b2_168_, v_a_169_, v_x_170_);
lean_dec(v_x_170_);
lean_dec(v_a_169_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1(lean_object* v_00_u03b2_173_, lean_object* v_data_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1___redArg(v_data_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__2(lean_object* v_00_u03b2_176_, lean_object* v_a_177_, lean_object* v_b_178_, lean_object* v_x_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__2___redArg(v_a_177_, v_b_178_, v_x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_181_, lean_object* v_i_182_, lean_object* v_source_183_, lean_object* v_target_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2___redArg(v_i_182_, v_source_183_, v_target_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_186_, lean_object* v_x_187_, lean_object* v_x_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_FrameProcs_insert_spec__0_spec__1_spec__2_spec__3___redArg(v_x_187_, v_x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__0(lean_object* v_info_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(v_info_190_);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__0___boxed(lean_object* v_info_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__0(v_info_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec_ref(v_info_198_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__1(lean_object* v___x_205_, lean_object* v_info_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_212_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(v_info_206_);
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
v___x_214_ = lean_box(0);
v___x_215_ = lean_unsigned_to_nat(2u);
v___x_216_ = lean_mk_empty_array_with_capacity(v___x_215_);
v___x_217_ = lean_array_push(v___x_216_, v___x_213_);
v___x_218_ = lean_array_push(v___x_217_, v___x_214_);
v___x_219_ = l_Lean_Meta_mkAppOptM(v___x_205_, v___x_218_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__1___boxed(lean_object* v___x_220_, lean_object* v_info_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc___lam__1(v___x_220_, v_info_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec_ref(v_info_221_);
return v_res_227_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Do_Order_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs = _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameProcs);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp(uint8_t builtin);
lean_object* initialize_Std_Internal_Do_Order_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Do_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(builtin);
}
#ifdef __cplusplus
}
#endif
