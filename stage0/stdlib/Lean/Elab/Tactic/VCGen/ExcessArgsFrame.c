// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.ExcessArgsFrame
// Imports: public import Lean.Meta.Basic import Lean.Meta.AppBuilder import Std.Internal.Order.Heyting
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_List_range(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CompleteLattice"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofProp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 140, 127, 117, 148, 144, 166, 107)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 160, 150, 32, 134, 96, 114, 42)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(194, 193, 63, 6, 53, 61, 199, 176)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "u"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 178, 247, 241, 102, 42, 87, 174)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_frame(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_frame___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "le_apply_of_point_meet_le"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 15, 136, 52, 94, 223, 161, 163)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "point_meet_le_of_le_apply"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 12, 18, 17, 144, 205, 23, 196)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_8_; 
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_8_ = lean_apply_6(v_k_1_, v_b_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, lean_box(0));
return v___x_8_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
lean_object* v_b_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v_res_9_;
v_res_9_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___redArg___lam__0(v_k_1_, v_b_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
stack->m_obj
 = v_res_9_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___redArg___lam__0(v_k_10_, v_b_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
lean_dec(v___y_13_);
lean_dec_ref(v___y_12_);
return v_res_17_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___redArg(lean_object* v_name_18_, uint8_t v_bi_19_, lean_object* v_type_20_, lean_object* v_k_21_, uint8_t v_kind_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; 
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_28_, 0, v_k_21_);
v___x_29_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_18_, v_bi_19_, v_type_20_, v___f_28_, v_kind_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
v_a_38_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_29_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_29_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_18_ = stack[0].m_obj;
uint8_t v_bi_19_ = stack[1].m_num;
lean_object* v_type_20_ = stack[2].m_obj;
lean_object* v_k_21_ = stack[3].m_obj;
uint8_t v_kind_22_ = stack[4].m_num;
lean_object* v___y_23_ = stack[5].m_obj;
lean_object* v___y_24_ = stack[6].m_obj;
lean_object* v___y_25_ = stack[7].m_obj;
lean_object* v___y_26_ = stack[8].m_obj;
lean_object* v_res_46_;
v_res_46_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___redArg(v_name_18_, v_bi_19_, v_type_20_, v_k_21_, v_kind_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___redArg___boxed(lean_object* v_name_47_, lean_object* v_bi_48_, lean_object* v_type_49_, lean_object* v_k_50_, lean_object* v_kind_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
uint8_t v_bi_boxed_57_; uint8_t v_kind_boxed_58_; lean_object* v_res_59_; 
v_bi_boxed_57_ = lean_unbox(v_bi_48_);
v_kind_boxed_58_ = lean_unbox(v_kind_51_);
v_res_59_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___redArg(v_name_47_, v_bi_boxed_57_, v_type_49_, v_k_50_, v_kind_boxed_58_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_59_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0___redArg(lean_object* v_name_60_, lean_object* v_type_61_, lean_object* v_k_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
uint8_t v___x_68_; uint8_t v___x_69_; lean_object* v___x_70_; 
v___x_68_ = 0;
v___x_69_ = 0;
v___x_70_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___redArg(v_name_60_, v___x_68_, v_type_61_, v_k_62_, v___x_69_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
return v___x_70_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_60_ = stack[0].m_obj;
lean_object* v_type_61_ = stack[1].m_obj;
lean_object* v_k_62_ = stack[2].m_obj;
lean_object* v___y_63_ = stack[3].m_obj;
lean_object* v___y_64_ = stack[4].m_obj;
lean_object* v___y_65_ = stack[5].m_obj;
lean_object* v___y_66_ = stack[6].m_obj;
lean_object* v_res_71_;
v_res_71_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0___redArg(v_name_60_, v_type_61_, v_k_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0___redArg___boxed(lean_object* v_name_72_, lean_object* v_type_73_, lean_object* v_k_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0___redArg(v_name_72_, v_type_73_, v_k_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
return v_res_80_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0(lean_object* v___x_95_, lean_object* v_a_96_, lean_object* v___x_97_, uint8_t v___x_98_, lean_object* v_u_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___x_105_; 
lean_inc(v___y_103_);
lean_inc_ref(v___y_102_);
lean_inc(v___y_101_);
lean_inc_ref(v___y_100_);
lean_inc_ref(v___x_95_);
v___x_105_ = lean_infer_type(v___x_95_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_143_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_143_ == 0)
{
v___x_108_ = v___x_105_;
v_isShared_109_ = v_isSharedCheck_143_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_143_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; 
lean_inc_ref(v_u_99_);
v___x_110_ = l_Lean_Meta_mkEq(v_u_99_, v_a_96_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_142_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_142_ == 0)
{
v___x_113_ = v___x_110_;
v_isShared_114_ = v_isSharedCheck_142_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_110_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_142_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__4));
if (v_isShared_114_ == 0)
{
lean_ctor_set_tag(v___x_113_, 1);
lean_ctor_set(v___x_113_, 0, v_a_106_);
v___x_117_ = v___x_113_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_106_);
v___x_117_ = v_reuseFailAlloc_141_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; lean_object* v___x_120_; 
v___x_118_ = lean_box(0);
if (v_isShared_109_ == 0)
{
lean_ctor_set_tag(v___x_108_, 1);
lean_ctor_set(v___x_108_, 0, v_a_111_);
v___x_120_ = v___x_108_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_111_);
v___x_120_ = v_reuseFailAlloc_140_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_121_ = lean_unsigned_to_nat(3u);
v___x_122_ = lean_mk_empty_array_with_capacity(v___x_121_);
v___x_123_ = lean_array_push(v___x_122_, v___x_117_);
v___x_124_ = lean_array_push(v___x_123_, v___x_118_);
v___x_125_ = lean_array_push(v___x_124_, v___x_120_);
v___x_126_ = l_Lean_Meta_mkAppOptM(v___x_115_, v___x_125_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_a_127_);
lean_dec_ref_known(v___x_126_, 1);
v___x_128_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___closed__6));
v___x_129_ = lean_unsigned_to_nat(2u);
v___x_130_ = lean_mk_empty_array_with_capacity(v___x_129_);
v___x_131_ = lean_array_push(v___x_130_, v_a_127_);
v___x_132_ = lean_array_push(v___x_131_, v___x_95_);
v___x_133_ = l_Lean_Meta_mkAppM(v___x_128_, v___x_132_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; uint8_t v___x_138_; lean_object* v___x_139_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
lean_dec_ref_known(v___x_133_, 1);
v___x_135_ = lean_mk_empty_array_with_capacity(v___x_97_);
v___x_136_ = lean_array_push(v___x_135_, v_u_99_);
v___x_137_ = 0;
v___x_138_ = 1;
v___x_139_ = l_Lean_Meta_mkLambdaFVars(v___x_136_, v_a_134_, v___x_137_, v___x_98_, v___x_137_, v___x_98_, v___x_138_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
lean_dec_ref(v___x_136_);
return v___x_139_;
}
else
{
lean_dec_ref(v_u_99_);
return v___x_133_;
}
}
else
{
lean_dec_ref(v_u_99_);
lean_dec_ref(v___x_95_);
return v___x_126_;
}
}
}
}
}
else
{
lean_del_object(v___x_108_);
lean_dec(v_a_106_);
lean_dec_ref(v_u_99_);
lean_dec_ref(v___x_95_);
return v___x_110_;
}
}
}
else
{
lean_dec_ref(v_u_99_);
lean_dec_ref(v_a_96_);
lean_dec_ref(v___x_95_);
return v___x_105_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_95_ = stack[0].m_obj;
lean_object* v_a_96_ = stack[1].m_obj;
lean_object* v___x_97_ = stack[2].m_obj;
uint8_t v___x_98_ = stack[3].m_num;
lean_object* v_u_99_ = stack[4].m_obj;
lean_object* v___y_100_ = stack[5].m_obj;
lean_object* v___y_101_ = stack[6].m_obj;
lean_object* v___y_102_ = stack[7].m_obj;
lean_object* v___y_103_ = stack[8].m_obj;
lean_object* v_res_144_;
v_res_144_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0(v___x_95_, v_a_96_, v___x_97_, v___x_98_, v_u_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
stack->m_obj
 = v_res_144_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___boxed(lean_object* v___x_145_, lean_object* v_a_146_, lean_object* v___x_147_, lean_object* v___x_148_, lean_object* v_u_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
uint8_t v___x_2072__boxed_155_; lean_object* v_res_156_; 
v___x_2072__boxed_155_ = lean_unbox(v___x_148_);
v_res_156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0(v___x_145_, v_a_146_, v___x_147_, v___x_2072__boxed_155_, v_u_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___x_147_);
return v_res_156_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1(lean_object* v_as_160_, size_t v_sz_161_, size_t v_i_162_, lean_object* v_b_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
uint8_t v___x_169_; 
v___x_169_ = lean_usize_dec_lt(v_i_162_, v_sz_161_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v_b_163_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v_a_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___f_178_; lean_object* v___x_179_; 
v___x_171_ = l_Lean_instInhabitedExpr;
v_a_172_ = lean_array_uget_borrowed(v_as_160_, v_i_162_);
v___x_173_ = lean_array_get_size(v_b_163_);
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_sub(v___x_173_, v___x_174_);
v___x_176_ = lean_array_get_borrowed(v___x_171_, v_b_163_, v___x_175_);
lean_dec(v___x_175_);
v___x_177_ = lean_box(v___x_169_);
lean_inc_n(v_a_172_, 2);
lean_inc(v___x_176_);
v___f_178_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___lam__0___boxed), 10, 4);
lean_closure_set(v___f_178_, 0, v___x_176_);
lean_closure_set(v___f_178_, 1, v_a_172_);
lean_closure_set(v___f_178_, 2, v___x_174_);
lean_closure_set(v___f_178_, 3, v___x_177_);
lean_inc(v___y_167_);
lean_inc_ref(v___y_166_);
lean_inc(v___y_165_);
lean_inc_ref(v___y_164_);
v___x_179_ = lean_infer_type(v_a_172_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 1);
v___x_181_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___closed__1));
v___x_182_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0___redArg(v___x_181_, v_a_180_, v___f_178_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_184_; size_t v___x_185_; size_t v___x_186_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_a_183_);
lean_dec_ref_known(v___x_182_, 1);
v___x_184_ = lean_array_push(v_b_163_, v_a_183_);
v___x_185_ = ((size_t)1ULL);
v___x_186_ = lean_usize_add(v_i_162_, v___x_185_);
v_i_162_ = v___x_186_;
v_b_163_ = v___x_184_;
goto _start;
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
lean_dec_ref(v_b_163_);
v_a_188_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_182_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_182_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_dec_ref(v___f_178_);
lean_dec_ref(v_b_163_);
v_a_196_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_179_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_179_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_160_ = stack[0].m_obj;
size_t v_sz_161_ = stack[1].m_num;
size_t v_i_162_ = stack[2].m_num;
lean_object* v_b_163_ = stack[3].m_obj;
lean_object* v___y_164_ = stack[4].m_obj;
lean_object* v___y_165_ = stack[5].m_obj;
lean_object* v___y_166_ = stack[6].m_obj;
lean_object* v___y_167_ = stack[7].m_obj;
lean_object* v_res_204_;
v_res_204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1(v_as_160_, v_sz_161_, v_i_162_, v_b_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
stack->m_obj
 = v_res_204_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1___boxed(lean_object* v_as_205_, lean_object* v_sz_206_, lean_object* v_i_207_, lean_object* v_b_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
size_t v_sz_boxed_214_; size_t v_i_boxed_215_; lean_object* v_res_216_; 
v_sz_boxed_214_ = lean_unbox_usize(v_sz_206_);
lean_dec(v_sz_206_);
v_i_boxed_215_ = lean_unbox_usize(v_i_207_);
lean_dec(v_i_207_);
v_res_216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1(v_as_205_, v_sz_boxed_214_, v_i_boxed_215_, v_b_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec_ref(v_as_205_);
return v_res_216_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new(lean_object* v_pre_217_, lean_object* v_ss_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_frames_226_; lean_object* v___x_227_; size_t v_sz_228_; size_t v___x_229_; lean_object* v___x_230_; 
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_mk_empty_array_with_capacity(v___x_224_);
v_frames_226_ = lean_array_push(v___x_225_, v_pre_217_);
v___x_227_ = l_Array_reverse___redArg(v_ss_218_);
v_sz_228_ = lean_array_size(v___x_227_);
v___x_229_ = ((size_t)0ULL);
v___x_230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__1(v___x_227_, v_sz_228_, v___x_229_, v_frames_226_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
lean_dec_ref(v___x_227_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_239_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_239_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_239_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_235_ = l_Array_reverse___redArg(v_a_231_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_235_);
v___x_237_ = v___x_233_;
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
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
v_a_240_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_230_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_230_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
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
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_217_ = stack[0].m_obj;
lean_object* v_ss_218_ = stack[1].m_obj;
lean_object* v_a_219_ = stack[2].m_obj;
lean_object* v_a_220_ = stack[3].m_obj;
lean_object* v_a_221_ = stack[4].m_obj;
lean_object* v_a_222_ = stack[5].m_obj;
lean_object* v_res_248_;
v_res_248_ = l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new(v_pre_217_, v_ss_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
stack->m_obj
 = v_res_248_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new___boxed(lean_object* v_pre_249_, lean_object* v_ss_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new(v_pre_249_, v_ss_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
return v_res_256_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0(lean_object* v_00_u03b1_257_, lean_object* v_name_258_, uint8_t v_bi_259_, lean_object* v_type_260_, lean_object* v_k_261_, uint8_t v_kind_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___redArg(v_name_258_, v_bi_259_, v_type_260_, v_k_261_, v_kind_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
return v___x_268_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_258_ = stack[1].m_obj;
uint8_t v_bi_259_ = stack[2].m_num;
lean_object* v_type_260_ = stack[3].m_obj;
lean_object* v_k_261_ = stack[4].m_obj;
uint8_t v_kind_262_ = stack[5].m_num;
lean_object* v___y_263_ = stack[6].m_obj;
lean_object* v___y_264_ = stack[7].m_obj;
lean_object* v___y_265_ = stack[8].m_obj;
lean_object* v___y_266_ = stack[9].m_obj;
lean_object* v_res_269_;
v_res_269_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0(lean_box(0), v_name_258_, v_bi_259_, v_type_260_, v_k_261_, v_kind_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
stack->m_obj
 = v_res_269_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0___boxed(lean_object* v_00_u03b1_270_, lean_object* v_name_271_, lean_object* v_bi_272_, lean_object* v_type_273_, lean_object* v_k_274_, lean_object* v_kind_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
uint8_t v_bi_boxed_281_; uint8_t v_kind_boxed_282_; lean_object* v_res_283_; 
v_bi_boxed_281_ = lean_unbox(v_bi_272_);
v_kind_boxed_282_ = lean_unbox(v_kind_275_);
v_res_283_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_spec__0(v_00_u03b1_270_, v_name_271_, v_bi_boxed_281_, v_type_273_, v_k_274_, v_kind_boxed_282_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
return v_res_283_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0(lean_object* v_00_u03b1_284_, lean_object* v_name_285_, lean_object* v_type_286_, lean_object* v_k_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0___redArg(v_name_285_, v_type_286_, v_k_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
return v___x_293_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_285_ = stack[1].m_obj;
lean_object* v_type_286_ = stack[2].m_obj;
lean_object* v_k_287_ = stack[3].m_obj;
lean_object* v___y_288_ = stack[4].m_obj;
lean_object* v___y_289_ = stack[5].m_obj;
lean_object* v___y_290_ = stack[6].m_obj;
lean_object* v___y_291_ = stack[7].m_obj;
lean_object* v_res_294_;
v_res_294_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0(lean_box(0), v_name_285_, v_type_286_, v_k_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0___boxed(lean_object* v_00_u03b1_295_, lean_object* v_name_296_, lean_object* v_type_297_, lean_object* v_k_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_new_spec__0(v_00_u03b1_295_, v_name_296_, v_type_297_, v_k_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_frame(lean_object* v_i_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = l_Lean_instInhabitedExpr;
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_array_get_borrowed(v___x_306_, v_i_305_, v___x_307_);
lean_inc(v___x_308_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_frame___boxed(lean_object* v_i_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_frame(v_i_309_);
lean_dec_ref(v_i_309_);
return v_res_310_;
}
}
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg(lean_object* v_ss_316_, lean_object* v_i_317_, lean_object* v_X_318_, lean_object* v_range_319_, lean_object* v_b_320_, lean_object* v_i_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_stop_327_; lean_object* v_step_328_; uint8_t v___x_329_; 
v_stop_327_ = lean_ctor_get(v_range_319_, 1);
v_step_328_ = lean_ctor_get(v_range_319_, 2);
v___x_329_ = lean_nat_dec_lt(v_i_321_, v_stop_327_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
lean_dec(v_i_321_);
lean_dec_ref(v_X_318_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v_b_320_);
return v___x_330_;
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_331_ = l_Lean_instInhabitedExpr;
v___x_332_ = lean_unsigned_to_nat(1u);
v___x_333_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg___closed__1));
v___x_334_ = lean_array_get_borrowed(v___x_331_, v_ss_316_, v_i_321_);
v___x_335_ = lean_nat_add(v_i_321_, v___x_332_);
v___x_336_ = lean_array_get_borrowed(v___x_331_, v_i_317_, v___x_335_);
lean_dec(v___x_335_);
v___x_337_ = lean_unsigned_to_nat(0u);
lean_inc(v_i_321_);
v___x_338_ = l_Array_extract___redArg(v_ss_316_, v___x_337_, v_i_321_);
lean_inc_ref(v_X_318_);
v___x_339_ = l_Lean_mkAppN(v_X_318_, v___x_338_);
lean_dec_ref(v___x_338_);
v___x_340_ = lean_unsigned_to_nat(4u);
v___x_341_ = lean_mk_empty_array_with_capacity(v___x_340_);
lean_inc(v___x_334_);
v___x_342_ = lean_array_push(v___x_341_, v___x_334_);
lean_inc(v___x_336_);
v___x_343_ = lean_array_push(v___x_342_, v___x_336_);
v___x_344_ = lean_array_push(v___x_343_, v___x_339_);
v___x_345_ = lean_array_push(v___x_344_, v_b_320_);
v___x_346_ = l_Lean_Meta_mkAppM(v___x_333_, v___x_345_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_348_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref_known(v___x_346_, 1);
v___x_348_ = lean_nat_add(v_i_321_, v_step_328_);
lean_dec(v_i_321_);
v_b_320_ = v_a_347_;
v_i_321_ = v___x_348_;
goto _start;
}
else
{
lean_dec(v_i_321_);
lean_dec_ref(v_X_318_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ss_316_ = stack[0].m_obj;
lean_object* v_i_317_ = stack[1].m_obj;
lean_object* v_X_318_ = stack[2].m_obj;
lean_object* v_range_319_ = stack[3].m_obj;
lean_object* v_b_320_ = stack[4].m_obj;
lean_object* v_i_321_ = stack[5].m_obj;
lean_object* v___y_322_ = stack[6].m_obj;
lean_object* v___y_323_ = stack[7].m_obj;
lean_object* v___y_324_ = stack[8].m_obj;
lean_object* v___y_325_ = stack[9].m_obj;
lean_object* v_res_350_;
v_res_350_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg(v_ss_316_, v_i_317_, v_X_318_, v_range_319_, v_b_320_, v_i_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
stack->m_obj
 = v_res_350_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg___boxed(lean_object* v_ss_351_, lean_object* v_i_352_, lean_object* v_X_353_, lean_object* v_range_354_, lean_object* v_b_355_, lean_object* v_i_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg(v_ss_351_, v_i_352_, v_X_353_, v_range_354_, v_b_355_, v_i_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec_ref(v_range_354_);
lean_dec_ref(v_i_352_);
lean_dec_ref(v_ss_351_);
return v_res_362_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate(lean_object* v_i_363_, lean_object* v_X_364_, lean_object* v_ss_365_, lean_object* v_h_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = lean_array_get_size(v_ss_365_);
v___x_374_ = lean_unsigned_to_nat(1u);
v___x_375_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_375_, 0, v___x_372_);
lean_ctor_set(v___x_375_, 1, v___x_373_);
lean_ctor_set(v___x_375_, 2, v___x_374_);
v___x_376_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg(v_ss_365_, v_i_363_, v_X_364_, v___x_375_, v_h_366_, v___x_372_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
lean_dec_ref_known(v___x_375_, 3);
return v___x_376_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_363_ = stack[0].m_obj;
lean_object* v_X_364_ = stack[1].m_obj;
lean_object* v_ss_365_ = stack[2].m_obj;
lean_object* v_h_366_ = stack[3].m_obj;
lean_object* v_a_367_ = stack[4].m_obj;
lean_object* v_a_368_ = stack[5].m_obj;
lean_object* v_a_369_ = stack[6].m_obj;
lean_object* v_a_370_ = stack[7].m_obj;
lean_object* v_res_377_;
v_res_377_ = l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate(v_i_363_, v_X_364_, v_ss_365_, v_h_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
stack->m_obj
 = v_res_377_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate___boxed(lean_object* v_i_378_, lean_object* v_X_379_, lean_object* v_ss_380_, lean_object* v_h_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate(v_i_378_, v_X_379_, v_ss_380_, v_h_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec_ref(v_ss_380_);
lean_dec_ref(v_i_378_);
return v_res_387_;
}
}
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0(lean_object* v_ss_388_, lean_object* v_i_389_, lean_object* v_X_390_, lean_object* v_range_391_, lean_object* v_b_392_, lean_object* v_i_393_, lean_object* v_hs_394_, lean_object* v_hl_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___redArg(v_ss_388_, v_i_389_, v_X_390_, v_range_391_, v_b_392_, v_i_393_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
return v___x_401_;
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ss_388_ = stack[0].m_obj;
lean_object* v_i_389_ = stack[1].m_obj;
lean_object* v_X_390_ = stack[2].m_obj;
lean_object* v_range_391_ = stack[3].m_obj;
lean_object* v_b_392_ = stack[4].m_obj;
lean_object* v_i_393_ = stack[5].m_obj;
lean_object* v___y_396_ = stack[8].m_obj;
lean_object* v___y_397_ = stack[9].m_obj;
lean_object* v___y_398_ = stack[10].m_obj;
lean_object* v___y_399_ = stack[11].m_obj;
lean_object* v_res_402_;
v_res_402_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0(v_ss_388_, v_i_389_, v_X_390_, v_range_391_, v_b_392_, v_i_393_, lean_box(0), lean_box(0), v___y_396_, v___y_397_, v___y_398_, v___y_399_);
stack->m_obj
 = v_res_402_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0___boxed(lean_object* v_ss_403_, lean_object* v_i_404_, lean_object* v_X_405_, lean_object* v_range_406_, lean_object* v_b_407_, lean_object* v_i_408_, lean_object* v_hs_409_, lean_object* v_hl_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_instantiate_spec__0(v_ss_403_, v_i_404_, v_X_405_, v_range_406_, v_b_407_, v_i_408_, v_hs_409_, v_hl_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec_ref(v_range_406_);
lean_dec_ref(v_i_404_);
lean_dec_ref(v_ss_403_);
return v_res_416_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg(lean_object* v_ss_422_, lean_object* v_i_423_, lean_object* v_X_424_, lean_object* v_as_x27_425_, lean_object* v_b_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
if (lean_obj_tag(v_as_x27_425_) == 0)
{
lean_object* v___x_432_; 
lean_dec_ref(v_X_424_);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v_b_426_);
return v___x_432_;
}
else
{
lean_object* v_head_433_; lean_object* v_tail_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_head_433_ = lean_ctor_get(v_as_x27_425_, 0);
v_tail_434_ = lean_ctor_get(v_as_x27_425_, 1);
v___x_435_ = l_Lean_instInhabitedExpr;
v___x_436_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg___closed__1));
v___x_437_ = lean_array_get_borrowed(v___x_435_, v_ss_422_, v_head_433_);
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_add(v_head_433_, v___x_438_);
v___x_440_ = lean_array_get_borrowed(v___x_435_, v_i_423_, v___x_439_);
lean_dec(v___x_439_);
v___x_441_ = lean_unsigned_to_nat(0u);
lean_inc(v_head_433_);
v___x_442_ = l_Array_extract___redArg(v_ss_422_, v___x_441_, v_head_433_);
lean_inc_ref(v_X_424_);
v___x_443_ = l_Lean_mkAppN(v_X_424_, v___x_442_);
lean_dec_ref(v___x_442_);
v___x_444_ = lean_unsigned_to_nat(4u);
v___x_445_ = lean_mk_empty_array_with_capacity(v___x_444_);
lean_inc(v___x_437_);
v___x_446_ = lean_array_push(v___x_445_, v___x_437_);
lean_inc(v___x_440_);
v___x_447_ = lean_array_push(v___x_446_, v___x_440_);
v___x_448_ = lean_array_push(v___x_447_, v___x_443_);
v___x_449_ = lean_array_push(v___x_448_, v_b_426_);
v___x_450_ = l_Lean_Meta_mkAppM(v___x_436_, v___x_449_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_a_451_);
lean_dec_ref_known(v___x_450_, 1);
v_as_x27_425_ = v_tail_434_;
v_b_426_ = v_a_451_;
goto _start;
}
else
{
lean_dec_ref(v_X_424_);
return v___x_450_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ss_422_ = stack[0].m_obj;
lean_object* v_i_423_ = stack[1].m_obj;
lean_object* v_X_424_ = stack[2].m_obj;
lean_object* v_as_x27_425_ = stack[3].m_obj;
lean_object* v_b_426_ = stack[4].m_obj;
lean_object* v___y_427_ = stack[5].m_obj;
lean_object* v___y_428_ = stack[6].m_obj;
lean_object* v___y_429_ = stack[7].m_obj;
lean_object* v___y_430_ = stack[8].m_obj;
lean_object* v_res_453_;
v_res_453_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg(v_ss_422_, v_i_423_, v_X_424_, v_as_x27_425_, v_b_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
stack->m_obj
 = v_res_453_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg___boxed(lean_object* v_ss_454_, lean_object* v_i_455_, lean_object* v_X_456_, lean_object* v_as_x27_457_, lean_object* v_b_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg(v_ss_454_, v_i_455_, v_X_456_, v_as_x27_457_, v_b_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v_as_x27_457_);
lean_dec_ref(v_i_455_);
lean_dec_ref(v_ss_454_);
return v_res_464_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract(lean_object* v_i_465_, lean_object* v_X_466_, lean_object* v_ss_467_, lean_object* v_h_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_474_ = lean_array_get_size(v_ss_467_);
v___x_475_ = l_List_range(v___x_474_);
v___x_476_ = l_List_reverse___redArg(v___x_475_);
v___x_477_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg(v_ss_467_, v_i_465_, v_X_466_, v___x_476_, v_h_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
lean_dec(v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_465_ = stack[0].m_obj;
lean_object* v_X_466_ = stack[1].m_obj;
lean_object* v_ss_467_ = stack[2].m_obj;
lean_object* v_h_468_ = stack[3].m_obj;
lean_object* v_a_469_ = stack[4].m_obj;
lean_object* v_a_470_ = stack[5].m_obj;
lean_object* v_a_471_ = stack[6].m_obj;
lean_object* v_a_472_ = stack[7].m_obj;
lean_object* v_res_478_;
v_res_478_ = l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract(v_i_465_, v_X_466_, v_ss_467_, v_h_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
stack->m_obj
 = v_res_478_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract___boxed(lean_object* v_i_479_, lean_object* v_X_480_, lean_object* v_ss_481_, lean_object* v_h_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract(v_i_479_, v_X_480_, v_ss_481_, v_h_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
lean_dec_ref(v_ss_481_);
lean_dec_ref(v_i_479_);
return v_res_488_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0(lean_object* v_ss_489_, lean_object* v_i_490_, lean_object* v_X_491_, lean_object* v_as_492_, lean_object* v_as_x27_493_, lean_object* v_b_494_, lean_object* v_a_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___redArg(v_ss_489_, v_i_490_, v_X_491_, v_as_x27_493_, v_b_494_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
return v___x_501_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ss_489_ = stack[0].m_obj;
lean_object* v_i_490_ = stack[1].m_obj;
lean_object* v_X_491_ = stack[2].m_obj;
lean_object* v_as_492_ = stack[3].m_obj;
lean_object* v_as_x27_493_ = stack[4].m_obj;
lean_object* v_b_494_ = stack[5].m_obj;
lean_object* v___y_496_ = stack[7].m_obj;
lean_object* v___y_497_ = stack[8].m_obj;
lean_object* v___y_498_ = stack[9].m_obj;
lean_object* v___y_499_ = stack[10].m_obj;
lean_object* v_res_502_;
v_res_502_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0(v_ss_489_, v_i_490_, v_X_491_, v_as_492_, v_as_x27_493_, v_b_494_, lean_box(0), v___y_496_, v___y_497_, v___y_498_, v___y_499_);
stack->m_obj
 = v_res_502_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0___boxed(lean_object* v_ss_503_, lean_object* v_i_504_, lean_object* v_X_505_, lean_object* v_as_506_, lean_object* v_as_x27_507_, lean_object* v_b_508_, lean_object* v_a_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_VCGen_ExcessArgsFrameInfo_abstract_spec__0(v_ss_503_, v_i_504_, v_X_505_, v_as_506_, v_as_x27_507_, v_b_508_, v_a_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v_as_x27_507_);
lean_dec(v_as_506_);
lean_dec_ref(v_i_504_);
lean_dec_ref(v_ss_503_);
return v_res_515_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Order_Heyting(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_ExcessArgsFrame(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Order_Heyting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_VCGen_ExcessArgsFrame(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Std_Internal_Order_Heyting(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_VCGen_ExcessArgsFrame(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Order_Heyting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_ExcessArgsFrame(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_VCGen_ExcessArgsFrame(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_VCGen_ExcessArgsFrame(builtin);
}
#ifdef __cplusplus
}
#endif
