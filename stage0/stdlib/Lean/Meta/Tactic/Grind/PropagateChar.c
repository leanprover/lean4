// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.PropagateChar
// Imports: import Init.Grind.Propagator import Lean.Meta.LitValues public import Lean.Meta.Tactic.Grind.PropagatorAttr
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getCharValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isCharLit(lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateCharToNatUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l_Lean_Meta_Grind_propagateCharToNatUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateCharToNatUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNat"};
static const lean_object* l_Lean_Meta_Grind_propagateCharToNatUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateCharToNatUp___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateCharToNatUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 248, 141, 246, 182, 101, 131, 69)}};
static const lean_object* l_Lean_Meta_Grind_propagateCharToNatUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateCharToNatUp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateCharToNatUp___closed__3;
static const lean_string_object l_Lean_Meta_Grind_propagateCharToNatUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_propagateCharToNatUp___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_propagateCharToNatUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l_Lean_Meta_Grind_propagateCharToNatUp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateCharToNatUp___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateCharToNatUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__5_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l_Lean_Meta_Grind_propagateCharToNatUp___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateCharToNatUp___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateCharToNatUp___closed__7;
static lean_once_cell_t l_Lean_Meta_Grind_propagateCharToNatUp___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateCharToNatUp___closed__8;
static lean_once_cell_t l_Lean_Meta_Grind_propagateCharToNatUp___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateCharToNatUp___closed__9;
static const lean_string_object l_Lean_Meta_Grind_propagateCharToNatUp___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Meta_Grind_propagateCharToNatUp___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateCharToNatUp___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateCharToNatUp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__10_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Meta_Grind_propagateCharToNatUp___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateCharToNatUp___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateCharToNatUp___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCharToNatUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCharToNatUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharToNatUp___regBuiltin_Lean_Meta_Grind_propagateCharToNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_2780309645____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharToNatUp___regBuiltin_Lean_Meta_Grind_propagateCharToNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_2780309645____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateCharValUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "val"};
static const lean_object* l_Lean_Meta_Grind_propagateCharValUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateCharValUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateCharValUp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateCharValUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateCharValUp___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateCharValUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 121, 142, 57, 80, 29, 36, 131)}};
static const lean_object* l_Lean_Meta_Grind_propagateCharValUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateCharValUp___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_propagateCharValUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Lean_Meta_Grind_propagateCharValUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateCharValUp___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateCharValUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateCharValUp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l_Lean_Meta_Grind_propagateCharValUp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateCharValUp___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateCharValUp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateCharValUp___closed__4;
static lean_once_cell_t l_Lean_Meta_Grind_propagateCharValUp___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateCharValUp___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCharValUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCharValUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharValUp___regBuiltin_Lean_Meta_Grind_propagateCharValUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_3780693866____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharValUp___regBuiltin_Lean_Meta_Grind_propagateCharValUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_3780693866____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateCharOfNatUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Grind_propagateCharOfNatUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateCharOfNatUp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateCharOfNatUp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateCharOfNatUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateCharOfNatUp___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateCharOfNatUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l_Lean_Meta_Grind_propagateCharOfNatUp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateCharOfNatUp___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateCharOfNatUp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateCharOfNatUp___closed__2;
static const lean_ctor_object l_Lean_Meta_Grind_propagateCharOfNatUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateCharToNatUp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_object* l_Lean_Meta_Grind_propagateCharOfNatUp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateCharOfNatUp___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_propagateCharOfNatUp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_propagateCharOfNatUp___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCharOfNatUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCharOfNatUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharOfNatUp___regBuiltin_Lean_Meta_Grind_propagateCharOfNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_1207922169____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharOfNatUp___regBuiltin_Lean_Meta_Grind_propagateCharOfNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_1207922169____hygCtx___hyg_9____boxed(lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__3(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_box(0);
v___x_7_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharToNatUp___closed__2));
v___x_8_ = l_Lean_mkConst(v___x_7_, v___x_6_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__7(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(1u);
v___x_15_ = l_Lean_Level_ofNat(v___x_14_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__8(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_16_ = lean_box(0);
v___x_17_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharToNatUp___closed__7, &l_Lean_Meta_Grind_propagateCharToNatUp___closed__7_once, _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__7);
v___x_18_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
lean_ctor_set(v___x_18_, 1, v___x_16_);
return v___x_18_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__9(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_19_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharToNatUp___closed__8, &l_Lean_Meta_Grind_propagateCharToNatUp___closed__8_once, _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__8);
v___x_20_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharToNatUp___closed__6));
v___x_21_ = l_Lean_mkConst(v___x_20_, v___x_19_);
return v___x_21_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__12(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_26_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharToNatUp___closed__8, &l_Lean_Meta_Grind_propagateCharToNatUp___closed__8_once, _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__8);
v___x_27_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharToNatUp___closed__11));
v___x_28_ = l_Lean_mkConst(v___x_27_, v___x_26_);
return v___x_28_;
}
}
lean_object* l_Lean_Meta_Grind_propagateCharToNatUp(lean_object* v_e_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v___x_44_; uint8_t v___x_45_; 
lean_inc_ref(v_e_29_);
v___x_44_ = l_Lean_Expr_cleanupAnnotations(v_e_29_);
v___x_45_ = l_Lean_Expr_isApp(v___x_44_);
if (v___x_45_ == 0)
{
lean_dec_ref(v___x_44_);
lean_dec_ref(v_e_29_);
goto v___jp_41_;
}
else
{
lean_object* v_arg_46_; lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v_arg_46_ = lean_ctor_get(v___x_44_, 1);
lean_inc_ref(v_arg_46_);
v___x_47_ = l_Lean_Expr_appFnCleanup___redArg(v___x_44_);
v___x_48_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharToNatUp___closed__2));
v___x_49_ = l_Lean_Expr_isConstOf(v___x_47_, v___x_48_);
lean_dec_ref(v___x_47_);
if (v___x_49_ == 0)
{
lean_dec_ref(v_arg_46_);
lean_dec_ref(v_e_29_);
goto v___jp_41_;
}
else
{
lean_object* v___x_50_; 
lean_inc_ref(v_arg_46_);
v___x_50_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_46_, v_a_30_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_50_) == 0)
{
lean_object* v_a_51_; lean_object* v_self_52_; lean_object* v___x_53_; 
v_a_51_ = lean_ctor_get(v___x_50_, 0);
lean_inc(v_a_51_);
lean_dec_ref_known(v___x_50_, 1);
v_self_52_ = lean_ctor_get(v_a_51_, 0);
lean_inc_ref_n(v_self_52_, 2);
lean_dec(v_a_51_);
v___x_53_ = l_Lean_Meta_getCharValue_x3f(v_self_52_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_123_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_123_ == 0)
{
v___x_56_ = v___x_53_;
v_isShared_57_ = v_isSharedCheck_123_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_53_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_123_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
if (lean_obj_tag(v_a_54_) == 1)
{
lean_object* v_val_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_118_; 
lean_del_object(v___x_56_);
v_val_58_ = lean_ctor_get(v_a_54_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v_a_54_);
if (v_isSharedCheck_118_ == 0)
{
v___x_60_ = v_a_54_;
v_isShared_61_ = v_isSharedCheck_118_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_val_58_);
lean_dec(v_a_54_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_118_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
uint32_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = lean_unbox_uint32(v_val_58_);
lean_dec(v_val_58_);
v___x_63_ = lean_uint32_to_nat(v___x_62_);
v___x_64_ = l_Lean_mkNatLit(v___x_63_);
v___x_65_ = l_Lean_Meta_Sym_shareCommon(v___x_64_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_67_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_66_);
lean_dec_ref_known(v___x_65_, 1);
lean_inc(v_a_39_);
lean_inc_ref(v_a_38_);
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc(v_a_33_);
lean_inc_ref(v_a_32_);
lean_inc(v_a_31_);
lean_inc(v_a_30_);
lean_inc_ref(v_self_52_);
v___x_67_ = lean_grind_mk_eq_proof(v_arg_46_, v_self_52_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_a_68_);
lean_dec_ref_known(v___x_67_, 1);
v___x_69_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharToNatUp___closed__3, &l_Lean_Meta_Grind_propagateCharToNatUp___closed__3_once, _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__3);
v___x_70_ = l_Lean_Meta_mkCongrArg(v___x_69_, v_a_68_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_a_71_);
lean_dec_ref_known(v___x_70_, 1);
v___x_72_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharToNatUp___closed__9, &l_Lean_Meta_Grind_propagateCharToNatUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__9);
v___x_73_ = l_Lean_Nat_mkType;
v___x_74_ = l_Lean_Expr_app___override(v___x_69_, v_self_52_);
v___x_75_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharToNatUp___closed__12, &l_Lean_Meta_Grind_propagateCharToNatUp___closed__12_once, _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__12);
lean_inc_n(v_a_66_, 2);
v___x_76_ = l_Lean_mkAppB(v___x_75_, v___x_73_, v_a_66_);
lean_inc_ref(v_e_29_);
v___x_77_ = l_Lean_mkApp6(v___x_72_, v___x_73_, v_e_29_, v___x_74_, v_a_66_, v_a_71_, v___x_76_);
v___x_78_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_29_, v_a_30_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_81_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_a_79_);
lean_dec_ref_known(v___x_78_, 1);
lean_inc_ref(v_e_29_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v_e_29_);
v___x_81_ = v___x_60_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_e_29_);
v___x_81_ = v_reuseFailAlloc_85_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
lean_object* v___x_82_; 
lean_inc(v_a_39_);
lean_inc_ref(v_a_38_);
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc(v_a_33_);
lean_inc_ref(v_a_32_);
lean_inc(v_a_31_);
lean_inc(v_a_30_);
lean_inc(v_a_66_);
v___x_82_ = lean_grind_internalize(v_a_66_, v_a_79_, v___x_81_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_82_) == 0)
{
uint8_t v___x_83_; lean_object* v___x_84_; 
lean_dec_ref_known(v___x_82_, 1);
v___x_83_ = 0;
v___x_84_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_29_, v_a_66_, v___x_77_, v___x_83_, v_a_30_, v_a_32_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
return v___x_84_;
}
else
{
lean_dec_ref(v___x_77_);
lean_dec(v_a_66_);
lean_dec_ref(v_e_29_);
return v___x_82_;
}
}
}
else
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_93_; 
lean_dec_ref(v___x_77_);
lean_dec(v_a_66_);
lean_del_object(v___x_60_);
lean_dec_ref(v_e_29_);
v_a_86_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_93_ == 0)
{
v___x_88_ = v___x_78_;
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_78_);
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
else
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
lean_dec(v_a_66_);
lean_del_object(v___x_60_);
lean_dec_ref(v_self_52_);
lean_dec_ref(v_e_29_);
v_a_94_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___x_70_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_70_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_dec(v_a_66_);
lean_del_object(v___x_60_);
lean_dec_ref(v_self_52_);
lean_dec_ref(v_e_29_);
v_a_102_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_67_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_67_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
lean_del_object(v___x_60_);
lean_dec_ref(v_self_52_);
lean_dec_ref(v_arg_46_);
lean_dec_ref(v_e_29_);
v_a_110_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_65_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_65_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
else
{
lean_object* v___x_119_; lean_object* v___x_121_; 
lean_dec(v_a_54_);
lean_dec_ref(v_self_52_);
lean_dec_ref(v_arg_46_);
lean_dec_ref(v_e_29_);
v___x_119_ = lean_box(0);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v___x_119_);
v___x_121_ = v___x_56_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
lean_dec_ref(v_self_52_);
lean_dec_ref(v_arg_46_);
lean_dec_ref(v_e_29_);
v_a_124_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_53_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_53_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
lean_dec_ref(v_arg_46_);
lean_dec_ref(v_e_29_);
v_a_132_ = lean_ctor_get(v___x_50_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_50_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_50_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
v___jp_41_:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_box(0);
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateCharToNatUp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_29_ = stack[0].m_obj;
lean_object* v_a_30_ = stack[1].m_obj;
lean_object* v_a_31_ = stack[2].m_obj;
lean_object* v_a_32_ = stack[3].m_obj;
lean_object* v_a_33_ = stack[4].m_obj;
lean_object* v_a_34_ = stack[5].m_obj;
lean_object* v_a_35_ = stack[6].m_obj;
lean_object* v_a_36_ = stack[7].m_obj;
lean_object* v_a_37_ = stack[8].m_obj;
lean_object* v_a_38_ = stack[9].m_obj;
lean_object* v_a_39_ = stack[10].m_obj;
lean_object* v_res_140_;
v_res_140_ = l_Lean_Meta_Grind_propagateCharToNatUp(v_e_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
stack->m_obj
 = v_res_140_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCharToNatUp___boxed(lean_object* v_e_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_Meta_Grind_propagateCharToNatUp(v_e_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec(v_a_142_);
return v_res_153_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharToNatUp___regBuiltin_Lean_Meta_Grind_propagateCharToNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_2780309645____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharToNatUp___closed__2));
v___x_156_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateCharToNatUp___boxed), 12, 0);
v___x_157_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_155_, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharToNatUp___regBuiltin_Lean_Meta_Grind_propagateCharToNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_2780309645____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_158_;
v_res_158_ = l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharToNatUp___regBuiltin_Lean_Meta_Grind_propagateCharToNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_2780309645____hygCtx___hyg_9_();
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharToNatUp___regBuiltin_Lean_Meta_Grind_propagateCharToNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_2780309645____hygCtx___hyg_9____boxed(lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharToNatUp___regBuiltin_Lean_Meta_Grind_propagateCharToNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_2780309645____hygCtx___hyg_9_();
return v_res_160_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateCharValUp___closed__4(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_box(0);
v___x_169_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharValUp___closed__3));
v___x_170_ = l_Lean_mkConst(v___x_169_, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateCharValUp___closed__5(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_box(0);
v___x_172_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharValUp___closed__1));
v___x_173_ = l_Lean_mkConst(v___x_172_, v___x_171_);
return v___x_173_;
}
}
lean_object* l_Lean_Meta_Grind_propagateCharValUp(lean_object* v_e_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v___x_189_; uint8_t v___x_190_; 
lean_inc_ref(v_e_174_);
v___x_189_ = l_Lean_Expr_cleanupAnnotations(v_e_174_);
v___x_190_ = l_Lean_Expr_isApp(v___x_189_);
if (v___x_190_ == 0)
{
lean_dec_ref(v___x_189_);
lean_dec_ref(v_e_174_);
goto v___jp_186_;
}
else
{
lean_object* v_arg_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_arg_191_ = lean_ctor_get(v___x_189_, 1);
lean_inc_ref(v_arg_191_);
v___x_192_ = l_Lean_Expr_appFnCleanup___redArg(v___x_189_);
v___x_193_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharValUp___closed__1));
v___x_194_ = l_Lean_Expr_isConstOf(v___x_192_, v___x_193_);
lean_dec_ref(v___x_192_);
if (v___x_194_ == 0)
{
lean_dec_ref(v_arg_191_);
lean_dec_ref(v_e_174_);
goto v___jp_186_;
}
else
{
lean_object* v___x_195_; 
lean_inc_ref(v_arg_191_);
v___x_195_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_191_, v_a_175_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v_self_197_; lean_object* v___x_198_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_a_196_);
lean_dec_ref_known(v___x_195_, 1);
v_self_197_ = lean_ctor_get(v_a_196_, 0);
lean_inc_ref_n(v_self_197_, 2);
lean_dec(v_a_196_);
v___x_198_ = l_Lean_Meta_getCharValue_x3f(v_self_197_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_277_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_277_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_277_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_277_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
if (lean_obj_tag(v_a_199_) == 1)
{
lean_object* v_val_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_272_; 
lean_del_object(v___x_201_);
v_val_203_ = lean_ctor_get(v_a_199_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v_a_199_);
if (v_isSharedCheck_272_ == 0)
{
v___x_205_ = v_a_199_;
v_isShared_206_ = v_isSharedCheck_272_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_val_203_);
lean_dec(v_a_199_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_272_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; uint32_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_207_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharValUp___closed__4, &l_Lean_Meta_Grind_propagateCharValUp___closed__4_once, _init_l_Lean_Meta_Grind_propagateCharValUp___closed__4);
v___x_208_ = lean_unbox_uint32(v_val_203_);
lean_dec(v_val_203_);
v___x_209_ = lean_uint32_to_nat(v___x_208_);
v___x_210_ = l_Lean_Meta_mkNumeral(v___x_207_, v___x_209_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_212_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
lean_dec_ref_known(v___x_210_, 1);
v___x_212_ = l_Lean_Meta_Sym_shareCommon(v_a_211_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_214_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_213_);
lean_dec_ref_known(v___x_212_, 1);
lean_inc(v_a_184_);
lean_inc_ref(v_a_183_);
lean_inc(v_a_182_);
lean_inc_ref(v_a_181_);
lean_inc(v_a_180_);
lean_inc_ref(v_a_179_);
lean_inc(v_a_178_);
lean_inc_ref(v_a_177_);
lean_inc(v_a_176_);
lean_inc(v_a_175_);
lean_inc_ref(v_self_197_);
v___x_214_ = lean_grind_mk_eq_proof(v_arg_191_, v_self_197_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_a_215_);
lean_dec_ref_known(v___x_214_, 1);
v___x_216_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharValUp___closed__5, &l_Lean_Meta_Grind_propagateCharValUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateCharValUp___closed__5);
v___x_217_ = l_Lean_Meta_mkCongrArg(v___x_216_, v_a_215_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_218_);
lean_dec_ref_known(v___x_217_, 1);
v___x_219_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharToNatUp___closed__9, &l_Lean_Meta_Grind_propagateCharToNatUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__9);
v___x_220_ = l_Lean_Expr_app___override(v___x_216_, v_self_197_);
v___x_221_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharToNatUp___closed__12, &l_Lean_Meta_Grind_propagateCharToNatUp___closed__12_once, _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__12);
lean_inc_n(v_a_213_, 2);
v___x_222_ = l_Lean_mkAppB(v___x_221_, v___x_207_, v_a_213_);
lean_inc_ref(v_e_174_);
v___x_223_ = l_Lean_mkApp6(v___x_219_, v___x_207_, v_e_174_, v___x_220_, v_a_213_, v_a_218_, v___x_222_);
v___x_224_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_174_, v_a_175_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref_known(v___x_224_, 1);
lean_inc_ref(v_e_174_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v_e_174_);
v___x_227_ = v___x_205_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_e_174_);
v___x_227_ = v_reuseFailAlloc_231_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; 
lean_inc(v_a_184_);
lean_inc_ref(v_a_183_);
lean_inc(v_a_182_);
lean_inc_ref(v_a_181_);
lean_inc(v_a_180_);
lean_inc_ref(v_a_179_);
lean_inc(v_a_178_);
lean_inc_ref(v_a_177_);
lean_inc(v_a_176_);
lean_inc(v_a_175_);
lean_inc(v_a_213_);
v___x_228_ = lean_grind_internalize(v_a_213_, v_a_225_, v___x_227_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_228_) == 0)
{
uint8_t v___x_229_; lean_object* v___x_230_; 
lean_dec_ref_known(v___x_228_, 1);
v___x_229_ = 0;
v___x_230_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_174_, v_a_213_, v___x_223_, v___x_229_, v_a_175_, v_a_177_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
return v___x_230_;
}
else
{
lean_dec_ref(v___x_223_);
lean_dec(v_a_213_);
lean_dec_ref(v_e_174_);
return v___x_228_;
}
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_dec_ref(v___x_223_);
lean_dec(v_a_213_);
lean_del_object(v___x_205_);
lean_dec_ref(v_e_174_);
v_a_232_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_224_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_224_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec(v_a_213_);
lean_del_object(v___x_205_);
lean_dec_ref(v_self_197_);
lean_dec_ref(v_e_174_);
v_a_240_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_217_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_217_);
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
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
lean_dec(v_a_213_);
lean_del_object(v___x_205_);
lean_dec_ref(v_self_197_);
lean_dec_ref(v_e_174_);
v_a_248_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_214_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_214_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_del_object(v___x_205_);
lean_dec_ref(v_self_197_);
lean_dec_ref(v_arg_191_);
lean_dec_ref(v_e_174_);
v_a_256_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_212_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_212_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_del_object(v___x_205_);
lean_dec_ref(v_self_197_);
lean_dec_ref(v_arg_191_);
lean_dec_ref(v_e_174_);
v_a_264_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_210_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_210_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
else
{
lean_object* v___x_273_; lean_object* v___x_275_; 
lean_dec(v_a_199_);
lean_dec_ref(v_self_197_);
lean_dec_ref(v_arg_191_);
lean_dec_ref(v_e_174_);
v___x_273_ = lean_box(0);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_273_);
v___x_275_ = v___x_201_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v_self_197_);
lean_dec_ref(v_arg_191_);
lean_dec_ref(v_e_174_);
v_a_278_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_198_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_198_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v_arg_191_);
lean_dec_ref(v_e_174_);
v_a_286_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_195_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_195_);
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
}
v___jp_186_:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_box(0);
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
return v___x_188_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateCharValUp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_174_ = stack[0].m_obj;
lean_object* v_a_175_ = stack[1].m_obj;
lean_object* v_a_176_ = stack[2].m_obj;
lean_object* v_a_177_ = stack[3].m_obj;
lean_object* v_a_178_ = stack[4].m_obj;
lean_object* v_a_179_ = stack[5].m_obj;
lean_object* v_a_180_ = stack[6].m_obj;
lean_object* v_a_181_ = stack[7].m_obj;
lean_object* v_a_182_ = stack[8].m_obj;
lean_object* v_a_183_ = stack[9].m_obj;
lean_object* v_a_184_ = stack[10].m_obj;
lean_object* v_res_294_;
v_res_294_ = l_Lean_Meta_Grind_propagateCharValUp(v_e_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCharValUp___boxed(lean_object* v_e_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Meta_Grind_propagateCharValUp(v_e_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec(v_a_296_);
return v_res_307_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharValUp___regBuiltin_Lean_Meta_Grind_propagateCharValUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_3780693866____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharValUp___closed__1));
v___x_310_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateCharValUp___boxed), 12, 0);
v___x_311_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_309_, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharValUp___regBuiltin_Lean_Meta_Grind_propagateCharValUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_3780693866____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_312_;
v_res_312_ = l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharValUp___regBuiltin_Lean_Meta_Grind_propagateCharValUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_3780693866____hygCtx___hyg_9_();
stack->m_obj
 = v_res_312_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharValUp___regBuiltin_Lean_Meta_Grind_propagateCharValUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_3780693866____hygCtx___hyg_9____boxed(lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharValUp___regBuiltin_Lean_Meta_Grind_propagateCharValUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_3780693866____hygCtx___hyg_9_();
return v_res_314_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateCharOfNatUp___closed__2(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_box(0);
v___x_320_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharOfNatUp___closed__1));
v___x_321_ = l_Lean_mkConst(v___x_320_, v___x_319_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateCharOfNatUp___closed__4(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = lean_box(0);
v___x_325_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharOfNatUp___closed__3));
v___x_326_ = l_Lean_mkConst(v___x_325_, v___x_324_);
return v___x_326_;
}
}
lean_object* l_Lean_Meta_Grind_propagateCharOfNatUp(lean_object* v_e_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v___x_342_; uint8_t v___x_343_; 
lean_inc_ref(v_e_327_);
v___x_342_ = l_Lean_Expr_cleanupAnnotations(v_e_327_);
v___x_343_ = l_Lean_Expr_isApp(v___x_342_);
if (v___x_343_ == 0)
{
lean_dec_ref(v___x_342_);
lean_dec_ref(v_e_327_);
goto v___jp_339_;
}
else
{
lean_object* v_arg_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_arg_344_ = lean_ctor_get(v___x_342_, 1);
lean_inc_ref(v_arg_344_);
v___x_345_ = l_Lean_Expr_appFnCleanup___redArg(v___x_342_);
v___x_346_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharOfNatUp___closed__1));
v___x_347_ = l_Lean_Expr_isConstOf(v___x_345_, v___x_346_);
lean_dec_ref(v___x_345_);
if (v___x_347_ == 0)
{
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_327_);
goto v___jp_339_;
}
else
{
uint8_t v___x_348_; 
v___x_348_ = l_Lean_Expr_isCharLit(v_e_327_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
lean_inc_ref(v_arg_344_);
v___x_349_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_344_, v_a_328_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v_self_351_; lean_object* v___x_352_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_350_);
lean_dec_ref_known(v___x_349_, 1);
v_self_351_ = lean_ctor_get(v_a_350_, 0);
lean_inc_ref(v_self_351_);
lean_dec(v_a_350_);
v___x_352_ = l_Lean_Meta_getNatValue_x3f(v_self_351_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_422_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_422_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_422_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_422_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
if (lean_obj_tag(v_a_353_) == 1)
{
lean_object* v_val_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_417_; 
lean_del_object(v___x_355_);
v_val_357_ = lean_ctor_get(v_a_353_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v_a_353_);
if (v_isSharedCheck_417_ == 0)
{
v___x_359_ = v_a_353_;
v_isShared_360_ = v_isSharedCheck_417_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_val_357_);
lean_dec(v_a_353_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_417_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
uint32_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_361_ = l_Char_ofNat(v_val_357_);
lean_dec(v_val_357_);
v___x_362_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharOfNatUp___closed__2, &l_Lean_Meta_Grind_propagateCharOfNatUp___closed__2_once, _init_l_Lean_Meta_Grind_propagateCharOfNatUp___closed__2);
v___x_363_ = lean_uint32_to_nat(v___x_361_);
v___x_364_ = l_Lean_mkRawNatLit(v___x_363_);
v___x_365_ = l_Lean_Expr_app___override(v___x_362_, v___x_364_);
v___x_366_ = l_Lean_Meta_Sym_shareCommon(v___x_365_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_368_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_367_);
lean_dec_ref_known(v___x_366_, 1);
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
lean_inc(v_a_335_);
lean_inc_ref(v_a_334_);
lean_inc(v_a_333_);
lean_inc_ref(v_a_332_);
lean_inc(v_a_331_);
lean_inc_ref(v_a_330_);
lean_inc(v_a_329_);
lean_inc(v_a_328_);
lean_inc_ref(v_self_351_);
v___x_368_ = lean_grind_mk_eq_proof(v_arg_344_, v_self_351_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_370_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
lean_dec_ref_known(v___x_368_, 1);
v___x_370_ = l_Lean_Meta_mkCongrArg(v___x_362_, v_a_369_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
lean_dec_ref_known(v___x_370_, 1);
v___x_372_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharToNatUp___closed__9, &l_Lean_Meta_Grind_propagateCharToNatUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__9);
v___x_373_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharOfNatUp___closed__4, &l_Lean_Meta_Grind_propagateCharOfNatUp___closed__4_once, _init_l_Lean_Meta_Grind_propagateCharOfNatUp___closed__4);
v___x_374_ = l_Lean_Expr_app___override(v___x_362_, v_self_351_);
v___x_375_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharToNatUp___closed__12, &l_Lean_Meta_Grind_propagateCharToNatUp___closed__12_once, _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__12);
lean_inc_n(v_a_367_, 2);
v___x_376_ = l_Lean_mkAppB(v___x_375_, v___x_373_, v_a_367_);
lean_inc_ref(v_e_327_);
v___x_377_ = l_Lean_mkApp6(v___x_372_, v___x_373_, v_e_327_, v___x_374_, v_a_367_, v_a_371_, v___x_376_);
v___x_378_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_327_, v_a_328_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_381_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref_known(v___x_378_, 1);
lean_inc_ref(v_e_327_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v_e_327_);
v___x_381_ = v___x_359_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_e_327_);
v___x_381_ = v_reuseFailAlloc_384_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; 
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
lean_inc(v_a_335_);
lean_inc_ref(v_a_334_);
lean_inc(v_a_333_);
lean_inc_ref(v_a_332_);
lean_inc(v_a_331_);
lean_inc_ref(v_a_330_);
lean_inc(v_a_329_);
lean_inc(v_a_328_);
lean_inc(v_a_367_);
v___x_382_ = lean_grind_internalize(v_a_367_, v_a_379_, v___x_381_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v___x_383_; 
lean_dec_ref_known(v___x_382_, 1);
v___x_383_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_327_, v_a_367_, v___x_377_, v___x_348_, v_a_328_, v_a_330_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
return v___x_383_;
}
else
{
lean_dec_ref(v___x_377_);
lean_dec(v_a_367_);
lean_dec_ref(v_e_327_);
return v___x_382_;
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec_ref(v___x_377_);
lean_dec(v_a_367_);
lean_del_object(v___x_359_);
lean_dec_ref(v_e_327_);
v_a_385_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_378_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_378_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
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
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec(v_a_367_);
lean_del_object(v___x_359_);
lean_dec_ref(v_self_351_);
lean_dec_ref(v_e_327_);
v_a_393_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_370_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_370_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec(v_a_367_);
lean_del_object(v___x_359_);
lean_dec_ref(v_self_351_);
lean_dec_ref(v_e_327_);
v_a_401_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_368_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_368_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
lean_del_object(v___x_359_);
lean_dec_ref(v_self_351_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_327_);
v_a_409_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_366_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_366_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
else
{
lean_object* v___x_418_; lean_object* v___x_420_; 
lean_dec(v_a_353_);
lean_dec_ref(v_self_351_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_327_);
v___x_418_ = lean_box(0);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_418_);
v___x_420_ = v___x_355_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec_ref(v_self_351_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_327_);
v_a_423_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_352_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_352_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_327_);
v_a_431_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_349_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_349_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_e_327_);
v___x_439_ = lean_box(0);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
}
}
v___jp_339_:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_box(0);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateCharOfNatUp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_327_ = stack[0].m_obj;
lean_object* v_a_328_ = stack[1].m_obj;
lean_object* v_a_329_ = stack[2].m_obj;
lean_object* v_a_330_ = stack[3].m_obj;
lean_object* v_a_331_ = stack[4].m_obj;
lean_object* v_a_332_ = stack[5].m_obj;
lean_object* v_a_333_ = stack[6].m_obj;
lean_object* v_a_334_ = stack[7].m_obj;
lean_object* v_a_335_ = stack[8].m_obj;
lean_object* v_a_336_ = stack[9].m_obj;
lean_object* v_a_337_ = stack[10].m_obj;
lean_object* v_res_441_;
v_res_441_ = l_Lean_Meta_Grind_propagateCharOfNatUp(v_e_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
stack->m_obj
 = v_res_441_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCharOfNatUp___boxed(lean_object* v_e_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Meta_Grind_propagateCharOfNatUp(v_e_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec(v_a_443_);
return v_res_454_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharOfNatUp___regBuiltin_Lean_Meta_Grind_propagateCharOfNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_1207922169____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharOfNatUp___closed__1));
v___x_457_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateCharOfNatUp___boxed), 12, 0);
v___x_458_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_456_, v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharOfNatUp___regBuiltin_Lean_Meta_Grind_propagateCharOfNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_1207922169____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_459_;
v_res_459_ = l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharOfNatUp___regBuiltin_Lean_Meta_Grind_propagateCharOfNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_1207922169____hygCtx___hyg_9_();
stack->m_obj
 = v_res_459_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharOfNatUp___regBuiltin_Lean_Meta_Grind_propagateCharOfNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_1207922169____hygCtx___hyg_9____boxed(lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharOfNatUp___regBuiltin_Lean_Meta_Grind_propagateCharOfNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_1207922169____hygCtx___hyg_9_();
return v_res_461_;
}
}
lean_object* runtime_initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagateChar(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharToNatUp___regBuiltin_Lean_Meta_Grind_propagateCharToNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_2780309645____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharValUp___regBuiltin_Lean_Meta_Grind_propagateCharValUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_3780693866____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharOfNatUp___regBuiltin_Lean_Meta_Grind_propagateCharOfNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_1207922169____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_PropagateChar(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_PropagateChar(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagateChar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_PropagateChar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_PropagateChar(builtin);
}
#ifdef __cplusplus
}
#endif
