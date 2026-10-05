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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCharToNatUp(lean_object* v_e_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCharToNatUp___boxed(lean_object* v_e_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Meta_Grind_propagateCharToNatUp(v_e_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
lean_dec(v_a_141_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharToNatUp___regBuiltin_Lean_Meta_Grind_propagateCharToNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_2780309645____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharToNatUp___closed__2));
v___x_155_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateCharToNatUp___boxed), 12, 0);
v___x_156_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_154_, v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharToNatUp___regBuiltin_Lean_Meta_Grind_propagateCharToNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_2780309645____hygCtx___hyg_9____boxed(lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharToNatUp___regBuiltin_Lean_Meta_Grind_propagateCharToNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_2780309645____hygCtx___hyg_9_();
return v_res_158_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateCharValUp___closed__4(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_box(0);
v___x_167_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharValUp___closed__3));
v___x_168_ = l_Lean_mkConst(v___x_167_, v___x_166_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateCharValUp___closed__5(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_box(0);
v___x_170_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharValUp___closed__1));
v___x_171_ = l_Lean_mkConst(v___x_170_, v___x_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCharValUp(lean_object* v_e_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v___x_187_; uint8_t v___x_188_; 
lean_inc_ref(v_e_172_);
v___x_187_ = l_Lean_Expr_cleanupAnnotations(v_e_172_);
v___x_188_ = l_Lean_Expr_isApp(v___x_187_);
if (v___x_188_ == 0)
{
lean_dec_ref(v___x_187_);
lean_dec_ref(v_e_172_);
goto v___jp_184_;
}
else
{
lean_object* v_arg_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_arg_189_ = lean_ctor_get(v___x_187_, 1);
lean_inc_ref(v_arg_189_);
v___x_190_ = l_Lean_Expr_appFnCleanup___redArg(v___x_187_);
v___x_191_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharValUp___closed__1));
v___x_192_ = l_Lean_Expr_isConstOf(v___x_190_, v___x_191_);
lean_dec_ref(v___x_190_);
if (v___x_192_ == 0)
{
lean_dec_ref(v_arg_189_);
lean_dec_ref(v_e_172_);
goto v___jp_184_;
}
else
{
lean_object* v___x_193_; 
lean_inc_ref(v_arg_189_);
v___x_193_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_189_, v_a_173_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v_self_195_; lean_object* v___x_196_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_193_, 1);
v_self_195_ = lean_ctor_get(v_a_194_, 0);
lean_inc_ref_n(v_self_195_, 2);
lean_dec(v_a_194_);
v___x_196_ = l_Lean_Meta_getCharValue_x3f(v_self_195_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_275_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_275_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_275_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_275_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
if (lean_obj_tag(v_a_197_) == 1)
{
lean_object* v_val_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_270_; 
lean_del_object(v___x_199_);
v_val_201_ = lean_ctor_get(v_a_197_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v_a_197_);
if (v_isSharedCheck_270_ == 0)
{
v___x_203_ = v_a_197_;
v_isShared_204_ = v_isSharedCheck_270_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_val_201_);
lean_dec(v_a_197_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_270_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; uint32_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_205_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharValUp___closed__4, &l_Lean_Meta_Grind_propagateCharValUp___closed__4_once, _init_l_Lean_Meta_Grind_propagateCharValUp___closed__4);
v___x_206_ = lean_unbox_uint32(v_val_201_);
lean_dec(v_val_201_);
v___x_207_ = lean_uint32_to_nat(v___x_206_);
v___x_208_ = l_Lean_Meta_mkNumeral(v___x_205_, v___x_207_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_210_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_208_, 1);
v___x_210_ = l_Lean_Meta_Sym_shareCommon(v_a_209_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_212_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_a_211_);
lean_dec_ref_known(v___x_210_, 1);
lean_inc(v_a_182_);
lean_inc_ref(v_a_181_);
lean_inc(v_a_180_);
lean_inc_ref(v_a_179_);
lean_inc(v_a_178_);
lean_inc_ref(v_a_177_);
lean_inc(v_a_176_);
lean_inc_ref(v_a_175_);
lean_inc(v_a_174_);
lean_inc(v_a_173_);
lean_inc_ref(v_self_195_);
v___x_212_ = lean_grind_mk_eq_proof(v_arg_189_, v_self_195_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_213_);
lean_dec_ref_known(v___x_212_, 1);
v___x_214_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharValUp___closed__5, &l_Lean_Meta_Grind_propagateCharValUp___closed__5_once, _init_l_Lean_Meta_Grind_propagateCharValUp___closed__5);
v___x_215_ = l_Lean_Meta_mkCongrArg(v___x_214_, v_a_213_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_a_216_);
lean_dec_ref_known(v___x_215_, 1);
v___x_217_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharToNatUp___closed__9, &l_Lean_Meta_Grind_propagateCharToNatUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__9);
v___x_218_ = l_Lean_Expr_app___override(v___x_214_, v_self_195_);
v___x_219_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharToNatUp___closed__12, &l_Lean_Meta_Grind_propagateCharToNatUp___closed__12_once, _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__12);
lean_inc_n(v_a_211_, 2);
v___x_220_ = l_Lean_mkAppB(v___x_219_, v___x_205_, v_a_211_);
lean_inc_ref(v_e_172_);
v___x_221_ = l_Lean_mkApp6(v___x_217_, v___x_205_, v_e_172_, v___x_218_, v_a_211_, v_a_216_, v___x_220_);
v___x_222_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_172_, v_a_173_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_225_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_a_223_);
lean_dec_ref_known(v___x_222_, 1);
lean_inc_ref(v_e_172_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v_e_172_);
v___x_225_ = v___x_203_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_e_172_);
v___x_225_ = v_reuseFailAlloc_229_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; 
lean_inc(v_a_182_);
lean_inc_ref(v_a_181_);
lean_inc(v_a_180_);
lean_inc_ref(v_a_179_);
lean_inc(v_a_178_);
lean_inc_ref(v_a_177_);
lean_inc(v_a_176_);
lean_inc_ref(v_a_175_);
lean_inc(v_a_174_);
lean_inc(v_a_173_);
lean_inc(v_a_211_);
v___x_226_ = lean_grind_internalize(v_a_211_, v_a_223_, v___x_225_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_226_) == 0)
{
uint8_t v___x_227_; lean_object* v___x_228_; 
lean_dec_ref_known(v___x_226_, 1);
v___x_227_ = 0;
v___x_228_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_172_, v_a_211_, v___x_221_, v___x_227_, v_a_173_, v_a_175_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
return v___x_228_;
}
else
{
lean_dec_ref(v___x_221_);
lean_dec(v_a_211_);
lean_dec_ref(v_e_172_);
return v___x_226_;
}
}
}
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_dec_ref(v___x_221_);
lean_dec(v_a_211_);
lean_del_object(v___x_203_);
lean_dec_ref(v_e_172_);
v_a_230_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_222_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_222_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_dec(v_a_211_);
lean_del_object(v___x_203_);
lean_dec_ref(v_self_195_);
lean_dec_ref(v_e_172_);
v_a_238_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_215_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_215_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec(v_a_211_);
lean_del_object(v___x_203_);
lean_dec_ref(v_self_195_);
lean_dec_ref(v_e_172_);
v_a_246_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_212_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_212_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_del_object(v___x_203_);
lean_dec_ref(v_self_195_);
lean_dec_ref(v_arg_189_);
lean_dec_ref(v_e_172_);
v_a_254_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_210_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_210_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_del_object(v___x_203_);
lean_dec_ref(v_self_195_);
lean_dec_ref(v_arg_189_);
lean_dec_ref(v_e_172_);
v_a_262_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_208_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_208_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
else
{
lean_object* v___x_271_; lean_object* v___x_273_; 
lean_dec(v_a_197_);
lean_dec_ref(v_self_195_);
lean_dec_ref(v_arg_189_);
lean_dec_ref(v_e_172_);
v___x_271_ = lean_box(0);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_271_);
v___x_273_ = v___x_199_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref(v_self_195_);
lean_dec_ref(v_arg_189_);
lean_dec_ref(v_e_172_);
v_a_276_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_196_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_196_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec_ref(v_arg_189_);
lean_dec_ref(v_e_172_);
v_a_284_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_193_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_193_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
v___jp_184_:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_box(0);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCharValUp___boxed(lean_object* v_e_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_Grind_propagateCharValUp(v_e_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec(v_a_293_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharValUp___regBuiltin_Lean_Meta_Grind_propagateCharValUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_3780693866____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharValUp___closed__1));
v___x_307_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateCharValUp___boxed), 12, 0);
v___x_308_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_306_, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharValUp___regBuiltin_Lean_Meta_Grind_propagateCharValUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_3780693866____hygCtx___hyg_9____boxed(lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharValUp___regBuiltin_Lean_Meta_Grind_propagateCharValUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_3780693866____hygCtx___hyg_9_();
return v_res_310_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateCharOfNatUp___closed__2(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_box(0);
v___x_316_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharOfNatUp___closed__1));
v___x_317_ = l_Lean_mkConst(v___x_316_, v___x_315_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateCharOfNatUp___closed__4(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_box(0);
v___x_321_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharOfNatUp___closed__3));
v___x_322_ = l_Lean_mkConst(v___x_321_, v___x_320_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCharOfNatUp(lean_object* v_e_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v___x_338_; uint8_t v___x_339_; 
lean_inc_ref(v_e_323_);
v___x_338_ = l_Lean_Expr_cleanupAnnotations(v_e_323_);
v___x_339_ = l_Lean_Expr_isApp(v___x_338_);
if (v___x_339_ == 0)
{
lean_dec_ref(v___x_338_);
lean_dec_ref(v_e_323_);
goto v___jp_335_;
}
else
{
lean_object* v_arg_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_arg_340_ = lean_ctor_get(v___x_338_, 1);
lean_inc_ref(v_arg_340_);
v___x_341_ = l_Lean_Expr_appFnCleanup___redArg(v___x_338_);
v___x_342_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharOfNatUp___closed__1));
v___x_343_ = l_Lean_Expr_isConstOf(v___x_341_, v___x_342_);
lean_dec_ref(v___x_341_);
if (v___x_343_ == 0)
{
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_e_323_);
goto v___jp_335_;
}
else
{
uint8_t v___x_344_; 
v___x_344_ = l_Lean_Expr_isCharLit(v_e_323_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
lean_inc_ref(v_arg_340_);
v___x_345_ = l_Lean_Meta_Grind_getRootENode___redArg(v_arg_340_, v_a_324_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v_self_347_; lean_object* v___x_348_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_345_, 1);
v_self_347_ = lean_ctor_get(v_a_346_, 0);
lean_inc_ref(v_self_347_);
lean_dec(v_a_346_);
v___x_348_ = l_Lean_Meta_getNatValue_x3f(v_self_347_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_418_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_418_ == 0)
{
v___x_351_ = v___x_348_;
v_isShared_352_ = v_isSharedCheck_418_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_418_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
if (lean_obj_tag(v_a_349_) == 1)
{
lean_object* v_val_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_413_; 
lean_del_object(v___x_351_);
v_val_353_ = lean_ctor_get(v_a_349_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v_a_349_);
if (v_isSharedCheck_413_ == 0)
{
v___x_355_ = v_a_349_;
v_isShared_356_ = v_isSharedCheck_413_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_val_353_);
lean_dec(v_a_349_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_413_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
uint32_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_357_ = l_Char_ofNat(v_val_353_);
lean_dec(v_val_353_);
v___x_358_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharOfNatUp___closed__2, &l_Lean_Meta_Grind_propagateCharOfNatUp___closed__2_once, _init_l_Lean_Meta_Grind_propagateCharOfNatUp___closed__2);
v___x_359_ = lean_uint32_to_nat(v___x_357_);
v___x_360_ = l_Lean_mkRawNatLit(v___x_359_);
v___x_361_ = l_Lean_Expr_app___override(v___x_358_, v___x_360_);
v___x_362_ = l_Lean_Meta_Sym_shareCommon(v___x_361_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_364_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_362_, 1);
lean_inc(v_a_333_);
lean_inc_ref(v_a_332_);
lean_inc(v_a_331_);
lean_inc_ref(v_a_330_);
lean_inc(v_a_329_);
lean_inc_ref(v_a_328_);
lean_inc(v_a_327_);
lean_inc_ref(v_a_326_);
lean_inc(v_a_325_);
lean_inc(v_a_324_);
lean_inc_ref(v_self_347_);
v___x_364_ = lean_grind_mk_eq_proof(v_arg_340_, v_self_347_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_366_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_365_);
lean_dec_ref_known(v___x_364_, 1);
v___x_366_ = l_Lean_Meta_mkCongrArg(v___x_358_, v_a_365_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_367_);
lean_dec_ref_known(v___x_366_, 1);
v___x_368_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharToNatUp___closed__9, &l_Lean_Meta_Grind_propagateCharToNatUp___closed__9_once, _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__9);
v___x_369_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharOfNatUp___closed__4, &l_Lean_Meta_Grind_propagateCharOfNatUp___closed__4_once, _init_l_Lean_Meta_Grind_propagateCharOfNatUp___closed__4);
v___x_370_ = l_Lean_Expr_app___override(v___x_358_, v_self_347_);
v___x_371_ = lean_obj_once(&l_Lean_Meta_Grind_propagateCharToNatUp___closed__12, &l_Lean_Meta_Grind_propagateCharToNatUp___closed__12_once, _init_l_Lean_Meta_Grind_propagateCharToNatUp___closed__12);
lean_inc_n(v_a_363_, 2);
v___x_372_ = l_Lean_mkAppB(v___x_371_, v___x_369_, v_a_363_);
lean_inc_ref(v_e_323_);
v___x_373_ = l_Lean_mkApp6(v___x_368_, v___x_369_, v_e_323_, v___x_370_, v_a_363_, v_a_367_, v___x_372_);
v___x_374_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_323_, v_a_324_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_377_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_374_, 1);
lean_inc_ref(v_e_323_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v_e_323_);
v___x_377_ = v___x_355_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_e_323_);
v___x_377_ = v_reuseFailAlloc_380_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; 
lean_inc(v_a_333_);
lean_inc_ref(v_a_332_);
lean_inc(v_a_331_);
lean_inc_ref(v_a_330_);
lean_inc(v_a_329_);
lean_inc_ref(v_a_328_);
lean_inc(v_a_327_);
lean_inc_ref(v_a_326_);
lean_inc(v_a_325_);
lean_inc(v_a_324_);
lean_inc(v_a_363_);
v___x_378_ = lean_grind_internalize(v_a_363_, v_a_375_, v___x_377_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v___x_379_; 
lean_dec_ref_known(v___x_378_, 1);
v___x_379_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_323_, v_a_363_, v___x_373_, v___x_344_, v_a_324_, v_a_326_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
return v___x_379_;
}
else
{
lean_dec_ref(v___x_373_);
lean_dec(v_a_363_);
lean_dec_ref(v_e_323_);
return v___x_378_;
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec_ref(v___x_373_);
lean_dec(v_a_363_);
lean_del_object(v___x_355_);
lean_dec_ref(v_e_323_);
v_a_381_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_374_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_374_);
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
lean_dec(v_a_363_);
lean_del_object(v___x_355_);
lean_dec_ref(v_self_347_);
lean_dec_ref(v_e_323_);
v_a_389_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_366_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_366_);
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
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec(v_a_363_);
lean_del_object(v___x_355_);
lean_dec_ref(v_self_347_);
lean_dec_ref(v_e_323_);
v_a_397_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_364_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_364_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_del_object(v___x_355_);
lean_dec_ref(v_self_347_);
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_e_323_);
v_a_405_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_362_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_362_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
else
{
lean_object* v___x_414_; lean_object* v___x_416_; 
lean_dec(v_a_349_);
lean_dec_ref(v_self_347_);
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_e_323_);
v___x_414_ = lean_box(0);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_414_);
v___x_416_ = v___x_351_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec_ref(v_self_347_);
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_e_323_);
v_a_419_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_348_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_348_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_e_323_);
v_a_427_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_345_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_345_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_e_323_);
v___x_435_ = lean_box(0);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
}
v___jp_335_:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_box(0);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCharOfNatUp___boxed(lean_object* v_e_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_Meta_Grind_propagateCharOfNatUp(v_e_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec(v_a_438_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharOfNatUp___regBuiltin_Lean_Meta_Grind_propagateCharOfNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_1207922169____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = ((lean_object*)(l_Lean_Meta_Grind_propagateCharOfNatUp___closed__1));
v___x_452_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateCharOfNatUp___boxed), 12, 0);
v___x_453_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_451_, v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharOfNatUp___regBuiltin_Lean_Meta_Grind_propagateCharOfNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_1207922169____hygCtx___hyg_9____boxed(lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l___private_Lean_Meta_Tactic_Grind_PropagateChar_0__Lean_Meta_Grind_propagateCharOfNatUp___regBuiltin_Lean_Meta_Grind_propagateCharOfNatUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateChar_1207922169____hygCtx___hyg_9_();
return v_res_455_;
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
