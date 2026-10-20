// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Types
// Imports: public import Init.Grind.Ring.CommSemiringAdapter public import Lean.Meta.Sym.SymM
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Sym_registerSymExtension___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_SymExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instInhabitedSemiring;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_instInhabitedRing_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_instInhabitedRing_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instInhabitedRing_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instInhabitedRing;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instInhabitedCommRing;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_commRing_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_commRing_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_nonCommRing_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_nonCommRing_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_commSemiring_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_commSemiring_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_nonCommSemiring_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_nonCommSemiring_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_none_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instInhabitedClassifyResult_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_Arith_instInhabitedClassifyResult_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_instInhabitedClassifyResult_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Arith_instInhabitedClassifyResult_default = (const lean_object*)&l_Lean_Meta_Sym_Arith_instInhabitedClassifyResult_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Arith_instInhabitedClassifyResult = (const lean_object*)&l_Lean_Meta_Sym_Arith_instInhabitedClassifyResult_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_instInhabitedOrder_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_instInhabitedOrder_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instInhabitedOrder_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instInhabitedOrder;
static const lean_array_object l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instInhabitedState;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_arithExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getArithState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getArithState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_modifyArithState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_modifyArithState___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_modifyArithState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_modifyArithState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_withExpThreshold___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_withExpThreshold___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_withExpThreshold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_withExpThreshold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__3(void){
_start:
{
uint8_t v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_7_ = 0;
v___x_8_ = lean_box(0);
v___x_9_ = lean_box(0);
v___x_10_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2, &l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2);
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
lean_ctor_set(v___x_12_, 2, v___x_9_);
lean_ctor_set(v___x_12_, 3, v___x_10_);
lean_ctor_set(v___x_12_, 4, v___x_8_);
lean_ctor_set(v___x_12_, 5, v___x_8_);
lean_ctor_set(v___x_12_, 6, v___x_8_);
lean_ctor_set(v___x_12_, 7, v___x_8_);
lean_ctor_set(v___x_12_, 8, v___x_8_);
lean_ctor_set(v___x_12_, 9, v___x_8_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*10, v___x_7_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__3, &l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__3_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__3);
return v___x_13_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default;
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedRing_default___closed__0(void){
_start:
{
uint8_t v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_15_ = 0;
v___x_16_ = lean_box(0);
v___x_17_ = lean_box(0);
v___x_18_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2, &l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2);
v___x_19_ = lean_unsigned_to_nat(0u);
v___x_20_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v___x_18_);
lean_ctor_set(v___x_20_, 2, v___x_17_);
lean_ctor_set(v___x_20_, 3, v___x_18_);
lean_ctor_set(v___x_20_, 4, v___x_18_);
lean_ctor_set(v___x_20_, 5, v___x_16_);
lean_ctor_set(v___x_20_, 6, v___x_16_);
lean_ctor_set(v___x_20_, 7, v___x_16_);
lean_ctor_set(v___x_20_, 8, v___x_16_);
lean_ctor_set(v___x_20_, 9, v___x_16_);
lean_ctor_set(v___x_20_, 10, v___x_16_);
lean_ctor_set(v___x_20_, 11, v___x_16_);
lean_ctor_set(v___x_20_, 12, v___x_16_);
lean_ctor_set(v___x_20_, 13, v___x_16_);
lean_ctor_set(v___x_20_, 14, v___x_16_);
lean_ctor_set(v___x_20_, 15, v___x_16_);
lean_ctor_set_uint8(v___x_20_, sizeof(void*)*16, v___x_15_);
return v___x_20_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedRing_default(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedRing_default___closed__0, &l_Lean_Meta_Sym_Arith_instInhabitedRing_default___closed__0_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedRing_default___closed__0);
return v___x_21_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedRing(void){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Lean_Meta_Sym_Arith_instInhabitedRing_default;
return v___x_22_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default___closed__0(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_23_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2, &l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2);
v___x_24_ = lean_box(0);
v___x_25_ = l_Lean_Meta_Sym_Arith_instInhabitedRing_default;
v___x_26_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
lean_ctor_set(v___x_26_, 1, v___x_24_);
lean_ctor_set(v___x_26_, 2, v___x_24_);
lean_ctor_set(v___x_26_, 3, v___x_24_);
lean_ctor_set(v___x_26_, 4, v___x_23_);
lean_ctor_set(v___x_26_, 5, v___x_23_);
lean_ctor_set(v___x_26_, 6, v___x_24_);
lean_ctor_set(v___x_26_, 7, v___x_24_);
lean_ctor_set(v___x_26_, 8, v___x_24_);
return v___x_26_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default(void){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default___closed__0, &l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default___closed__0_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default___closed__0);
return v___x_27_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedCommRing(void){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default;
return v___x_28_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default___closed__0(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_29_ = lean_box(0);
v___x_30_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2, &l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default;
v___x_33_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v___x_31_);
lean_ctor_set(v___x_33_, 2, v___x_30_);
lean_ctor_set(v___x_33_, 3, v___x_29_);
lean_ctor_set(v___x_33_, 4, v___x_29_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default(void){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default___closed__0, &l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default___closed__0_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default___closed__0);
return v___x_34_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring(void){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default;
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_ctorIdx___impl(lean_object* v_x_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_obj_tag_nat(v_x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_ctorIdx___impl___boxed(lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorIdx___impl(v_x_38_);
lean_dec(v_x_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(lean_object* v_t_40_, lean_object* v_k_41_){
_start:
{
if (lean_obj_tag(v_t_40_) == 4)
{
return v_k_41_;
}
else
{
lean_object* v_id_42_; lean_object* v___x_43_; 
v_id_42_ = lean_ctor_get(v_t_40_, 0);
lean_inc(v_id_42_);
lean_dec(v_t_40_);
v___x_43_ = lean_apply_1(v_k_41_, v_id_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim(lean_object* v_motive_44_, lean_object* v_ctorIdx_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_k_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_46_, v_k_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___boxed(lean_object* v_motive_50_, lean_object* v_ctorIdx_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_k_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim(v_motive_50_, v_ctorIdx_51_, v_t_52_, v_h_53_, v_k_54_);
lean_dec(v_ctorIdx_51_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_commRing_elim___redArg(lean_object* v_t_56_, lean_object* v_commRing_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_56_, v_commRing_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_commRing_elim(lean_object* v_motive_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_commRing_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_60_, v_commRing_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_nonCommRing_elim___redArg(lean_object* v_t_64_, lean_object* v_nonCommRing_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_64_, v_nonCommRing_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_nonCommRing_elim(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_nonCommRing_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_68_, v_nonCommRing_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_commSemiring_elim___redArg(lean_object* v_t_72_, lean_object* v_commSemiring_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_72_, v_commSemiring_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_commSemiring_elim(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_commSemiring_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_76_, v_commSemiring_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_nonCommSemiring_elim___redArg(lean_object* v_t_80_, lean_object* v_nonCommSemiring_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_80_, v_nonCommSemiring_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_nonCommSemiring_elim(lean_object* v_motive_83_, lean_object* v_t_84_, lean_object* v_h_85_, lean_object* v_nonCommSemiring_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_84_, v_nonCommSemiring_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_none_elim___redArg(lean_object* v_t_88_, lean_object* v_none_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_88_, v_none_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_none_elim(lean_object* v_motive_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_none_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_92_, v_none_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedOrder_default___closed__0(void){
_start:
{
uint8_t v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_100_ = 1;
v___x_101_ = 0;
v___x_102_ = lean_box(0);
v___x_103_ = lean_box(0);
v___x_104_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2, &l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2);
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___x_104_);
lean_ctor_set(v___x_106_, 2, v___x_103_);
lean_ctor_set(v___x_106_, 3, v___x_104_);
lean_ctor_set(v___x_106_, 4, v___x_104_);
lean_ctor_set(v___x_106_, 5, v___x_102_);
lean_ctor_set(v___x_106_, 6, v___x_102_);
lean_ctor_set(v___x_106_, 7, v___x_102_);
lean_ctor_set(v___x_106_, 8, v___x_102_);
lean_ctor_set(v___x_106_, 9, v___x_102_);
lean_ctor_set(v___x_106_, 10, v___x_102_);
lean_ctor_set(v___x_106_, 11, v___x_102_);
lean_ctor_set(v___x_106_, 12, v___x_102_);
lean_ctor_set(v___x_106_, 13, v___x_104_);
lean_ctor_set(v___x_106_, 14, v___x_102_);
lean_ctor_set_uint8(v___x_106_, sizeof(void*)*15, v___x_101_);
lean_ctor_set_uint8(v___x_106_, sizeof(void*)*15 + 1, v___x_100_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedOrder_default(void){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedOrder_default___closed__0, &l_Lean_Meta_Sym_Arith_instInhabitedOrder_default___closed__0_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedOrder_default___closed__0);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedOrder(void){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_Meta_Sym_Arith_instInhabitedOrder_default;
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1, &l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_114_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2, &l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2);
v___x_115_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__0));
v___x_116_ = lean_unsigned_to_nat(1048576u);
v___x_117_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
lean_ctor_set(v___x_117_, 2, v___x_115_);
lean_ctor_set(v___x_117_, 3, v___x_115_);
lean_ctor_set(v___x_117_, 4, v___x_115_);
lean_ctor_set(v___x_117_, 5, v___x_114_);
lean_ctor_set(v___x_117_, 6, v___x_115_);
lean_ctor_set(v___x_117_, 7, v___x_114_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3, &l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedState(void){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Meta_Sym_Arith_instInhabitedState_default;
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_(lean_object* v___x_120_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_120_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2____boxed(lean_object* v___x_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_(v___x_123_);
return v_res_125_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_126_; lean_object* v___f_127_; 
v___x_126_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3, &l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3);
v___f_127_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_127_, 0, v___x_126_);
return v___f_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_129_; lean_object* v___x_130_; 
v___f_129_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_);
v___x_130_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v___f_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2____boxed(lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_();
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg(lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_137_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v___x_136_, v_a_133_, v_a_134_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg___boxed(lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_138_, v_a_139_);
lean_dec_ref(v_a_139_);
lean_dec(v_a_138_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getArithState(lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_143_, v_a_146_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getArithState___boxed(lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Meta_Sym_Arith_getArithState(v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_modifyArithState___redArg(lean_object* v_f_158_, lean_object* v_a_159_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_162_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_161_, v_f_158_, v_a_159_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_modifyArithState___redArg___boxed(lean_object* v_f_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Meta_Sym_Arith_modifyArithState___redArg(v_f_163_, v_a_164_);
lean_dec(v_a_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_modifyArithState(lean_object* v_f_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_176_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_175_, v_f_167_, v_a_169_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_modifyArithState___boxed(lean_object* v_f_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Meta_Sym_Arith_modifyArithState(v_f_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold___redArg(lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_186_, v_a_187_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_198_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_198_ == 0)
{
v___x_192_ = v___x_189_;
v_isShared_193_ = v_isSharedCheck_198_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_198_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v_exp_194_; lean_object* v___x_196_; 
v_exp_194_ = lean_ctor_get(v_a_190_, 0);
lean_inc(v_exp_194_);
lean_dec(v_a_190_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v_exp_194_);
v___x_196_ = v___x_192_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_exp_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
v_a_199_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_189_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_189_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold___redArg___boxed(lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Meta_Sym_Arith_getExpThreshold___redArg(v_a_207_, v_a_208_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold(lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Meta_Sym_Arith_getExpThreshold___redArg(v_a_212_, v_a_215_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold___boxed(lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Meta_Sym_Arith_getExpThreshold(v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold___redArg___lam__0(lean_object* v_exp_227_, lean_object* v_s_228_){
_start:
{
lean_object* v_rings_229_; lean_object* v_semirings_230_; lean_object* v_ncRings_231_; lean_object* v_ncSemirings_232_; lean_object* v_typeClassify_233_; lean_object* v_orders_234_; lean_object* v_typeOrderClassify_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
v_rings_229_ = lean_ctor_get(v_s_228_, 1);
v_semirings_230_ = lean_ctor_get(v_s_228_, 2);
v_ncRings_231_ = lean_ctor_get(v_s_228_, 3);
v_ncSemirings_232_ = lean_ctor_get(v_s_228_, 4);
v_typeClassify_233_ = lean_ctor_get(v_s_228_, 5);
v_orders_234_ = lean_ctor_get(v_s_228_, 6);
v_typeOrderClassify_235_ = lean_ctor_get(v_s_228_, 7);
v_isSharedCheck_242_ = !lean_is_exclusive(v_s_228_);
if (v_isSharedCheck_242_ == 0)
{
lean_object* v_unused_243_; 
v_unused_243_ = lean_ctor_get(v_s_228_, 0);
lean_dec(v_unused_243_);
v___x_237_ = v_s_228_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_typeOrderClassify_235_);
lean_inc(v_orders_234_);
lean_inc(v_typeClassify_233_);
lean_inc(v_ncSemirings_232_);
lean_inc(v_ncRings_231_);
lean_inc(v_semirings_230_);
lean_inc(v_rings_229_);
lean_dec(v_s_228_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v_exp_227_);
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_exp_227_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_rings_229_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_semirings_230_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v_ncRings_231_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v_ncSemirings_232_);
lean_ctor_set(v_reuseFailAlloc_241_, 5, v_typeClassify_233_);
lean_ctor_set(v_reuseFailAlloc_241_, 6, v_orders_234_);
lean_ctor_set(v_reuseFailAlloc_241_, 7, v_typeOrderClassify_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(lean_object* v_exp_244_, lean_object* v_a_245_){
_start:
{
lean_object* v___f_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___f_247_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_setExpThreshold___redArg___lam__0), 2, 1);
lean_closure_set(v___f_247_, 0, v_exp_244_);
v___x_248_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_249_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_248_, v___f_247_, v_a_245_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold___redArg___boxed(lean_object* v_exp_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_250_, v_a_251_);
lean_dec(v_a_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold(lean_object* v_exp_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_254_, v_a_256_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold___boxed(lean_object* v_exp_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Meta_Sym_Arith_setExpThreshold(v_exp_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_withExpThreshold___redArg(lean_object* v_exp_272_, lean_object* v_k_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_275_, v_a_278_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; lean_object* v_exp_283_; lean_object* v___x_284_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_a_282_);
lean_dec_ref_known(v___x_281_, 1);
v_exp_283_ = lean_ctor_get(v_a_282_, 0);
lean_inc(v_exp_283_);
lean_dec(v_a_282_);
v___x_284_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_272_, v_a_275_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_r_285_; 
lean_dec_ref_known(v___x_284_, 1);
lean_inc(v_a_279_);
lean_inc_ref(v_a_278_);
lean_inc(v_a_277_);
lean_inc_ref(v_a_276_);
lean_inc(v_a_275_);
lean_inc_ref(v_a_274_);
v_r_285_ = lean_apply_7(v_k_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, lean_box(0));
if (lean_obj_tag(v_r_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_287_; 
v_a_286_ = lean_ctor_get(v_r_285_, 0);
lean_inc(v_a_286_);
lean_dec_ref_known(v_r_285_, 1);
v___x_287_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_283_, v_a_275_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v___x_287_, 0);
lean_dec(v_unused_295_);
v___x_289_ = v___x_287_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_dec(v___x_287_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v_a_286_);
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_286_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec(v_a_286_);
v_a_296_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_287_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_287_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_305_; 
v_a_304_ = lean_ctor_get(v_r_285_, 0);
lean_inc(v_a_304_);
lean_dec_ref_known(v_r_285_, 1);
v___x_305_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_283_, v_a_275_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_312_ == 0)
{
lean_object* v_unused_313_; 
v_unused_313_ = lean_ctor_get(v___x_305_, 0);
lean_dec(v_unused_313_);
v___x_307_ = v___x_305_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_dec(v___x_305_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set_tag(v___x_307_, 1);
lean_ctor_set(v___x_307_, 0, v_a_304_);
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_304_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_dec(v_a_304_);
v_a_314_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_305_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_305_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_dec(v_exp_283_);
lean_dec_ref(v_k_273_);
v_a_322_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_284_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_284_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec_ref(v_k_273_);
lean_dec(v_exp_272_);
v_a_330_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_281_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_281_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_withExpThreshold___redArg___boxed(lean_object* v_exp_338_, lean_object* v_k_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Meta_Sym_Arith_withExpThreshold___redArg(v_exp_338_, v_k_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_withExpThreshold(lean_object* v_00_u03b1_348_, lean_object* v_exp_349_, lean_object* v_k_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_Meta_Sym_Arith_withExpThreshold___redArg(v_exp_349_, v_k_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_withExpThreshold___boxed(lean_object* v_00_u03b1_359_, lean_object* v_exp_360_, lean_object* v_k_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Meta_Sym_Arith_withExpThreshold(v_00_u03b1_359_, v_exp_360_, v_k_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
return v_res_369_;
}
}
lean_object* runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default = _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default);
l_Lean_Meta_Sym_Arith_instInhabitedSemiring = _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedSemiring);
l_Lean_Meta_Sym_Arith_instInhabitedRing_default = _init_l_Lean_Meta_Sym_Arith_instInhabitedRing_default();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedRing_default);
l_Lean_Meta_Sym_Arith_instInhabitedRing = _init_l_Lean_Meta_Sym_Arith_instInhabitedRing();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedRing);
l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default = _init_l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default);
l_Lean_Meta_Sym_Arith_instInhabitedCommRing = _init_l_Lean_Meta_Sym_Arith_instInhabitedCommRing();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedCommRing);
l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default = _init_l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default);
l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring = _init_l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring);
l_Lean_Meta_Sym_Arith_instInhabitedOrder_default = _init_l_Lean_Meta_Sym_Arith_instInhabitedOrder_default();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedOrder_default);
l_Lean_Meta_Sym_Arith_instInhabitedOrder = _init_l_Lean_Meta_Sym_Arith_instInhabitedOrder();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedOrder);
l_Lean_Meta_Sym_Arith_instInhabitedState_default = _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedState_default);
l_Lean_Meta_Sym_Arith_instInhabitedState = _init_l_Lean_Meta_Sym_Arith_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedState);
res = l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Sym_Arith_arithExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Sym_Arith_arithExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_Types(builtin);
}
#ifdef __cplusplus
}
#endif
