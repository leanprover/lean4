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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_ctorIdx___boxed(lean_object*);
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
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_7_ = lean_box(0);
v___x_8_ = lean_box(0);
v___x_9_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2, &l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2);
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_9_);
lean_ctor_set(v___x_11_, 2, v___x_8_);
lean_ctor_set(v___x_11_, 3, v___x_9_);
lean_ctor_set(v___x_11_, 4, v___x_7_);
lean_ctor_set(v___x_11_, 5, v___x_7_);
lean_ctor_set(v___x_11_, 6, v___x_7_);
lean_ctor_set(v___x_11_, 7, v___x_7_);
lean_ctor_set(v___x_11_, 8, v___x_7_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__3, &l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__3_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__3);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default;
return v___x_13_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedRing_default___closed__0(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_14_ = lean_box(0);
v___x_15_ = lean_box(0);
v___x_16_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2, &l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2);
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
lean_ctor_set(v___x_18_, 1, v___x_16_);
lean_ctor_set(v___x_18_, 2, v___x_15_);
lean_ctor_set(v___x_18_, 3, v___x_16_);
lean_ctor_set(v___x_18_, 4, v___x_16_);
lean_ctor_set(v___x_18_, 5, v___x_14_);
lean_ctor_set(v___x_18_, 6, v___x_14_);
lean_ctor_set(v___x_18_, 7, v___x_14_);
lean_ctor_set(v___x_18_, 8, v___x_14_);
lean_ctor_set(v___x_18_, 9, v___x_14_);
lean_ctor_set(v___x_18_, 10, v___x_14_);
lean_ctor_set(v___x_18_, 11, v___x_14_);
lean_ctor_set(v___x_18_, 12, v___x_14_);
lean_ctor_set(v___x_18_, 13, v___x_14_);
lean_ctor_set(v___x_18_, 14, v___x_14_);
lean_ctor_set(v___x_18_, 15, v___x_14_);
return v___x_18_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedRing_default(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedRing_default___closed__0, &l_Lean_Meta_Sym_Arith_instInhabitedRing_default___closed__0_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedRing_default___closed__0);
return v___x_19_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedRing(void){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Meta_Sym_Arith_instInhabitedRing_default;
return v___x_20_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default___closed__0(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_21_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2, &l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2);
v___x_22_ = lean_box(0);
v___x_23_ = l_Lean_Meta_Sym_Arith_instInhabitedRing_default;
v___x_24_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
lean_ctor_set(v___x_24_, 1, v___x_22_);
lean_ctor_set(v___x_24_, 2, v___x_22_);
lean_ctor_set(v___x_24_, 3, v___x_22_);
lean_ctor_set(v___x_24_, 4, v___x_21_);
lean_ctor_set(v___x_24_, 5, v___x_21_);
lean_ctor_set(v___x_24_, 6, v___x_22_);
lean_ctor_set(v___x_24_, 7, v___x_22_);
lean_ctor_set(v___x_24_, 8, v___x_22_);
return v___x_24_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default(void){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default___closed__0, &l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default___closed__0_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default___closed__0);
return v___x_25_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedCommRing(void){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default;
return v___x_26_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default___closed__0(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_27_ = lean_box(0);
v___x_28_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2, &l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2);
v___x_29_ = lean_unsigned_to_nat(0u);
v___x_30_ = l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default;
v___x_31_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
lean_ctor_set(v___x_31_, 1, v___x_29_);
lean_ctor_set(v___x_31_, 2, v___x_28_);
lean_ctor_set(v___x_31_, 3, v___x_27_);
lean_ctor_set(v___x_31_, 4, v___x_27_);
return v___x_31_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default(void){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default___closed__0, &l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default___closed__0_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default___closed__0);
return v___x_32_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring(void){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default;
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_ctorIdx(lean_object* v_x_34_){
_start:
{
switch(lean_obj_tag(v_x_34_))
{
case 0:
{
lean_object* v___x_35_; 
v___x_35_ = lean_unsigned_to_nat(0u);
return v___x_35_;
}
case 1:
{
lean_object* v___x_36_; 
v___x_36_ = lean_unsigned_to_nat(1u);
return v___x_36_;
}
case 2:
{
lean_object* v___x_37_; 
v___x_37_ = lean_unsigned_to_nat(2u);
return v___x_37_;
}
case 3:
{
lean_object* v___x_38_; 
v___x_38_ = lean_unsigned_to_nat(3u);
return v___x_38_;
}
default: 
{
lean_object* v___x_39_; 
v___x_39_ = lean_unsigned_to_nat(4u);
return v___x_39_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_ctorIdx___boxed(lean_object* v_x_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorIdx(v_x_40_);
lean_dec(v_x_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(lean_object* v_t_42_, lean_object* v_k_43_){
_start:
{
if (lean_obj_tag(v_t_42_) == 4)
{
return v_k_43_;
}
else
{
lean_object* v_id_44_; lean_object* v___x_45_; 
v_id_44_ = lean_ctor_get(v_t_42_, 0);
lean_inc(v_id_44_);
lean_dec(v_t_42_);
v___x_45_ = lean_apply_1(v_k_43_, v_id_44_);
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim(lean_object* v_motive_46_, lean_object* v_ctorIdx_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_k_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_48_, v_k_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___boxed(lean_object* v_motive_52_, lean_object* v_ctorIdx_53_, lean_object* v_t_54_, lean_object* v_h_55_, lean_object* v_k_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim(v_motive_52_, v_ctorIdx_53_, v_t_54_, v_h_55_, v_k_56_);
lean_dec(v_ctorIdx_53_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_commRing_elim___redArg(lean_object* v_t_58_, lean_object* v_commRing_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_58_, v_commRing_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_commRing_elim(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_commRing_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_62_, v_commRing_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_nonCommRing_elim___redArg(lean_object* v_t_66_, lean_object* v_nonCommRing_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_66_, v_nonCommRing_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_nonCommRing_elim(lean_object* v_motive_69_, lean_object* v_t_70_, lean_object* v_h_71_, lean_object* v_nonCommRing_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_70_, v_nonCommRing_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_commSemiring_elim___redArg(lean_object* v_t_74_, lean_object* v_commSemiring_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_74_, v_commSemiring_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_commSemiring_elim(lean_object* v_motive_77_, lean_object* v_t_78_, lean_object* v_h_79_, lean_object* v_commSemiring_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_78_, v_commSemiring_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_nonCommSemiring_elim___redArg(lean_object* v_t_82_, lean_object* v_nonCommSemiring_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_82_, v_nonCommSemiring_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_nonCommSemiring_elim(lean_object* v_motive_85_, lean_object* v_t_86_, lean_object* v_h_87_, lean_object* v_nonCommSemiring_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_86_, v_nonCommSemiring_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_none_elim___redArg(lean_object* v_t_90_, lean_object* v_none_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_90_, v_none_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ClassifyResult_none_elim(lean_object* v_motive_93_, lean_object* v_t_94_, lean_object* v_h_95_, lean_object* v_none_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Meta_Sym_Arith_ClassifyResult_ctorElim___redArg(v_t_94_, v_none_96_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedOrder_default___closed__0(void){
_start:
{
uint8_t v___x_102_; uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_102_ = 1;
v___x_103_ = 0;
v___x_104_ = lean_box(0);
v___x_105_ = lean_box(0);
v___x_106_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2, &l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default___closed__2);
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_106_);
lean_ctor_set(v___x_108_, 2, v___x_105_);
lean_ctor_set(v___x_108_, 3, v___x_106_);
lean_ctor_set(v___x_108_, 4, v___x_106_);
lean_ctor_set(v___x_108_, 5, v___x_104_);
lean_ctor_set(v___x_108_, 6, v___x_104_);
lean_ctor_set(v___x_108_, 7, v___x_104_);
lean_ctor_set(v___x_108_, 8, v___x_104_);
lean_ctor_set(v___x_108_, 9, v___x_104_);
lean_ctor_set(v___x_108_, 10, v___x_104_);
lean_ctor_set(v___x_108_, 11, v___x_104_);
lean_ctor_set(v___x_108_, 12, v___x_104_);
lean_ctor_set(v___x_108_, 13, v___x_106_);
lean_ctor_set(v___x_108_, 14, v___x_104_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*15, v___x_103_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*15 + 1, v___x_102_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedOrder_default(void){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedOrder_default___closed__0, &l_Lean_Meta_Sym_Arith_instInhabitedOrder_default___closed__0_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedOrder_default___closed__0);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedOrder(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Meta_Sym_Arith_instInhabitedOrder_default;
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1, &l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_116_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2, &l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2);
v___x_117_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__0));
v___x_118_ = lean_unsigned_to_nat(1048576u);
v___x_119_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v___x_117_);
lean_ctor_set(v___x_119_, 2, v___x_117_);
lean_ctor_set(v___x_119_, 3, v___x_117_);
lean_ctor_set(v___x_119_, 4, v___x_117_);
lean_ctor_set(v___x_119_, 5, v___x_116_);
lean_ctor_set(v___x_119_, 6, v___x_117_);
lean_ctor_set(v___x_119_, 7, v___x_116_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default(void){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3, &l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedState(void){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_Meta_Sym_Arith_instInhabitedState_default;
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_(lean_object* v___x_122_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_122_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2____boxed(lean_object* v___x_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_(v___x_125_);
return v_res_127_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_128_; lean_object* v___f_129_; 
v___x_128_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3, &l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3);
v___f_129_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_129_, 0, v___x_128_);
return v___f_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_131_; lean_object* v___x_132_; 
v___f_131_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_);
v___x_132_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v___f_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2____boxed(lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_Meta_Sym_Arith_Types_0__Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_();
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg(lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_139_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v___x_138_, v_a_135_, v_a_136_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg___boxed(lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_140_, v_a_141_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getArithState(lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_145_, v_a_148_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getArithState___boxed(lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Meta_Sym_Arith_getArithState(v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_modifyArithState___redArg(lean_object* v_f_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_164_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_163_, v_f_160_, v_a_161_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_modifyArithState___redArg___boxed(lean_object* v_f_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Meta_Sym_Arith_modifyArithState___redArg(v_f_165_, v_a_166_);
lean_dec(v_a_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_modifyArithState(lean_object* v_f_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_178_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_177_, v_f_169_, v_a_171_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_modifyArithState___boxed(lean_object* v_f_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Meta_Sym_Arith_modifyArithState(v_f_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold___redArg(lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_188_, v_a_189_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_200_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_200_ == 0)
{
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_200_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_200_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v_exp_196_; lean_object* v___x_198_; 
v_exp_196_ = lean_ctor_get(v_a_192_, 0);
lean_inc(v_exp_196_);
lean_dec(v_a_192_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v_exp_196_);
v___x_198_ = v___x_194_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_exp_196_);
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
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
v_a_201_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_191_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_191_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold___redArg___boxed(lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Meta_Sym_Arith_getExpThreshold___redArg(v_a_209_, v_a_210_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold(lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Meta_Sym_Arith_getExpThreshold___redArg(v_a_214_, v_a_217_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold___boxed(lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Meta_Sym_Arith_getExpThreshold(v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold___redArg___lam__0(lean_object* v_exp_229_, lean_object* v_s_230_){
_start:
{
lean_object* v_rings_231_; lean_object* v_semirings_232_; lean_object* v_ncRings_233_; lean_object* v_ncSemirings_234_; lean_object* v_typeClassify_235_; lean_object* v_orders_236_; lean_object* v_typeOrderClassify_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
v_rings_231_ = lean_ctor_get(v_s_230_, 1);
v_semirings_232_ = lean_ctor_get(v_s_230_, 2);
v_ncRings_233_ = lean_ctor_get(v_s_230_, 3);
v_ncSemirings_234_ = lean_ctor_get(v_s_230_, 4);
v_typeClassify_235_ = lean_ctor_get(v_s_230_, 5);
v_orders_236_ = lean_ctor_get(v_s_230_, 6);
v_typeOrderClassify_237_ = lean_ctor_get(v_s_230_, 7);
v_isSharedCheck_244_ = !lean_is_exclusive(v_s_230_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v_s_230_, 0);
lean_dec(v_unused_245_);
v___x_239_ = v_s_230_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_typeOrderClassify_237_);
lean_inc(v_orders_236_);
lean_inc(v_typeClassify_235_);
lean_inc(v_ncSemirings_234_);
lean_inc(v_ncRings_233_);
lean_inc(v_semirings_232_);
lean_inc(v_rings_231_);
lean_dec(v_s_230_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 0, v_exp_229_);
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_exp_229_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_rings_231_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_semirings_232_);
lean_ctor_set(v_reuseFailAlloc_243_, 3, v_ncRings_233_);
lean_ctor_set(v_reuseFailAlloc_243_, 4, v_ncSemirings_234_);
lean_ctor_set(v_reuseFailAlloc_243_, 5, v_typeClassify_235_);
lean_ctor_set(v_reuseFailAlloc_243_, 6, v_orders_236_);
lean_ctor_set(v_reuseFailAlloc_243_, 7, v_typeOrderClassify_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(lean_object* v_exp_246_, lean_object* v_a_247_){
_start:
{
lean_object* v___f_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___f_249_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_setExpThreshold___redArg___lam__0), 2, 1);
lean_closure_set(v___f_249_, 0, v_exp_246_);
v___x_250_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_251_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_250_, v___f_249_, v_a_247_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold___redArg___boxed(lean_object* v_exp_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_252_, v_a_253_);
lean_dec(v_a_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold(lean_object* v_exp_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_256_, v_a_258_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold___boxed(lean_object* v_exp_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Meta_Sym_Arith_setExpThreshold(v_exp_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_withExpThreshold___redArg(lean_object* v_exp_274_, lean_object* v_k_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_277_, v_a_280_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v_exp_285_; lean_object* v___x_286_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_284_);
lean_dec_ref_known(v___x_283_, 1);
v_exp_285_ = lean_ctor_get(v_a_284_, 0);
lean_inc(v_exp_285_);
lean_dec(v_a_284_);
v___x_286_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_274_, v_a_277_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_r_287_; 
lean_dec_ref_known(v___x_286_, 1);
lean_inc(v_a_281_);
lean_inc_ref(v_a_280_);
lean_inc(v_a_279_);
lean_inc_ref(v_a_278_);
lean_inc(v_a_277_);
lean_inc_ref(v_a_276_);
v_r_287_ = lean_apply_7(v_k_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, lean_box(0));
if (lean_obj_tag(v_r_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_289_; 
v_a_288_ = lean_ctor_get(v_r_287_, 0);
lean_inc(v_a_288_);
lean_dec_ref_known(v_r_287_, 1);
v___x_289_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_285_, v_a_277_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; 
v_unused_297_ = lean_ctor_get(v___x_289_, 0);
lean_dec(v_unused_297_);
v___x_291_ = v___x_289_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_dec(v___x_289_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v_a_288_);
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_288_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec(v_a_288_);
v_a_298_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_289_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_289_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
else
{
lean_object* v_a_306_; lean_object* v___x_307_; 
v_a_306_ = lean_ctor_get(v_r_287_, 0);
lean_inc(v_a_306_);
lean_dec_ref_known(v_r_287_, 1);
v___x_307_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_285_, v_a_277_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; 
v_unused_315_ = lean_ctor_get(v___x_307_, 0);
lean_dec(v_unused_315_);
v___x_309_ = v___x_307_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_dec(v___x_307_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set_tag(v___x_309_, 1);
lean_ctor_set(v___x_309_, 0, v_a_306_);
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_306_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec(v_a_306_);
v_a_316_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_307_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_307_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec(v_exp_285_);
lean_dec_ref(v_k_275_);
v_a_324_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_286_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_286_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_dec_ref(v_k_275_);
lean_dec(v_exp_274_);
v_a_332_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_283_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_283_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_withExpThreshold___redArg___boxed(lean_object* v_exp_340_, lean_object* v_k_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Meta_Sym_Arith_withExpThreshold___redArg(v_exp_340_, v_k_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_withExpThreshold(lean_object* v_00_u03b1_350_, lean_object* v_exp_351_, lean_object* v_k_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Meta_Sym_Arith_withExpThreshold___redArg(v_exp_351_, v_k_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_withExpThreshold___boxed(lean_object* v_00_u03b1_361_, lean_object* v_exp_362_, lean_object* v_k_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Meta_Sym_Arith_withExpThreshold(v_00_u03b1_361_, v_exp_362_, v_k_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
return v_res_371_;
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
