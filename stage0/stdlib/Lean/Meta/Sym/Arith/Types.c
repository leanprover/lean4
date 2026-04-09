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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2____boxed(lean_object*);
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
v___x_11_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_9_);
lean_ctor_set(v___x_11_, 2, v___x_8_);
lean_ctor_set(v___x_11_, 3, v___x_9_);
lean_ctor_set(v___x_11_, 4, v___x_7_);
lean_ctor_set(v___x_11_, 5, v___x_7_);
lean_ctor_set(v___x_11_, 6, v___x_7_);
lean_ctor_set(v___x_11_, 7, v___x_7_);
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
v___x_18_ = lean_alloc_ctor(0, 14, 0);
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
v___x_24_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
lean_ctor_set(v___x_24_, 1, v___x_22_);
lean_ctor_set(v___x_24_, 2, v___x_22_);
lean_ctor_set(v___x_24_, 3, v___x_21_);
lean_ctor_set(v___x_24_, 4, v___x_21_);
lean_ctor_set(v___x_24_, 5, v___x_22_);
lean_ctor_set(v___x_24_, 6, v___x_22_);
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
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1, &l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__1);
v___x_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_107_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2, &l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2);
v___x_108_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__0));
v___x_109_ = lean_unsigned_to_nat(0u);
v___x_110_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v___x_108_);
lean_ctor_set(v___x_110_, 2, v___x_108_);
lean_ctor_set(v___x_110_, 3, v___x_108_);
lean_ctor_set(v___x_110_, 4, v___x_108_);
lean_ctor_set(v___x_110_, 5, v___x_107_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default(void){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3, &l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__3);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instInhabitedState(void){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Meta_Sym_Arith_instInhabitedState_default;
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_(lean_object* v___x_113_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2____boxed(lean_object* v___x_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_(v___x_116_);
return v_res_118_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_119_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2, &l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__2);
v___x_120_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_instInhabitedState_default___closed__0));
v___x_121_ = lean_unsigned_to_nat(8u);
v___x_122_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set(v___x_122_, 1, v___x_120_);
lean_ctor_set(v___x_122_, 2, v___x_120_);
lean_ctor_set(v___x_122_, 3, v___x_120_);
lean_ctor_set(v___x_122_, 4, v___x_120_);
lean_ctor_set(v___x_122_, 5, v___x_119_);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_123_; lean_object* v___f_124_; 
v___x_123_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_, &l_Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2__once, _init_l_Lean_Meta_Sym_Arith_initFn___closed__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_);
v___f_124_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_initFn___lam__0_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_124_, 0, v___x_123_);
return v___f_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_126_; lean_object* v___x_127_; 
v___f_126_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_, &l_Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2__once, _init_l_Lean_Meta_Sym_Arith_initFn___closed__1_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_);
v___x_127_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v___f_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2____boxed(lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_();
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg(lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_134_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v___x_133_, v_a_130_, v_a_131_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg___boxed(lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_135_, v_a_136_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getArithState(lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_140_, v_a_143_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getArithState___boxed(lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Meta_Sym_Arith_getArithState(v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_modifyArithState___redArg(lean_object* v_f_155_, lean_object* v_a_156_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_159_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_158_, v_f_155_, v_a_156_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_modifyArithState___redArg___boxed(lean_object* v_f_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_Meta_Sym_Arith_modifyArithState___redArg(v_f_160_, v_a_161_);
lean_dec(v_a_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_modifyArithState(lean_object* v_f_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_173_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_172_, v_f_164_, v_a_166_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_modifyArithState___boxed(lean_object* v_f_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Meta_Sym_Arith_modifyArithState(v_f_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold___redArg(lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_195_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_195_ == 0)
{
v___x_189_ = v___x_186_;
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_186_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v_exp_191_; lean_object* v___x_193_; 
v_exp_191_ = lean_ctor_get(v_a_187_, 0);
lean_inc(v_exp_191_);
lean_dec(v_a_187_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v_exp_191_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_exp_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
v_a_196_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_186_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_186_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold___redArg___boxed(lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Meta_Sym_Arith_getExpThreshold___redArg(v_a_204_, v_a_205_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold(lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_Meta_Sym_Arith_getExpThreshold___redArg(v_a_209_, v_a_212_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold___boxed(lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Meta_Sym_Arith_getExpThreshold(v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold___redArg___lam__0(lean_object* v_exp_224_, lean_object* v_s_225_){
_start:
{
lean_object* v_rings_226_; lean_object* v_semirings_227_; lean_object* v_ncRings_228_; lean_object* v_ncSemirings_229_; lean_object* v_typeClassify_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
v_rings_226_ = lean_ctor_get(v_s_225_, 1);
v_semirings_227_ = lean_ctor_get(v_s_225_, 2);
v_ncRings_228_ = lean_ctor_get(v_s_225_, 3);
v_ncSemirings_229_ = lean_ctor_get(v_s_225_, 4);
v_typeClassify_230_ = lean_ctor_get(v_s_225_, 5);
v_isSharedCheck_237_ = !lean_is_exclusive(v_s_225_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; 
v_unused_238_ = lean_ctor_get(v_s_225_, 0);
lean_dec(v_unused_238_);
v___x_232_ = v_s_225_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_typeClassify_230_);
lean_inc(v_ncSemirings_229_);
lean_inc(v_ncRings_228_);
lean_inc(v_semirings_227_);
lean_inc(v_rings_226_);
lean_dec(v_s_225_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v_exp_224_);
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_exp_224_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_rings_226_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_semirings_227_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v_ncRings_228_);
lean_ctor_set(v_reuseFailAlloc_236_, 4, v_ncSemirings_229_);
lean_ctor_set(v_reuseFailAlloc_236_, 5, v_typeClassify_230_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(lean_object* v_exp_239_, lean_object* v_a_240_){
_start:
{
lean_object* v___f_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___f_242_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_setExpThreshold___redArg___lam__0), 2, 1);
lean_closure_set(v___f_242_, 0, v_exp_239_);
v___x_243_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_244_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_243_, v___f_242_, v_a_240_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold___redArg___boxed(lean_object* v_exp_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_245_, v_a_246_);
lean_dec(v_a_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold(lean_object* v_exp_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_249_, v_a_251_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_setExpThreshold___boxed(lean_object* v_exp_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Meta_Sym_Arith_setExpThreshold(v_exp_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_withExpThreshold___redArg(lean_object* v_exp_267_, lean_object* v_k_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_270_, v_a_273_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_278_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref(v___x_276_);
v___x_278_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_267_, v_a_270_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_exp_279_; lean_object* v_r_280_; 
lean_dec_ref(v___x_278_);
v_exp_279_ = lean_ctor_get(v_a_277_, 0);
lean_inc(v_exp_279_);
lean_dec(v_a_277_);
lean_inc(v_a_274_);
lean_inc_ref(v_a_273_);
lean_inc(v_a_272_);
lean_inc_ref(v_a_271_);
lean_inc(v_a_270_);
lean_inc_ref(v_a_269_);
v_r_280_ = lean_apply_7(v_k_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, lean_box(0));
if (lean_obj_tag(v_r_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_282_; 
v_a_281_ = lean_ctor_get(v_r_280_, 0);
lean_inc(v_a_281_);
lean_dec_ref(v_r_280_);
v___x_282_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_279_, v_a_270_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; 
v_unused_290_ = lean_ctor_get(v___x_282_, 0);
lean_dec(v_unused_290_);
v___x_284_ = v___x_282_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_dec(v___x_282_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v_a_281_);
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_281_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec(v_a_281_);
v_a_291_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_282_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_282_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_300_; 
v_a_299_ = lean_ctor_get(v_r_280_, 0);
lean_inc(v_a_299_);
lean_dec_ref(v_r_280_);
v___x_300_ = l_Lean_Meta_Sym_Arith_setExpThreshold___redArg(v_exp_279_, v_a_270_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; 
v_unused_308_ = lean_ctor_get(v___x_300_, 0);
lean_dec(v_unused_308_);
v___x_302_ = v___x_300_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_dec(v___x_300_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set_tag(v___x_302_, 1);
lean_ctor_set(v___x_302_, 0, v_a_299_);
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_299_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_dec(v_a_299_);
v_a_309_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_300_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_300_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec(v_a_277_);
lean_dec_ref(v_k_268_);
v_a_317_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_278_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_278_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec_ref(v_k_268_);
lean_dec(v_exp_267_);
v_a_325_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_276_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_276_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_withExpThreshold___redArg___boxed(lean_object* v_exp_333_, lean_object* v_k_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Meta_Sym_Arith_withExpThreshold___redArg(v_exp_333_, v_k_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_withExpThreshold(lean_object* v_00_u03b1_343_, lean_object* v_exp_344_, lean_object* v_k_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_Meta_Sym_Arith_withExpThreshold___redArg(v_exp_344_, v_k_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_withExpThreshold___boxed(lean_object* v_00_u03b1_354_, lean_object* v_exp_355_, lean_object* v_k_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Meta_Sym_Arith_withExpThreshold(v_00_u03b1_354_, v_exp_355_, v_k_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
return v_res_364_;
}
}
lean_object* runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
l_Lean_Meta_Sym_Arith_instInhabitedState_default = _init_l_Lean_Meta_Sym_Arith_instInhabitedState_default();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedState_default);
l_Lean_Meta_Sym_Arith_instInhabitedState = _init_l_Lean_Meta_Sym_Arith_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instInhabitedState);
res = l_Lean_Meta_Sym_Arith_initFn_00___x40_Lean_Meta_Sym_Arith_Types_1023037793____hygCtx___hyg_2_();
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
